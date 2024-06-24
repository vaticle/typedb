/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashMap;

use bytes::Bytes;
use encoding::{
    graph::{
        thing::{
            edge::{ThingEdgeRelationIndex, ThingEdgeRolePlayer},
            vertex_object::ObjectVertex,
        },
        type_::vertex::PrefixedTypeVertexEncoding,
        Typed,
    },
    layout::prefix::Prefix,
    value::decode_value_u64,
    AsBytes, Keyable, Prefixed,
};
use lending_iterator::{higher_order::Hkt, LendingIterator};
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use storage::{
    key_value::StorageKey,
    snapshot::{ReadableSnapshot, WritableSnapshot},
};

use crate::{
    concept_iterator, edge_iterator,
    error::{ConceptReadError, ConceptWriteError},
    thing::{
        object::{Object, ObjectAPI},
        thing_manager::ThingManager,
        ThingAPI,
    },
    type_::{
        annotation::AnnotationDistinct,
        relation_type::RelationType,
        role_type::{RoleType, RoleTypeAnnotation},
        ObjectTypeAPI, Ordering,
    },
    ByteReference, ConceptAPI, ConceptStatus,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Relation<'a> {
    vertex: ObjectVertex<'a>,
}

impl<'a> Relation<'a> {
    pub fn new(vertex: ObjectVertex<'a>) -> Self {
        debug_assert_eq!(
            vertex.prefix(),
            Prefix::VertexRelation,
            "non-relation prefix when constructing from a vertex"
        );
        Relation { vertex }
    }

    pub(crate) fn as_reference(&self) -> Relation<'_> {
        Relation { vertex: self.vertex.as_reference() }
    }

    pub fn type_(&self) -> RelationType<'static> {
        RelationType::build_from_type_id(self.vertex.type_id_())
    }

    pub fn iid(&self) -> ByteReference<'_> {
        self.vertex.bytes()
    }

    // pub fn delete_has_single(
    //     &self, thing_manager: &ThingManager, attribute: Attribute<'_>,
    // ) -> Result<(), ConceptWriteError> {
    //     self.delete_has_many(thing_manager, attribute, 1)
    // }
    //
    // pub fn delete_has_many(
    //     &self, thing_manager: &ThingManager, attribute: Attribute<'_>, count: u64,
    // ) -> Result<(), ConceptWriteError> {
    //     let owns = self.type_().get_owns_attribute(
    //         thing_manager.type_manager(),
    //         attribute.type_(),
    //     ).map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
    //     match owns {
    //         None => {
    //             todo!("throw useful schema violation error")
    //         }
    //         Some(owns) => {
    //             if owns.is_distinct(thing_manager.type_manager())
    //                 .map_err(|err| ConceptWriteError::ConceptRead { source: err })? {
    //                 debug_assert_eq!(count, 1);
    //                 thing_manager.delete_has(self.as_reference(), attribute);
    //             } else {
    //                 thing_manager.decrement_has(self.as_reference(), attribute, count);
    //             }
    //         }
    //     }
    //     Ok(())
    // }

    pub fn get_relations<'m>(
        &self,
        snapshot: &'m impl ReadableSnapshot,
        thing_manager: &'m ThingManager,
    ) -> RelationRoleIterator {
        thing_manager.get_relations_roles(snapshot, self.as_reference())
    }

    pub fn get_indexed_players<'m>(
        &self,
        snapshot: &'m impl ReadableSnapshot,
        thing_manager: &'m ThingManager,
    ) -> IndexedPlayersIterator {
        thing_manager.get_indexed_players(snapshot, Object::Relation(self.as_reference()))
    }

    pub fn has_players(&self, snapshot: &impl ReadableSnapshot, thing_manager: &ThingManager) -> bool {
        match self.get_status(snapshot, thing_manager) {
            ConceptStatus::Inserted => thing_manager.has_role_players(snapshot, self.as_reference(), true),
            ConceptStatus::Persisted => thing_manager.has_role_players(snapshot, self.as_reference(), false),
            ConceptStatus::Put => unreachable!("Encountered a `put` relation"),
            ConceptStatus::Deleted => unreachable!("Cannot operate on a deleted concept."),
        }
    }

    pub fn get_players(
        &self,
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
    ) -> impl for<'x> LendingIterator<Item<'x> = Result<(RolePlayer<'x>, u64), ConceptReadError>> {
        thing_manager.get_role_players(snapshot, self.as_reference())
    }

    pub fn get_players_ordered(
        &self,
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
        role_type: RoleType<'static>,
    ) -> Result<Vec<Object<'_>>, ConceptReadError> {
        thing_manager.get_role_players_ordered(snapshot, self.as_reference(), role_type)
    }

    pub fn get_players_role_type(
        &self,
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
        role_type: RoleType<'static>,
    ) -> impl for<'x> LendingIterator<Item<'x> = Result<Object<'x>, ConceptReadError>> {
        self.get_players(snapshot, thing_manager).filter_map::<Result<Object<'_>, _>, _>(move |res| match res {
            Ok((roleplayer, _count)) => (roleplayer.role_type() == role_type).then_some(Ok(roleplayer.player)),
            Err(error) => Some(Err(error)),
        })
    }

    fn get_player_counts(
        &self,
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
    ) -> Result<HashMap<RoleType<'static>, u64>, ConceptReadError> {
        let mut map = HashMap::new();
        let mut rp_iter = self.get_players(snapshot, thing_manager);
        let mut rp = rp_iter.next().transpose()?;
        while let Some((role_player, count)) = rp {
            let value = map.entry(role_player.role_type.clone()).or_insert(0);
            *value += count;
            rp = rp_iter.next().transpose()?;
        }
        Ok(map)
    }

    /// Semantics:
    ///   When duplicates are not allowed, we use set semantics and put the edge idempotently, which cannot fail other txn's
    ///   When duplicates are allowed, we increment the count of the role player edge and fail other txn's doing the same
    ///
    /// TODO: to optimise the common case of creating a full relation, we could introduce a RelationBuilder, which can accumulate role players,
    ///   Then write all players + indexes in one go
    pub fn add_player(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        role_type: RoleType<'static>,
        player: Object<'_>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: validate schema
        if !thing_manager
            .object_exists(snapshot, self)
            .map_err(|error| ConceptWriteError::ConceptRead { source: error })?
        {
            return Err(ConceptWriteError::AddPlayerOnDeleted { relation: self.clone().into_owned() });
        }

        let role_annotations = role_type.get_annotations(snapshot, thing_manager.type_manager()).unwrap();
        let distinct = role_annotations.contains(&RoleTypeAnnotation::Distinct(AnnotationDistinct));
        if distinct {
            thing_manager.put_role_player_unordered(
                snapshot,
                self.as_reference(),
                player.as_reference(),
                role_type.clone(),
            )
        } else {
            thing_manager.increment_role_player(snapshot, self.as_reference(), player.as_reference(), role_type.clone())
        }
    }

    pub fn set_players_ordered(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        role_type: RoleType<'static>,
        new_players: Vec<Object<'_>>,
    ) -> Result<(), ConceptWriteError> {
        if !thing_manager.object_exists(snapshot, self)? {
            return Err(ConceptWriteError::AddPlayerOnDeleted { relation: self.clone().into_owned() });
        }

        match role_type
            .get_ordering(snapshot, thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
        {
            Ordering::Unordered => todo!(),
            Ordering::Ordered => (),
        }

        let mut new_counts = HashMap::<_, u64>::new();
        for player in &new_players {
            *new_counts.entry(player).or_default() += 1;
        }

        // 1. get owned list
        let old_players = thing_manager
            .get_role_players_ordered(snapshot, self.as_reference(), role_type.clone())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;

        let mut old_counts = HashMap::<_, u64>::new();
        for player in &old_players {
            *old_counts.entry(player).or_default() += 1;
        }

        // 2. Delete existing but no-longer necessary has, and add new ones, with the correct counts (!)
        for player in old_counts.keys() {
            if !new_counts.contains_key(player) {
                thing_manager.unset_role_player(
                    snapshot,
                    self.as_reference(),
                    player.as_reference(),
                    role_type.clone(),
                )?;
            }
        }
        for (player, count) in new_counts {
            if old_counts.get(&player) != Some(&count) {
                thing_manager.set_role_player_count(
                    snapshot,
                    self.as_reference(),
                    player.as_reference(),
                    role_type.clone(),
                    count,
                )?;
            }
        }

        // 3. Overwrite owned list
        thing_manager.set_role_players_ordered(snapshot, self.as_reference(), role_type, new_players)?;
        Ok(())
    }

    pub fn remove_player_single(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        role_type: RoleType<'static>,
        player: Object<'_>,
    ) -> Result<(), ConceptWriteError> {
        self.remove_player_many(snapshot, thing_manager, role_type, player, 1)
    }

    pub fn remove_player_many(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        role_type: RoleType<'static>,
        player: Object<'_>,
        delete_count: u64,
    ) -> Result<(), ConceptWriteError> {
        let role_annotations = role_type.get_annotations(snapshot, thing_manager.type_manager()).unwrap();
        let distinct = role_annotations.contains(&RoleTypeAnnotation::Distinct(AnnotationDistinct));
        if distinct {
            debug_assert_eq!(delete_count, 1);
            thing_manager.unset_role_player(snapshot, self.as_reference(), player.as_reference(), role_type.clone())
        } else {
            thing_manager.decrement_role_player(
                snapshot,
                self.as_reference(),
                player.as_reference(),
                role_type.clone(),
                delete_count,
            )
        }
    }

    pub fn into_owned(self) -> Relation<'static> {
        Relation { vertex: self.vertex.into_owned() }
    }
}

impl<'a> ConceptAPI<'a> for Relation<'a> {}

impl<'a> ThingAPI<'a> for Relation<'a> {
    fn set_modified(&self, snapshot: &mut impl WritableSnapshot, thing_manager: &ThingManager) {
        if matches!(self.get_status(snapshot, thing_manager), ConceptStatus::Persisted) {
            thing_manager.lock_existing(snapshot, self.as_reference());
        }
    }

    fn get_status(&self, snapshot: &impl ReadableSnapshot, thing_manager: &ThingManager) -> ConceptStatus {
        thing_manager.get_status(snapshot, self.vertex().as_storage_key())
    }

    fn errors(
        &self,
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
    ) -> Result<Vec<ConceptWriteError>, ConceptReadError> {
        let mut errors = Vec::new();

        // validate cardinality
        let type_ = self.type_();
        let relation_relates = type_.get_relates(snapshot, thing_manager.type_manager())?;
        let role_player_count = self.get_player_counts(snapshot, thing_manager)?;
        for relates in relation_relates.iter() {
            let role_type = relates.role();
            let cardinality = role_type.get_cardinality(snapshot, thing_manager.type_manager())?;
            let player_count = role_player_count.get(&role_type).map_or(0, |c| *c);
            if !cardinality.is_valid(player_count) {
                errors.push(ConceptWriteError::RelationRoleCardinality {
                    relation: self.clone().into_owned(),
                    role_type: role_type.clone(),
                    cardinality,
                    actual_cardinality: player_count,
                });
            }
        }
        Ok(errors)
    }

    fn delete(
        self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
    ) -> Result<(), ConceptWriteError> {
        for attr in self
            .get_has_unordered(snapshot, thing_manager)
            .map_static(|res| res.map(|(key, _value)| key.into_owned()))
            .try_collect::<Vec<_>, _>()
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
        {
            thing_manager.unset_has(snapshot, &self, attr);
        }

        // TODO
        /*
        for attr in self
            .get_has_ordered(snapshot, thing_manager)
            .collect_cloned_vec(|(key, _value)| key.into_owned())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
        {
            // TODO huh?
            thing_manager.unset_has_ordered(snapshot, &self, attr.type_());
        }
        */

        for (relation, role) in self
            .get_relations(snapshot, thing_manager)
            .map_static(|res| res.map(|(relation, role, _count)| (relation.into_owned(), role.into_owned())))
            .try_collect::<Vec<_>, _>()
            .map_err(|error| ConceptWriteError::ConceptRead { source: error })?
        {
            thing_manager.unset_role_player(snapshot, relation, self.as_reference(), role)?;
        }

        let players = self
            .get_players(snapshot, thing_manager)
            .map_static(|item| {
                let (roleplayer, _count) = item?;
                Ok((roleplayer.role_type, roleplayer.player.into_owned()))
            })
            .try_collect::<Vec<_>, _>()
            .map_err(|error| ConceptWriteError::ConceptRead { source: error })?;
        for (role, player) in players {
            // TODO: Deleting one player at a time, each of which will delete parts of the relation index, isn't optimal
            //       Instead, we could delete the players, then delete the entire index at once, if there is one
            thing_manager.unset_role_player(snapshot, self.as_reference(), player, role)?;
        }

        debug_assert_eq!(self.get_indexed_players(snapshot, thing_manager).count(), 0);

        if self.get_status(snapshot, thing_manager) == ConceptStatus::Inserted {
            thing_manager.uninsert_relation(snapshot, self);
        } else {
            thing_manager.delete_relation(snapshot, self);
        }
        Ok(())
    }
}

impl<'a> ObjectAPI<'a> for Relation<'a> {
    fn vertex(&self) -> ObjectVertex<'_> {
        self.vertex.as_reference()
    }

    fn into_vertex(self) -> ObjectVertex<'a> {
        self.vertex
    }

    fn type_(&self) -> impl ObjectTypeAPI<'static> {
        self.type_()
    }

    fn into_owned_object(self) -> Object<'static> {
        Object::Relation(self.into_owned())
    }
}

impl Hkt for Relation<'static> {
    type HktSelf<'a> = Relation<'a>;
}

// TODO: can we inline this into the macro invocation?
fn storage_key_to_entity(storage_key: StorageKey<'_, BUFFER_KEY_INLINE>) -> Relation<'_> {
    Relation::new(ObjectVertex::new(storage_key.into_bytes()))
}
concept_iterator!(RelationIterator, Relation, storage_key_to_entity);

#[derive(Debug, Eq, PartialEq)]
pub struct RolePlayer<'a> {
    player: Object<'a>,
    role_type: RoleType<'static>,
}

impl<'a> RolePlayer<'a> {
    pub fn player(&self) -> Object<'_> {
        self.player.as_reference()
    }

    pub fn role_type(&self) -> RoleType<'static> {
        self.role_type.clone()
    }

    pub fn into_owned(self) -> RolePlayer<'static> {
        RolePlayer { player: self.player.into_owned(), role_type: self.role_type }
    }
}

fn storage_key_to_role_player<'a>(
    storage_key: StorageKey<'a, BUFFER_KEY_INLINE>,
    value: Bytes<'a, BUFFER_VALUE_INLINE>,
) -> (RolePlayer<'a>, u64) {
    let edge = ThingEdgeRolePlayer::new(storage_key.into_bytes());
    let role_type = RoleType::build_from_type_id(edge.role_id());
    (RolePlayer { player: Object::new(edge.into_to()), role_type }, decode_value_u64(value.as_reference()))
}

impl Hkt for RolePlayer<'static> {
    type HktSelf<'a> = RolePlayer<'a>;
}

edge_iterator!(
    RolePlayerIterator;
    'a -> (RolePlayer<'a>, u64);
    storage_key_to_role_player
);

fn storage_key_to_relation_role<'a>(
    storage_key: StorageKey<'a, BUFFER_KEY_INLINE>,
    value: Bytes<'a, BUFFER_VALUE_INLINE>,
) -> (Relation<'a>, RoleType<'static>, u64) {
    let edge = ThingEdgeRolePlayer::new(storage_key.into_bytes());
    let role_type = RoleType::build_from_type_id(edge.role_id());
    (Relation::new(edge.into_to()), role_type, decode_value_u64(value.as_reference()))
}

edge_iterator!(
    RelationRoleIterator;
    'a -> (Relation<'a>, RoleType<'static>, u64);
    storage_key_to_relation_role
);

fn storage_key_to_indexed_players<'a>(
    storage_key: StorageKey<'a, BUFFER_KEY_INLINE>,
    value: Bytes<'a, BUFFER_VALUE_INLINE>,
) -> (RolePlayer<'a>, RolePlayer<'a>, Relation<'a>, u64) {
    let from_role_player = RolePlayer {
        player: Object::new(ThingEdgeRelationIndex::read_from(storage_key.as_reference().byte_ref())),
        role_type: RoleType::build_from_type_id(ThingEdgeRelationIndex::read_from_role_id(
            storage_key.as_reference().byte_ref(),
        )),
    };
    let to_role_player = RolePlayer {
        player: Object::new(ThingEdgeRelationIndex::read_to(storage_key.as_reference().byte_ref())),
        role_type: RoleType::build_from_type_id(ThingEdgeRelationIndex::read_to_role_id(
            storage_key.as_reference().byte_ref(),
        )),
    };
    (
        from_role_player,
        to_role_player,
        Relation::new(ThingEdgeRelationIndex::read_relation(storage_key.as_reference().byte_ref())),
        decode_value_u64(value.as_reference()),
    )
}

edge_iterator!(
    IndexedPlayersIterator;
    'a -> (RolePlayer<'a>, RolePlayer<'a>, Relation<'a>, u64);
    storage_key_to_indexed_players
);
