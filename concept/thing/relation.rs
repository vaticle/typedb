/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use bytes::Bytes;
use encoding::{
    graph::{
        thing::{
            edge::{ThingEdgeHas, ThingEdgeRelationIndex, ThingEdgeRolePlayer},
            vertex_object::ObjectVertex,
        },
        type_::vertex::{build_vertex_relation_type, build_vertex_role_type},
        Typed,
    },
    layout::prefix::Prefix,
    value::decode_value_u64,
    AsBytes, Keyable, Prefixed,
};
use iterator::Collector;
use storage::{
    key_value::StorageKeyReference,
    snapshot::{ReadableSnapshot, WriteSnapshot},
};

use crate::{
    concept_iterator, edge_iterator,
    error::{ConceptReadError, ConceptWriteError},
    thing::{
        attribute::Attribute,
        object::{HasAttributeIterator, Object},
        thing_manager::ThingManager,
        value::Value,
        ObjectAPI, ThingAPI,
    },
    type_::{
        annotation::AnnotationDistinct,
        attribute_type::AttributeType,
        owns::Owns,
        relation_type::RelationType,
        role_type::{RoleType, RoleTypeAnnotation},
        type_manager::TypeManager,
        Ordering, OwnerAPI,
    },
    ByteReference, ConceptAPI, ConceptStatus,
};

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Relation<'a> {
    vertex: ObjectVertex<'a>,
}

impl<'a> Relation<'a> {
    pub fn new(vertex: ObjectVertex<'a>) -> Self {
        debug_assert_eq!(vertex.prefix(), Prefix::VertexRelation);
        Relation { vertex }
    }

    pub(crate) fn as_reference(&self) -> Relation<'_> {
        Relation { vertex: self.vertex.as_reference() }
    }

    pub fn type_(&self) -> RelationType<'static> {
        RelationType::new(build_vertex_relation_type(self.vertex.type_id_()))
    }

    pub fn iid(&self) -> ByteReference<'_> {
        self.vertex.bytes()
    }

    pub fn has_attribute(
        &self,
        thing_manager: &ThingManager<impl ReadableSnapshot>,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<bool, ConceptReadError> {
        thing_manager.has_attribute(self.as_reference(), attribute_type, value)
    }

    pub fn get_has<'m>(
        &self,
        thing_manager: &'m ThingManager<impl ReadableSnapshot>,
    ) -> HasAttributeIterator<'m, { ThingEdgeHas::LENGTH_PREFIX_FROM_OBJECT }> {
        thing_manager.get_has_unordered(self.as_reference())
    }

    pub fn get_has_type<'m>(
        &self,
        thing_manager: &'m ThingManager<impl ReadableSnapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<HasAttributeIterator<'m, { ThingEdgeHas::LENGTH_PREFIX_FROM_OBJECT_TO_TYPE }>, ConceptReadError> {
        thing_manager.get_has_type_unordered(self.as_reference(), attribute_type)
    }

    pub fn set_has_unordered<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        attribute: Attribute<'_>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: validate schema
        let owns = self
            .get_type_owns(thing_manager.type_manager(), attribute.type_())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        let ordering = owns
            .get_ordering(thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        match ordering {
            Ordering::Unordered => {
                thing_manager.set_has(self.as_reference(), attribute.as_reference());
                Ok(())
            }
            Ordering::Ordered => {
                todo!("throw a good error")
            }
        }
    }

    pub fn delete_has_unordered<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        attribute: Attribute<'static>,
    ) -> Result<(), ConceptWriteError> {
        let owns = self
            .get_type_owns(thing_manager.type_manager(), attribute.type_())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        let ordering = owns
            .get_ordering(thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        match ordering {
            Ordering::Unordered => {
                thing_manager.delete_has(self.as_reference(), attribute);
                Ok(())
            }
            Ordering::Ordered => {
                todo!("throw good error")
            }
        }
    }

    fn get_type_owns<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Owns<'m>, ConceptReadError> {
        let owns = self.type_().get_owns_attribute(type_manager, attribute_type)?;
        match owns {
            None => {
                todo!("throw useful schema error")
            }
            Some(owns) => Ok(owns),
        }
    }
    //
    //
    // pub fn delete_has_single(
    //     &self, thing_manager: &ThingManager<WriteSnapshot<D>>, attribute: Attribute<'_>,
    // ) -> Result<(), ConceptWriteError> {
    //     self.delete_has_many(thing_manager, attribute, 1)
    // }
    //
    // pub fn delete_has_many(
    //     &self, thing_manager: &ThingManager<WriteSnapshot<D>>, attribute: Attribute<'_>, count: u64,
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
        thing_manager: &'m ThingManager<impl ReadableSnapshot>,
    ) -> RelationRoleIterator<'m, { ThingEdgeRolePlayer::LENGTH_PREFIX_FROM }> {
        thing_manager.get_relations_roles(self.as_reference())
    }

    pub fn get_indexed_players<'m>(
        &self,
        thing_manager: &'m ThingManager<impl ReadableSnapshot>,
    ) -> IndexedPlayersIterator<'m, { ThingEdgeRelationIndex::LENGTH_PREFIX_FROM }> {
        thing_manager.get_indexed_players(Object::Relation(self.as_reference()))
    }

    pub fn has_players<'m>(&self, thing_manager: &'m ThingManager<impl ReadableSnapshot>) -> bool {
        match self.get_status(thing_manager) {
            ConceptStatus::Inserted => thing_manager.has_role_players(self.as_reference(), true),
            ConceptStatus::Put | ConceptStatus::Persisted => thing_manager.has_role_players(self.as_reference(), false),
            ConceptStatus::Deleted => unreachable!("Cannot operate on a deleted concept."),
        }
    }

    pub fn get_players<'m>(
        &self,
        thing_manager: &'m ThingManager<impl ReadableSnapshot>,
    ) -> RolePlayerIterator<'m, { ThingEdgeHas::LENGTH_PREFIX_FROM_OBJECT }> {
        thing_manager.get_role_players(self.as_reference())
    }

    fn get_player_counts(
        &self,
        thing_manager: &ThingManager<impl ReadableSnapshot>,
    ) -> Result<HashMap<RoleType<'static>, u64>, ConceptReadError> {
        let mut map = HashMap::new();
        let mut rp_iter = self.get_players(thing_manager);
        let mut rp = rp_iter.next().transpose()?;
        while let Some((role_player, count)) = rp {
            let mut value = map.entry(role_player.role_type.clone()).or_insert(0);
            *value += count;
            rp = rp_iter.next().transpose()?;
        }
        Ok(map)
    }

    ///
    /// Semantics:
    ///   When duplicates are not allowed, we use set semantics and put the edge idempotently, which cannot fail other txn's
    ///   When duplicates are allowed, we increment the count of the role player edge and fail other txn's doing the same
    ///
    /// TODO: to optimise the common case of creating a full relation, we could introduce a RelationBuilder, which can accumulate role players,
    ///   Then write all players + indexes in one go
    ///
    pub fn add_player<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
        player: Object<'_>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: validate schema
        let role_annotations = role_type.get_annotations(thing_manager.type_manager()).unwrap();
        let distinct = role_annotations.contains(&RoleTypeAnnotation::Distinct(AnnotationDistinct::new()));
        if distinct {
            self.add_player_distinct(thing_manager, role_type, player)
        } else {
            self.add_player_increment(thing_manager, role_type, player)
        }
    }

    fn add_player_distinct<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
        player: Object<'_>,
    ) -> Result<(), ConceptWriteError> {
        if thing_manager
            .type_manager()
            .relation_index_available(self.type_())
            .map_err(|e| ConceptWriteError::ConceptRead { source: e })?
        {
            let compound_update_guard = thing_manager.relation_compound_update_mutex().lock().unwrap();
            thing_manager.set_role_player(self.as_reference(), player.as_reference(), role_type.clone());
            thing_manager.relation_index_player_regenerate(
                self.as_reference(),
                player.as_reference(),
                role_type,
                1,
                &compound_update_guard,
            );
        } else {
            thing_manager.set_role_player(self.as_reference(), player.as_reference(), role_type.clone());
        }
        Ok(())
    }

    fn add_player_increment<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
        player: Object<'_>,
    ) -> Result<(), ConceptWriteError> {
        let compound_update_guard = thing_manager.relation_compound_update_mutex().lock().unwrap();
        let player_count = thing_manager.increment_role_player(
            self.as_reference(),
            player.as_reference(),
            role_type.clone(),
            &compound_update_guard,
        );
        if thing_manager
            .type_manager()
            .relation_index_available(self.type_())
            .map_err(|e| ConceptWriteError::ConceptRead { source: e })?
        {
            thing_manager.relation_index_player_regenerate(
                self.as_reference(),
                player.as_reference(),
                role_type,
                player_count,
                &compound_update_guard,
            );
        }
        Ok(())
    }

    pub fn delete_player_single<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
        player: Object<'_>,
    ) -> Result<(), ConceptWriteError> {
        self.delete_player_many(thing_manager, role_type, player, 1)
    }

    pub fn delete_player_many<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
        player: Object<'_>,
        delete_count: u64,
    ) -> Result<(), ConceptWriteError> {
        let role_annotations = role_type.get_annotations(thing_manager.type_manager()).unwrap();
        let distinct = role_annotations.contains(&RoleTypeAnnotation::Distinct(AnnotationDistinct::new()));
        if distinct {
            debug_assert_eq!(delete_count, 1);
            self.delete_player_distinct(thing_manager, role_type, player)
        } else {
            self.delete_player_decrement(thing_manager, role_type, player, delete_count)
        }
    }

    fn delete_player_distinct<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
        player: Object<'_>,
    ) -> Result<(), ConceptWriteError> {
        if thing_manager
            .type_manager()
            .relation_index_available(self.type_())
            .map_err(|e| ConceptWriteError::ConceptRead { source: e })?
        {
            let compound_update_guard = thing_manager.relation_compound_update_mutex().lock().unwrap();
            thing_manager.delete_role_player(self.as_reference(), player.as_reference(), role_type.clone());
            thing_manager.relation_index_player_deleted(
                self.as_reference(),
                player.as_reference(),
                role_type,
                &compound_update_guard,
            );
        } else {
            thing_manager.delete_role_player(self.as_reference(), player.as_reference(), role_type.clone());
        }
        Ok(())
    }

    fn delete_player_decrement<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
        player: Object<'_>,
        decrement_count: u64,
    ) -> Result<(), ConceptWriteError> {
        let compound_update_guard = thing_manager.relation_compound_update_mutex().lock().unwrap();
        let remaining_player_count = thing_manager.decrement_role_player(
            self.as_reference(),
            player.as_reference(),
            role_type.clone(),
            decrement_count,
            &compound_update_guard,
        );
        if thing_manager
            .type_manager()
            .relation_index_available(self.type_())
            .map_err(|e| ConceptWriteError::ConceptRead { source: e })?
        {
            debug_assert_eq!(remaining_player_count, 0);
            thing_manager.relation_index_player_regenerate(
                self.as_reference(),
                player.as_reference(),
                role_type,
                remaining_player_count,
                &compound_update_guard,
            );
        }
        Ok(())
    }

    pub(crate) fn into_owned(self) -> Relation<'static> {
        Relation { vertex: self.vertex.into_owned() }
    }
}

impl<'a> ConceptAPI<'a> for Relation<'a> {}

impl<'a> ThingAPI<'a> for Relation<'a> {
    fn set_modified<D>(&self, thing_manager: &ThingManager<WriteSnapshot<D>>) {
        if matches!(self.get_status(thing_manager), ConceptStatus::Persisted) {
            thing_manager.lock_existing(self.as_reference());
        }
    }

    fn get_status<'m>(&self, thing_manager: &'m ThingManager<impl ReadableSnapshot>) -> ConceptStatus {
        thing_manager.get_status(self.vertex().as_storage_key())
    }

    fn errors<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
    ) -> Result<Vec<ConceptWriteError>, ConceptReadError> {
        let mut errors = Vec::new();

        // validate cardinality
        let type_ = self.type_();
        let relation_relates = type_.get_relates(thing_manager.type_manager())?;
        let role_player_count = self.get_player_counts(thing_manager)?;
        for relates in relation_relates.iter() {
            let role_type = relates.role();
            let cardinality = role_type.get_cardinality(thing_manager.type_manager())?;
            let player_count = role_player_count.get(&role_type).map_or(0, |c| *c);
            if !cardinality.is_valid(player_count) {
                errors.push(ConceptWriteError::RelationRoleCardinality {
                    relation: self.clone().into_owned(),
                    role_type: role_type.clone(),
                    cardinality: cardinality.clone(),
                    actual_cardinality: player_count,
                });
            }
        }
        Ok(errors)
    }

    fn delete<D>(self, thing_manager: &ThingManager<WriteSnapshot<D>>) -> Result<(), ConceptWriteError> {
        let mut has_iter = self.get_has(thing_manager);
        let mut has = has_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        let mut has_attr_type_deleted = HashSet::new();
        while let Some((attr, count)) = has {
            has_attr_type_deleted.add(attr.type_());
            thing_manager.delete_has(self.as_reference(), attr);
            has = has_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        }

        for owns in self
            .type_()
            .get_owns(thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
            .iter()
        {
            let ordering = owns
                .get_ordering(thing_manager.type_manager())
                .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
            if matches!(ordering, Ordering::Ordered) {
                thing_manager.delete_has_ordered(self.as_reference(), owns.attribute());
            }
        }

        let mut relation_iter = self.get_relations(thing_manager);
        let mut playing =
            relation_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        while let Some((relation, role, count)) = playing {
            relation.delete_player_many(thing_manager, role, Object::Relation(self.as_reference()), count)?;
            playing = relation_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        }

        let mut player_iter = self.get_players(thing_manager);
        let mut role_player = player_iter
            .next()
            .transpose()
            .map_err(|err| ConceptWriteError::ConceptRead { source: ConceptReadError::from(err) })?;
        while let Some((rp, count)) = role_player {
            self.delete_player_many(thing_manager, rp.role_type(), rp.player(), count)?;
            role_player =
                player_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        }

        thing_manager.delete_relation(self);
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
}

// TODO: can we inline this into the macro invocation?
fn storage_key_ref_to_entity(storage_key_ref: StorageKeyReference<'_>) -> Relation<'_> {
    Relation::new(ObjectVertex::new(Bytes::Reference(storage_key_ref.byte_ref())))
}
concept_iterator!(RelationIterator, Relation, storage_key_ref_to_entity);

#[derive(Debug, Eq, PartialEq)]
pub struct RolePlayer<'a> {
    player: Object<'a>,
    role_type: RoleType<'static>,
}

impl<'a> RolePlayer<'a> {
    pub(crate) fn player(&self) -> Object<'_> {
        self.player.as_reference()
    }

    pub(crate) fn role_type(&self) -> RoleType<'static> {
        self.role_type.clone()
    }
}

fn storage_key_to_role_player<'a>(
    storage_key_ref: StorageKeyReference<'a>,
    value: ByteReference<'a>,
) -> (RolePlayer<'a>, u64) {
    let edge = ThingEdgeRolePlayer::new(Bytes::Reference(storage_key_ref.byte_ref()));
    let role_type = build_vertex_role_type(edge.role_id());
    (RolePlayer { player: Object::new(edge.into_to()), role_type: RoleType::new(role_type) }, decode_value_u64(value))
}

edge_iterator!(
    RolePlayerIterator;
    (RolePlayer<'_>, u64);
    storage_key_to_role_player
);

fn storage_key_to_relation_role<'a>(
    storage_key_ref: StorageKeyReference<'a>,
    value: ByteReference<'a>,
) -> (Relation<'a>, RoleType<'static>, u64) {
    let edge = ThingEdgeRolePlayer::new(Bytes::Reference(storage_key_ref.byte_ref()));
    let role_type = build_vertex_role_type(edge.role_id());
    (Relation::new(edge.into_to()), RoleType::new(role_type), decode_value_u64(value))
}

edge_iterator!(
    RelationRoleIterator;
    (Relation<'_>, RoleType<'static>, u64);
    storage_key_to_relation_role
);

fn storage_key_to_indexed_players<'a>(
    storage_key_ref: StorageKeyReference<'a>,
    value: ByteReference<'a>,
) -> (RolePlayer<'a>, RolePlayer<'a>, Relation<'a>, u64) {
    let from_role_player = RolePlayer {
        player: Object::new(ThingEdgeRelationIndex::read_from(storage_key_ref.byte_ref())),
        role_type: RoleType::new(build_vertex_role_type(ThingEdgeRelationIndex::read_from_role_id(
            storage_key_ref.byte_ref(),
        ))),
    };
    let to_role_player = RolePlayer {
        player: Object::new(ThingEdgeRelationIndex::read_to(storage_key_ref.byte_ref())),
        role_type: RoleType::new(build_vertex_role_type(ThingEdgeRelationIndex::read_to_role_id(
            storage_key_ref.byte_ref(),
        ))),
    };
    (
        from_role_player,
        to_role_player,
        Relation::new(ThingEdgeRelationIndex::read_relation(storage_key_ref.byte_ref())),
        decode_value_u64(value),
    )
}

edge_iterator!(
    IndexedPlayersIterator;
    (RolePlayer<'_>, RolePlayer<'_>, Relation<'_>, u64);
    storage_key_to_indexed_players
);
