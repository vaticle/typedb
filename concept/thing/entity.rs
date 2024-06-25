/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

use encoding::{
    graph::{thing::vertex_object::ObjectVertex, type_::vertex::PrefixedTypeVertexEncoding, Typed},
    layout::prefix::Prefix,
    AsBytes, Keyable, Prefixed,
};
use iterator::Collector;
use lending_iterator::LendingIterator;
use resource::constants::snapshot::BUFFER_KEY_INLINE;
use storage::{
    key_value::StorageKey,
    snapshot::{ReadableSnapshot, WritableSnapshot},
};

use crate::{
    concept_iterator,
    error::{ConceptReadError, ConceptWriteError},
    thing::{
        object::{Object, ObjectAPI},
        relation::{IndexedPlayersIterator, RelationRoleIterator},
        thing_manager::ThingManager,
        ThingAPI,
    },
    type_::{entity_type::EntityType, ObjectTypeAPI, Ordering, OwnerAPI},
    ByteReference, ConceptAPI, ConceptStatus,
};
#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Entity<'a> {
    vertex: ObjectVertex<'a>,
}

impl<'a> Entity<'a> {
    pub fn new(vertex: ObjectVertex<'a>) -> Self {
        debug_assert_eq!(vertex.prefix(), Prefix::VertexEntity);
        Entity { vertex }
    }

    pub fn type_(&self) -> EntityType<'static> {
        EntityType::build_from_type_id(self.vertex.type_id_())
    }

    pub fn as_reference(&self) -> Entity<'_> {
        Entity { vertex: self.vertex.as_reference() }
    }

    pub fn iid(&self) -> ByteReference<'_> {
        self.vertex.bytes()
    }

    pub fn get_relations<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &'m Snapshot,
        thing_manager: &'m ThingManager<Snapshot>,
    ) -> RelationRoleIterator {
        thing_manager.get_relations_roles(snapshot, self.as_reference())
    }

    pub fn get_indexed_players<'m, Snapshot: ReadableSnapshot>(
        &'m self,
        snapshot: &'m Snapshot,
        thing_manager: &'m ThingManager<Snapshot>,
    ) -> IndexedPlayersIterator {
        thing_manager.get_indexed_players(snapshot, Object::Entity(self.as_reference()))
    }

    pub fn into_owned(self) -> Entity<'static> {
        Entity { vertex: self.vertex.into_owned() }
    }
}

impl<'a> ConceptAPI<'a> for Entity<'a> {}

impl<'a> ThingAPI<'a> for Entity<'a> {
    fn set_modified<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        thing_manager: &ThingManager<Snapshot>,
    ) {
        if matches!(self.get_status(snapshot, thing_manager), ConceptStatus::Persisted) {
            thing_manager.lock_existing(snapshot, self.as_reference());
        }
    }

    fn get_status<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        thing_manager: &ThingManager<Snapshot>,
    ) -> ConceptStatus {
        thing_manager.get_status(snapshot, self.vertex().as_storage_key())
    }

    fn errors<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &Snapshot,
        thing_manager: &ThingManager<Snapshot>,
    ) -> Result<Vec<ConceptWriteError>, ConceptReadError> {
        todo!()
    }

    fn delete<Snapshot: WritableSnapshot>(
        self,
        snapshot: &mut Snapshot,
        thing_manager: &ThingManager<Snapshot>,
    ) -> Result<(), ConceptWriteError> {
        let has = self
            .get_has_unordered(snapshot, thing_manager)
            .map_static(|res| res.map(|(k, _)| k.into_owned()))
            .try_collect::<Vec<_>, _>()
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        let mut has_attr_type_deleted = HashSet::new();
        for attr in has {
            has_attr_type_deleted.add(attr.type_());
            thing_manager.unset_has(snapshot, &self, attr);
        }

        for owns in self
            .type_()
            .get_owns_declared(snapshot, thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
            .iter()
        {
            let ordering = owns
                .get_ordering(snapshot, thing_manager.type_manager())
                .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
            if matches!(ordering, Ordering::Ordered) {
                thing_manager.unset_has_ordered(snapshot, &self, owns.attribute());
            }
        }

        let relations_roles = self
            .get_relations(snapshot, thing_manager)
            .map_static(|res| res.map(|(relation, role, _count)| (relation.into_owned(), role.into_owned())))
            .try_collect::<Vec<_>, _>()
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        for (relation, role) in relations_roles {
            thing_manager.unset_role_player(snapshot, relation, self.as_reference(), role)?;
        }

        thing_manager.delete_entity(snapshot, self);
        Ok(())
    }
}

impl<'a> ObjectAPI<'a> for Entity<'a> {
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
        Object::Entity(self.into_owned())
    }
}

fn storage_key_to_entity(storage_key: StorageKey<'_, BUFFER_KEY_INLINE>) -> Entity<'_> {
    Entity::new(ObjectVertex::new(storage_key.into_bytes()))
}

concept_iterator!(EntityIterator, Entity, storage_key_to_entity);
