/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

use bytes::Bytes;
use encoding::{
    graph::{
        thing::{
            edge::{ThingEdgeHas, ThingEdgeRelationIndex, ThingEdgeRolePlayer},
            vertex_object::ObjectVertex,
        },
        type_::vertex::build_vertex_entity_type,
        Typed,
    },
    layout::prefix::Prefix,
    AsBytes, Keyable, Prefixed,
};
use iterator::Collector;
use storage::{
    key_value::StorageKeyReference,
    snapshot::{ReadableSnapshot, WriteSnapshot},
};

use crate::{
    concept_iterator,
    error::{ConceptReadError, ConceptWriteError},
    thing::{
        attribute::Attribute,
        object::{HasAttributeIterator, Object},
        relation::{IndexedPlayersIterator, RelationRoleIterator},
        thing_manager::ThingManager,
        value::Value,
        ObjectAPI, ThingAPI,
    },
    type_::{
        attribute_type::AttributeType, entity_type::EntityType, owns::Owns, type_manager::TypeManager, Ordering,
        OwnerAPI,
    },
    ByteReference, ConceptAPI, ConceptStatus, 
};

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Entity<'a> {
    vertex: ObjectVertex<'a>,
}

impl<'a> Entity<'a> {
    pub fn new(vertex: ObjectVertex<'a>) -> Self {
        debug_assert_eq!(vertex.prefix(), Prefix::VertexEntity);
        Entity { vertex }
    }

    pub fn type_(&self) -> EntityType<'static> {
        EntityType::new(build_vertex_entity_type(self.vertex.type_id_()))
    }

    pub fn as_reference<'this>(&'this self) -> Entity<'this> {
        Entity { vertex: self.vertex.as_reference() }
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
        attribute: Attribute<'_>,
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

    pub fn set_has_ordered<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        attribute_type: AttributeType<'static>,
        attributes: Vec<Attribute<'_>>,
    ) -> Result<(), ConceptWriteError> {
        let owns = self
            .get_type_owns(thing_manager.type_manager(), attribute_type.clone())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        let ordering = owns
            .get_ordering(thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        match ordering {
            Ordering::Unordered => {
                todo!("throw good error")
            }
            Ordering::Ordered => {
                // 1. get owned list
                let attributes = thing_manager
                    .get_has_type_ordered(self.as_reference(), attribute_type.clone())
                    .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;

                // 2. Delete existing but no-longer necessary has, and add new ones, with the correct counts (!)
                todo!()
                //
                // // 3. Overwrite owned list
                // thing_manager.set_has_ordered(self.as_reference(), attribute_type, attributes);
                // Ok(())
            }
        }
    }

    pub fn delete_has_ordered<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        let owns = self
            .get_type_owns(thing_manager.type_manager(), attribute_type)
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        let ordering = owns
            .get_ordering(thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        match ordering {
            Ordering::Unordered => {
                todo!("throw good error")
            }
            Ordering::Ordered => {
                // TODO: 1. get owned list 2. Delete each ownership has 3. delete owned list
                todo!()
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
        thing_manager.get_indexed_players(Object::Entity(self.as_reference()))
    }

    pub(crate) fn into_owned(self) -> Entity<'static> {
        Entity { vertex: self.vertex.into_owned() }
    }
}

impl<'a> ConceptAPI<'a> for Entity<'a> {}

impl<'a> ThingAPI<'a> for Entity<'a> {
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
        todo!()
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
            relation.delete_player_many(thing_manager, role, Object::Entity(self.as_reference()), count)?;
            playing = relation_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        }

        thing_manager.delete_entity(self);
        Ok(())
    }
}

impl<'a> ObjectAPI<'a> for Entity<'a> {
    fn vertex<'this>(&'this self) -> ObjectVertex<'this> {
        self.vertex.as_reference()
    }

    fn into_vertex(self) -> ObjectVertex<'a> {
        self.vertex
    }
}

fn storage_key_to_entity(storage_key_ref: StorageKeyReference<'_>) -> Entity<'_> {
    Entity::new(ObjectVertex::new(Bytes::Reference(storage_key_ref.byte_ref())))
}
concept_iterator!(EntityIterator, Entity, storage_key_to_entity);
