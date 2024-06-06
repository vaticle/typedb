/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{collections::BTreeMap, fmt::Debug};

use bytes::Bytes;
use encoding::{
    graph::thing::{edge::ThingEdgeHas, vertex_object::ObjectVertex},
    layout::prefix::Prefix,
    value::{decode_value_u64, value::Value},
    Prefixed,
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
    thing::{attribute::Attribute, entity::Entity, relation::Relation, thing_manager::ThingManager, ThingAPI},
    type_::{
        attribute_type::AttributeType, object_type::ObjectType, owns::Owns, role_type::RoleType,
        type_manager::TypeManager, ObjectTypeAPI, Ordering, OwnerAPI,
    },
    ConceptStatus,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Object<'a> {
    Entity(Entity<'a>),
    Relation(Relation<'a>),
}

impl<'a> Object<'a> {
    pub(crate) fn new(object_vertex: ObjectVertex<'a>) -> Self {
        match object_vertex.prefix() {
            Prefix::VertexEntity => Object::Entity(Entity::new(object_vertex)),
            Prefix::VertexRelation => Object::Relation(Relation::new(object_vertex)),
            _ => unreachable!("Object creation requires either Entity or Relation vertex."),
        }
    }

    pub(crate) fn as_reference(&self) -> Object<'_> {
        match self {
            Object::Entity(entity) => Object::Entity(entity.as_reference()),
            Object::Relation(relation) => Object::Relation(relation.as_reference()),
        }
    }

    pub fn unwrap_entity(self) -> Entity<'a> {
        match self {
            Self::Entity(entity) => entity,
            Self::Relation(relation) => panic!("called `Object::unwrap_entity()` on a `Relation` value: {relation:?}"),
        }
    }

    pub fn unwrap_relation(self) -> Relation<'a> {
        match self {
            Self::Relation(relation) => relation,
            Self::Entity(entity) => panic!("called `Object::unwrap_relation()` on an `Entity` value: {entity:?}"),
        }
    }

    pub fn type_(&self) -> ObjectType<'static> {
        match self {
            Object::Entity(entity) => ObjectType::Entity(entity.type_()),
            Object::Relation(relation) => ObjectType::Relation(relation.type_()),
        }
    }

    pub fn vertex(&self) -> ObjectVertex<'_> {
        match self {
            Object::Entity(entity) => entity.vertex(),
            Object::Relation(relation) => relation.vertex(),
        }
    }

    pub fn into_owned(self) -> Object<'static> {
        match self {
            Object::Entity(entity) => Object::Entity(entity.into_owned()),
            Object::Relation(relation) => Object::Relation(relation.into_owned()),
        }
    }
}

impl<'a> ThingAPI<'a> for Object<'a> {
    fn set_modified(&self, snapshot: &mut impl WritableSnapshot, thing_manager: &ThingManager) {
        match self {
            Object::Entity(entity) => entity.set_modified(snapshot, thing_manager),
            Object::Relation(relation) => relation.set_modified(snapshot, thing_manager),
        }
    }

    fn get_status(&self, snapshot: &impl ReadableSnapshot, thing_manager: &ThingManager) -> ConceptStatus {
        match self {
            Object::Entity(entity) => entity.get_status(snapshot, thing_manager),
            Object::Relation(relation) => relation.get_status(snapshot, thing_manager),
        }
    }

    fn errors(
        &self,
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
    ) -> Result<Vec<ConceptWriteError>, ConceptReadError> {
        match self {
            Object::Entity(entity) => entity.errors(snapshot, thing_manager),
            Object::Relation(relation) => relation.errors(snapshot, thing_manager),
        }
    }

    fn delete(
        self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
    ) -> Result<(), ConceptWriteError> {
        match self {
            Object::Entity(entity) => entity.delete(snapshot, thing_manager),
            Object::Relation(relation) => relation.delete(snapshot, thing_manager),
        }
    }
}

pub trait ObjectAPI<'a>: ThingAPI<'a> + Clone + Debug {
    fn vertex(&self) -> ObjectVertex<'_>;
    fn into_vertex(self) -> ObjectVertex<'a>;

    fn type_(&self) -> impl ObjectTypeAPI<'static>;
    fn into_owned_object(self) -> Object<'static>;

    fn has_attribute(
        &self,
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<bool, ConceptReadError> {
        thing_manager.has_attribute(snapshot, self, attribute_type, value)
    }

    fn get_has_unordered<'m>(
        &self,
        snapshot: &'m impl ReadableSnapshot,
        thing_manager: &'m ThingManager,
    ) -> HasAttributeIterator {
        thing_manager.get_has_unordered(snapshot, self)
    }

    fn get_has_ordered<'m>(
        &self,
        snapshot: &'m impl ReadableSnapshot,
        thing_manager: &'m ThingManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<Vec<Attribute<'_>>, ConceptReadError> {
        thing_manager.get_has_type_ordered(snapshot, self, attribute_type)
    }

    fn get_has_type<'m>(
        &self,
        snapshot: &'m impl ReadableSnapshot,
        thing_manager: &'m ThingManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<HasAttributeIterator, ConceptReadError> {
        thing_manager.get_has_type_unordered(snapshot, self, attribute_type)
    }

    fn set_has_unordered(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        mut attribute: Attribute<'_>,
    ) -> Result<(), ConceptWriteError> {
        if !thing_manager.object_exists(snapshot, self)? {
            return Err(ConceptWriteError::SetHasOnDeleted { owner: self.clone().into_owned_object() });
        }

        let owns = self
            .get_type_owns(snapshot, thing_manager.type_manager(), attribute.type_())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        match owns
            .get_ordering(snapshot, thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
        {
            Ordering::Unordered => (),
            Ordering::Ordered => return Err(ConceptWriteError::SetHasUnorderedOwnsOrdered {}),
        }

        if owns.is_unique(snapshot, thing_manager.type_manager())?
            && attribute.get_owners_by_type(snapshot, thing_manager, self.type_()).count() > 0
        {
            if owns.is_key(snapshot, thing_manager.type_manager())? {
                return Err(ConceptWriteError::KeyTaken {
                    owner: self.clone().into_owned_object(),
                    key_type: attribute.type_(),
                    value: attribute.get_value(snapshot, thing_manager)?.into_owned(),
                    owner_type: self.type_().into_owned_object_type(),
                });
            } else {
                todo!()
            }
        }

        if let Some(cardinality) = owns.get_cardinality(snapshot, thing_manager.type_manager())? {
            let count = self
                .get_has_type(snapshot, thing_manager, owns.attribute())
                .map_err(|error| ConceptWriteError::ConceptRead { source: error })?
                .count();
            if !cardinality.is_valid(count as u64 + 1) {
                return Err(ConceptWriteError::MultipleKeys {
                    owner: self.clone().into_owned_object(),
                    key_type: owns.attribute(),
                });
            }
        }

        thing_manager.set_has_unordered(snapshot, self, attribute.as_reference());
        Ok(())
    }

    fn unset_has_unordered(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        attribute: Attribute<'_>,
    ) -> Result<(), ConceptWriteError> {
        let owns = self
            .get_type_owns(snapshot, thing_manager.type_manager(), attribute.type_())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        match owns
            .get_ordering(snapshot, thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
        {
            Ordering::Unordered => (),
            Ordering::Ordered => return Err(ConceptWriteError::SetHasUnorderedOwnsOrdered {}),
        }
        thing_manager.unset_has(snapshot, self, attribute);
        Ok(())
    }

    fn set_has_ordered(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        attribute_type: AttributeType<'static>,
        new_attributes: Vec<Attribute<'_>>,
    ) -> Result<(), ConceptWriteError> {
        if !thing_manager.object_exists(snapshot, self)? {
            return Err(ConceptWriteError::SetHasOnDeleted { owner: self.clone().into_owned_object() });
        }

        let owns = self
            .get_type_owns(snapshot, thing_manager.type_manager(), attribute_type.clone())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        match owns
            .get_ordering(snapshot, thing_manager.type_manager())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
        {
            Ordering::Unordered => return Err(ConceptWriteError::SetHasOrderedOwnsUnordered {}),
            Ordering::Ordered => (),
        }

        let mut new_counts = BTreeMap::<_, u64>::new();
        for attr in &new_attributes {
            *new_counts.entry(attr).or_default() += 1;
        }

        // 1. get owned list
        let old_attributes = thing_manager
            .get_has_type_ordered(snapshot, self, attribute_type.clone())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;

        let mut old_counts = BTreeMap::<_, u64>::new();
        for attr in &old_attributes {
            *old_counts.entry(attr).or_default() += 1;
        }

        // 2. Delete existing but no-longer necessary has, and add new ones, with the correct counts (!)
        for attr in old_counts.keys() {
            if !new_counts.contains_key(attr) {
                thing_manager.unset_has(snapshot, self, attr.as_reference());
            }
        }
        for (attr, count) in new_counts {
            if old_counts.get(&attr) != Some(&count) {
                thing_manager.set_has_count(snapshot, self, attr.as_reference(), count);
            }
        }

        // 3. Overwrite owned list
        thing_manager.set_has_ordered(snapshot, self, attribute_type, new_attributes)?;
        Ok(())
    }

    fn unset_has_ordered(
        &self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        let owns = self
            .get_type_owns(snapshot, thing_manager.type_manager(), attribute_type)
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        let ordering = owns
            .get_ordering(snapshot, thing_manager.type_manager())
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
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<Owns<'m>, ConceptReadError> {
        let owns = self.type_().get_owns_attribute(snapshot, type_manager, attribute_type)?;
        match owns {
            None => {
                todo!("throw useful schema error")
            }
            Some(owns) => Ok(owns),
        }
    }

    fn get_relations<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        thing_manager: &'m ThingManager,
    ) -> impl for<'x> LendingIterator<Item<'x> = Result<Relation<'x>, ConceptReadError>> {
        thing_manager.get_relations_player(snapshot, self)
    }

    fn get_relations_by_role<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        thing_manager: &'m ThingManager,
        role_type: RoleType<'static>,
    ) -> impl for<'x> LendingIterator<Item<'x> = Result<Relation<'x>, ConceptReadError>> {
        thing_manager.get_relations_player_role(snapshot, self, role_type)
    }
}

impl<'a> ObjectAPI<'a> for Object<'a> {
    fn vertex(&self) -> ObjectVertex<'_> {
        match self {
            Object::Entity(entity) => entity.vertex(),
            Object::Relation(relation) => relation.vertex(),
        }
    }

    fn into_vertex(self) -> ObjectVertex<'a> {
        match self {
            Object::Entity(entity) => entity.into_vertex(),
            Object::Relation(relation) => relation.into_vertex(),
        }
    }

    fn type_(&self) -> impl ObjectTypeAPI<'static> {
        self.type_()
    }

    fn into_owned_object(self) -> Object<'static> {
        self.into_owned()
    }
}

impl Hkt for Object<'static> {
    type HktSelf<'a> = Object<'a>;
}

fn storage_key_to_object(storage_key: StorageKey<'_, BUFFER_KEY_INLINE>) -> Object<'_> {
    Object::new(ObjectVertex::new(storage_key.into_bytes()))
}

concept_iterator!(ObjectIterator, Object, storage_key_to_object);

fn storage_key_to_has_attribute<'a>(
    storage_key: StorageKey<'a, BUFFER_KEY_INLINE>,
    value: Bytes<'a, BUFFER_VALUE_INLINE>,
) -> (Attribute<'a>, u64) {
    let edge = ThingEdgeHas::new(storage_key.into_bytes());
    (Attribute::new(edge.into_to()), decode_value_u64(value.as_reference()))
}

edge_iterator!(
    HasAttributeIterator;
    'a -> (Attribute<'a>, u64);
    storage_key_to_has_attribute
);
