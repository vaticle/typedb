/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

use encoding::{graph::type_::vertex::TypeVertex, layout::prefix::Prefix, Prefixed};
use primitive::maybe_owns::MaybeOwns;
use storage::snapshot::{ReadableSnapshot, WriteSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        attribute_type::AttributeType, entity_type::EntityType, owns::Owns, plays::Plays, relation_type::RelationType,
        role_type::RoleType, type_manager::TypeManager, Ordering, OwnerAPI, PlayerAPI, TypeAPI,
    },
    ConceptAPI,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ObjectType<'a> {
    Entity(EntityType<'a>),
    Relation(RelationType<'a>),
}

impl<'a> ObjectType<'a> {
    pub(crate) fn new(vertex: TypeVertex<'a>) -> Self {
        match vertex.prefix() {
            Prefix::VertexEntityType => ObjectType::Entity(EntityType::new(vertex)),
            Prefix::VertexRelationType => ObjectType::Relation(RelationType::new(vertex)),
            _ => unreachable!("Object type creation requires either entity type or relation type vertex."),
        }
    }
}

impl<'a> OwnerAPI<'a> for ObjectType<'a> {
    fn set_owns<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Owns<'static> {
        // TODO: decide behaviour (ok or error) if already owning
        match self {
            ObjectType::Entity(entity) => entity.set_owns(type_manager, attribute_type, ordering),
            ObjectType::Relation(relation) => relation.set_owns(type_manager, attribute_type, ordering),
        }
    }

    fn delete_owns<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, attribute_type: AttributeType<'static>) {
        match self {
            ObjectType::Entity(entity) => entity.delete_owns(type_manager, attribute_type),
            ObjectType::Relation(relation) => relation.delete_owns(type_manager, attribute_type),
        }
    }

    fn get_owns<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_owns(type_manager),
            ObjectType::Relation(relation) => relation.get_owns(type_manager),
        }
    }

    fn get_owns_attribute(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_owns_attribute(type_manager, attribute_type),
            ObjectType::Relation(relation) => relation.get_owns_attribute(type_manager, attribute_type),
        }
    }
}

impl<'a> ConceptAPI<'a> for ObjectType<'a> {}

impl<'a> TypeAPI<'a> for ObjectType<'a> {
    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        match self {
            ObjectType::Entity(entity) => entity.vertex(),
            ObjectType::Relation(relation) => relation.vertex(),
        }
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        match self {
            ObjectType::Entity(entity) => entity.into_vertex(),
            ObjectType::Relation(relation) => relation.into_vertex(),
        }
    }

    fn is_abstract(&self, type_manager: &TypeManager<impl ReadableSnapshot>) -> Result<bool, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.is_abstract(type_manager),
            ObjectType::Relation(relation) => relation.is_abstract(type_manager),
        }
    }

    fn delete<D>(self, type_manager: &TypeManager<WriteSnapshot<D>>) -> Result<(), ConceptWriteError> {
        match self {
            ObjectType::Entity(entity) => entity.delete(type_manager),
            ObjectType::Relation(relation) => relation.delete(type_manager),
        }
    }
}

impl<'a> PlayerAPI<'a> for ObjectType<'a> {
    fn set_plays<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
    ) -> Plays<'static> {
        match self {
            ObjectType::Entity(entity) => entity.set_plays(type_manager, role_type),
            ObjectType::Relation(relation) => relation.set_plays(type_manager, role_type),
        }
    }

    fn delete_plays<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, role_type: RoleType<'static>) {
        match self {
            ObjectType::Entity(entity) => entity.delete_plays(type_manager, role_type),
            ObjectType::Relation(relation) => relation.delete_plays(type_manager, role_type),
        }
    }

    fn get_plays<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_plays(type_manager),
            ObjectType::Relation(relation) => relation.get_plays(type_manager),
        }
    }

    fn get_plays_role(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_plays_role(type_manager, role_type),
            ObjectType::Relation(relation) => relation.get_plays_role(type_manager, role_type),
        }
    }
}
