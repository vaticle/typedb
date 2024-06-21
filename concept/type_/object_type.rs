/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use encoding::{
    error::{EncodingError, EncodingError::UnexpectedPrefix},
    graph::type_::vertex::{TypeVertex, TypeVertexEncoding},
    layout::prefix::Prefix,
    value::label::Label,
    Prefixed,
};
use primitive::maybe_owns::MaybeOwns;
use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        attribute_type::AttributeType, entity_type::EntityType, owns::Owns, plays::Plays, relation_type::RelationType,
        role_type::RoleType, type_manager::TypeManager, ObjectTypeAPI, Ordering, OwnerAPI, PlayerAPI, TypeAPI,
    },
    ConceptAPI,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ObjectType<'a> {
    Entity(EntityType<'a>),
    Relation(RelationType<'a>),
}

impl<'a> ObjectType<'a> {
    pub fn get_supertype<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<Option<ObjectType<'_>>, ConceptReadError> {
        Ok(match self {
            ObjectType::Entity(entity) => entity.get_supertype(snapshot, type_manager)?.map(ObjectType::Entity),
            ObjectType::Relation(relation) => relation.get_supertype(snapshot, type_manager)?.map(ObjectType::Relation),
        })
    }

    pub(crate) fn into_owned(self) -> ObjectType<'static> {
        match self {
            Self::Entity(entity_type) => ObjectType::Entity(entity_type.into_owned()),
            Self::Relation(relation_type) => ObjectType::Relation(relation_type.into_owned()),
        }
    }
}

impl<'a> TypeVertexEncoding<'a> for ObjectType<'a> {
    fn from_vertex(vertex: TypeVertex<'a>) -> Result<Self, EncodingError> {
        match vertex.prefix() {
            Prefix::VertexEntityType => Ok(ObjectType::Entity(EntityType::new(vertex))),
            Prefix::VertexRelationType => Ok(ObjectType::Relation(RelationType::new(vertex))),
            _ => Err(UnexpectedPrefix { actual_prefix: vertex.prefix(), expected_prefix: Prefix::VertexEntityType }), // TODO: That's not right. It can also be VertexRelationType
        }
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        match self {
            ObjectType::Entity(entity) => entity.into_vertex(),
            ObjectType::Relation(relation) => relation.into_vertex(),
        }
    }
}

impl<'a> OwnerAPI<'a> for ObjectType<'a> {
    fn set_owns<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Result<Owns<'static>, ConceptWriteError> {
        match self {
            ObjectType::Entity(entity) => entity.set_owns(snapshot, type_manager, attribute_type, ordering),
            ObjectType::Relation(relation) => relation.set_owns(snapshot, type_manager, attribute_type, ordering),
        }
    }

    fn delete_owns<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        match self {
            ObjectType::Entity(entity) => entity.delete_owns(snapshot, type_manager, attribute_type),
            ObjectType::Relation(relation) => relation.delete_owns(snapshot, type_manager, attribute_type),
        }
    }

    fn get_owns<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_owns(snapshot, type_manager),
            ObjectType::Relation(relation) => relation.get_owns(snapshot, type_manager),
        }
    }

    fn get_owns_attribute<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_owns_attribute(snapshot, type_manager, attribute_type),
            ObjectType::Relation(relation) => relation.get_owns_attribute(snapshot, type_manager, attribute_type),
        }
    }

    fn get_owns_transitive<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_owns_transitive(snapshot, type_manager),
            ObjectType::Relation(relation) => relation.get_owns_transitive(snapshot, type_manager),
        }
    }
}

impl<'a> ConceptAPI<'a> for ObjectType<'a> {}

impl<'a> TypeAPI<'a> for ObjectType<'a> {
    type SelfStatic = RelationType<'static>;

    fn new(vertex: TypeVertex<'a>) -> Self {
        Self::from_vertex(vertex).unwrap()
    }

    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        match self {
            ObjectType::Entity(entity) => entity.vertex(),
            ObjectType::Relation(relation) => relation.vertex(),
        }
    }

    fn is_abstract<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.is_abstract(snapshot, type_manager),
            ObjectType::Relation(relation) => relation.is_abstract(snapshot, type_manager),
        }
    }

    fn delete<Snapshot: WritableSnapshot>(
        self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<(), ConceptWriteError> {
        match self {
            ObjectType::Entity(entity) => entity.delete(snapshot, type_manager),
            ObjectType::Relation(relation) => relation.delete(snapshot, type_manager),
        }
    }

    fn get_label<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        match self {
            Self::Entity(entity_type) => entity_type.get_label(snapshot, type_manager),
            Self::Relation(relation_type) => relation_type.get_label(snapshot, type_manager),
        }
    }
}

impl<'a> ObjectTypeAPI<'a> for ObjectType<'a> {
    fn into_owned_object_type(self) -> ObjectType<'static> {
        self.into_owned()
    }
}

impl<'a> PlayerAPI<'a> for ObjectType<'a> {
    fn set_plays<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Plays<'static>, ConceptWriteError> {
        match self {
            ObjectType::Entity(entity) => entity.set_plays(snapshot, type_manager, role_type),
            ObjectType::Relation(relation) => relation.set_plays(snapshot, type_manager, role_type),
        }
    }

    fn delete_plays<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<(), ConceptWriteError> {
        match self {
            ObjectType::Entity(entity) => entity.delete_plays(snapshot, type_manager, role_type),
            ObjectType::Relation(relation) => relation.delete_plays(snapshot, type_manager, role_type),
        }
    }

    fn get_plays<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_plays(snapshot, type_manager),
            ObjectType::Relation(relation) => relation.get_plays(snapshot, type_manager),
        }
    }

    fn get_plays_role<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_plays_role(snapshot, type_manager, role_type),
            ObjectType::Relation(relation) => relation.get_plays_role(snapshot, type_manager, role_type),
        }
    }

    fn get_plays_transitive<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        match self {
            ObjectType::Entity(entity) => entity.get_plays_transitive(snapshot, type_manager),
            ObjectType::Relation(relation) => relation.get_plays_transitive(snapshot, type_manager),
        }
    }
}
