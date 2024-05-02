/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

use bytes::Bytes;
use encoding::{
    graph::type_::vertex::{new_vertex_entity_type, TypeVertex},
    layout::prefix::Prefix,
    value::label::Label,
    Prefixed,
};
use primitive::maybe_owns::MaybeOwns;
use storage::{
    key_value::StorageKeyReference,
    snapshot::{ReadableSnapshot, WriteSnapshot},
};

use crate::{
    concept_iterator,
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{Annotation, AnnotationAbstract},
        attribute_type::AttributeType,
        object_type::ObjectType,
        owns::Owns,
        plays::Plays,
        role_type::RoleType,
        type_manager::TypeManager,
        ObjectTypeAPI, Ordering, OwnerAPI, PlayerAPI, TypeAPI,
    },
    ConceptAPI,
};

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct EntityType<'a> {
    vertex: TypeVertex<'a>,
}

impl<'a> EntityType<'a> {
    pub fn new(vertex: TypeVertex<'a>) -> EntityType<'_> {
        if vertex.prefix() != Prefix::VertexEntityType {
            panic!(
                "Type IID prefix was expected to be Prefix::EntityType ({:?}) but was {:?}",
                Prefix::VertexEntityType,
                vertex.prefix()
            )
        }
        EntityType { vertex }
    }
}

impl<'a> ConceptAPI<'a> for EntityType<'a> {}

impl<'a> TypeAPI<'a> for EntityType<'a> {
    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        self.vertex.as_reference()
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        self.vertex
    }

    fn is_abstract(&self, type_manager: &TypeManager<impl ReadableSnapshot>) -> Result<bool, ConceptReadError> {
        let annotations = self.get_annotations(type_manager)?;
        Ok(annotations.contains(&EntityTypeAnnotation::Abstract(AnnotationAbstract::new())))
    }

    fn delete<D>(self, type_manager: &TypeManager<WriteSnapshot<D>>) -> Result<(), ConceptWriteError> {
        // todo!("Validation");
        type_manager.delete_entity_type(self);
        Ok(())
    }
}

impl<'a> ObjectTypeAPI<'a> for EntityType<'a> {}

impl<'a> EntityType<'a> {
    pub fn is_root(&self, type_manager: &TypeManager<impl ReadableSnapshot>) -> Result<bool, ConceptReadError> {
        type_manager.get_entity_type_is_root(self.clone().into_owned())
    }

    pub fn get_label<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        type_manager.get_entity_type_label(self.clone().into_owned())
    }

    pub fn set_label<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        label: &Label<'_>,
    ) -> Result<(), ConceptWriteError> {
        if self.is_root(type_manager)? {
            Err(ConceptWriteError::RootModification)
        } else {
            Ok(type_manager.storage_set_label(self.clone().into_owned(), label))
        }
    }

    pub fn get_supertype(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
    ) -> Result<Option<EntityType<'_>>, ConceptReadError> {
        type_manager.get_entity_type_supertype(self.clone().into_owned())
    }

    pub fn set_supertype<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        supertype: EntityType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.storage_set_supertype(self.clone().into_owned(), supertype);
        Ok(())
    }

    pub fn get_supertypes<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<EntityType<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_supertypes(self.clone().into_owned())
    }

    pub fn get_subtypes<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<EntityType<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_subtypes(self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<EntityType<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_subtypes_transitive(self.clone().into_owned())
    }

    pub fn get_annotations<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<EntityTypeAnnotation>>, ConceptReadError> {
        type_manager.get_entity_type_annotations(self.clone().into_owned())
    }

    pub fn set_annotation<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        annotation: EntityTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            EntityTypeAnnotation::Abstract(_) => {
                type_manager.storage_set_annotation_abstract(self.clone().into_owned())
            }
        };
        Ok(())
    }

    fn delete_annotation<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, annotation: EntityTypeAnnotation) {
        match annotation {
            EntityTypeAnnotation::Abstract(_) => {
                type_manager.storage_delete_annotation_abstract(self.clone().into_owned())
            }
        }
    }

    fn into_owned(self) -> EntityType<'static> {
        EntityType { vertex: self.vertex.into_owned() }
    }
}

impl<'a> OwnerAPI<'a> for EntityType<'a> {
    fn set_owns<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Owns<'static> {
        type_manager.storage_set_owns(self.clone().into_owned(), attribute_type.clone(), ordering);
        Owns::new(ObjectType::Entity(self.clone().into_owned()), attribute_type)
    }

    fn delete_owns<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, attribute_type: AttributeType<'static>) {
        // TODO: error if not owned?
        type_manager.storage_delete_owns(self.clone().into_owned(), attribute_type)
    }

    fn get_owns<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_owns(self.clone().into_owned())
    }

    fn get_owns_attribute(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        let expected_owns = Owns::new(ObjectType::Entity(self.clone().into_owned()), attribute_type);
        Ok(self.get_owns(type_manager)?.contains(&expected_owns).then_some(expected_owns))
    }
}

impl<'a> PlayerAPI<'a> for EntityType<'a> {
    fn set_plays<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
    ) -> Plays<'static> {
        // TODO: decide behaviour (ok or error) if already playing
        type_manager.storage_set_plays(self.clone().into_owned(), role_type.clone());
        Plays::new(ObjectType::Entity(self.clone().into_owned()), role_type)
    }

    fn delete_plays<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, role_type: RoleType<'static>) {
        // TODO: error if not playing
        type_manager.storage_delete_plays(self.clone().into_owned(), role_type)
    }

    fn get_plays<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_plays(self.clone().into_owned())
    }

    fn get_plays_role(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        let expected_plays = Plays::new(ObjectType::Entity(self.clone().into_owned()), role_type);
        Ok(self.get_plays(type_manager)?.contains(&expected_plays).then_some(expected_plays))
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum EntityTypeAnnotation {
    Abstract(AnnotationAbstract),
}

impl From<Annotation> for EntityTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Abstract(annotation) => EntityTypeAnnotation::Abstract(annotation),
            Annotation::Distinct(_) => unreachable!("Distinct annotation not available for Entity type."),
            Annotation::Independent(_) => unreachable!("Independent annotation not available for Entity type."),
            Annotation::Cardinality(_) => unreachable!("Cardinality annotation not available for Entity type."),
        }
    }
}

// impl<'a> IIDAPI<'a> for EntityType<'a> {
//     fn iid(&'a self) -> ByteReference<'a> {
//         self.vertex.bytes()
//     }
// }

// TODO: can we inline this into the macro invocation?
fn storage_key_ref_to_entity_type(storage_key_ref: StorageKeyReference<'_>) -> EntityType<'_> {
    EntityType::new(new_vertex_entity_type(Bytes::Reference(storage_key_ref.byte_ref())))
}

concept_iterator!(EntityTypeIterator, EntityType, storage_key_ref_to_entity_type);
