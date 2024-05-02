/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

use bytes::Bytes;
use encoding::{
    graph::type_::vertex::{new_vertex_relation_type, TypeVertex},
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
        relates::Relates,
        role_type::RoleType,
        type_manager::TypeManager,
        ObjectTypeAPI, Ordering, OwnerAPI, PlayerAPI, TypeAPI,
    },
    ConceptAPI,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RelationType<'a> {
    vertex: TypeVertex<'a>,
}

impl<'a> RelationType<'a> {
    pub fn new(vertex: TypeVertex<'a>) -> RelationType<'_> {
        if vertex.prefix() != Prefix::VertexRelationType {
            panic!(
                "Type IID prefix was expected to be Prefix::RelationType ({:?}) but was {:?}",
                Prefix::VertexRelationType,
                vertex.prefix()
            )
        }
        RelationType { vertex }
    }
}

impl<'a> ConceptAPI<'a> for RelationType<'a> {}

impl<'a> TypeAPI<'a> for RelationType<'a> {
    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        self.vertex.as_reference()
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        self.vertex
    }

    fn is_abstract(&self, type_manager: &TypeManager<impl ReadableSnapshot>) -> Result<bool, ConceptReadError> {
        let annotations = self.get_annotations(type_manager)?;
        Ok(annotations.contains(&RelationTypeAnnotation::Abstract(AnnotationAbstract::new())))
    }

    fn delete<D>(self, type_manager: &TypeManager<WriteSnapshot<D>>) -> Result<(), ConceptWriteError> {
        todo!()
    }
}

impl<'a> ObjectTypeAPI<'a> for RelationType<'a> {}

impl<'a> RelationType<'a> {
    pub fn is_root(&self, type_manager: &TypeManager<impl ReadableSnapshot>) -> Result<bool, ConceptReadError> {
        type_manager.get_relation_type_is_root(self.clone().into_owned())
    }

    pub fn get_label<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        type_manager.get_relation_type_label(self.clone().into_owned())
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
    ) -> Result<Option<RelationType<'static>>, ConceptReadError> {
        type_manager.get_relation_type_supertype(self.clone().into_owned())
    }

    pub fn set_supertype<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        supertype: RelationType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.storage_set_supertype(self.clone().into_owned(), supertype);
        Ok(())
    }

    pub fn get_supertypes<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_supertypes(self.clone().into_owned())
    }

    pub fn get_subtypes<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_subtypes(self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_subtypes_transitive(self.clone().into_owned())
    }

    pub fn get_annotations<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<RelationTypeAnnotation>>, ConceptReadError> {
        type_manager.get_relation_type_annotations(self.clone().into_owned())
    }

    pub fn set_annotation<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        annotation: RelationTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.storage_set_annotation_abstract(self.clone().into_owned())
            }
        };
        Ok(())
    }

    fn delete_annotation<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, annotation: RelationTypeAnnotation) {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.storage_delete_annotation_abstract(self.clone().into_owned())
            }
        }
    }

    pub fn get_role(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        name: &str,
    ) -> Result<Option<RoleType<'static>>, ConceptReadError> {
        let label = Label::build_scoped(name, self.get_label(type_manager)?.name().as_str());
        type_manager.get_role_type(&label)
    }

    pub fn create_relates<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        name: &str,
        ordering: Ordering,
    ) -> Result<RoleType<'static>, ConceptWriteError> {
        let label = Label::build_scoped(name, self.get_label(type_manager).unwrap().name().as_str());
        type_manager.create_role_type(&label, self.clone().into_owned(), false, ordering)
    }

    fn delete_relates<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, role_type: RoleType<'static>) {
        type_manager.storage_delete_relates(self.clone().into_owned(), role_type)
    }

    pub(crate) fn get_relates<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Relates<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_relates(self.clone().into_owned())
    }

    pub fn get_relates_role(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        name: &str,
    ) -> Result<Option<Relates<'static>>, ConceptReadError> {
        Ok(self.get_role(type_manager, name)?.map(|role_type| Relates::new(self.clone().into_owned(), role_type)))
    }

    fn has_relates_role(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        name: &str,
    ) -> Result<bool, ConceptReadError> {
        Ok(self.get_relates_role(type_manager, name)?.is_some())
    }

    fn into_owned(self) -> RelationType<'static> {
        RelationType { vertex: self.vertex.into_owned() }
    }
}

impl<'a> OwnerAPI<'a> for RelationType<'a> {
    fn set_owns<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Owns<'static> {
        type_manager.storage_set_owns(self.clone().into_owned(), attribute_type.clone(), ordering);
        Owns::new(ObjectType::Relation(self.clone().into_owned()), attribute_type)
    }

    fn delete_owns<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, attribute_type: AttributeType<'static>) {
        // TODO: error if not owned?
        type_manager.storage_delete_owns(self.clone().into_owned(), attribute_type)
    }

    fn get_owns<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_owns(self.clone().into_owned())
    }

    fn get_owns_attribute(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        let expected_owns = Owns::new(ObjectType::Relation(self.clone().into_owned()), attribute_type);
        Ok(self.get_owns(type_manager)?.contains(&expected_owns).then_some(expected_owns))
    }
}

impl<'a> PlayerAPI<'a> for RelationType<'a> {
    fn set_plays<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        role_type: RoleType<'static>,
    ) -> Plays<'static> {
        // TODO: decide behaviour (ok or error) if already playing
        type_manager.storage_set_plays(self.clone().into_owned(), role_type.clone());
        Plays::new(ObjectType::Relation(self.clone().into_owned()), role_type)
    }

    fn delete_plays<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, role_type: RoleType<'static>) {
        // TODO: error if not playing?
        type_manager.storage_delete_plays(self.clone().into_owned(), role_type)
    }

    fn get_plays<'m>(
        &self,
        _type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        todo!()
        // type_manager.get_relation_type_plays(self.clone().into_owned())
    }

    fn get_plays_role(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        let expected_plays = Plays::new(ObjectType::Relation(self.clone().into_owned()), role_type);
        Ok(self.get_plays(type_manager)?.contains(&expected_plays).then_some(expected_plays))
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum RelationTypeAnnotation {
    Abstract(AnnotationAbstract),
}

impl From<Annotation> for RelationTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Abstract(annotation) => RelationTypeAnnotation::Abstract(annotation),
            Annotation::Distinct(_) => unreachable!("Distinct annotation not available for Relation type."),
            Annotation::Independent(_) => unreachable!("Independent annotation not available for Relation type."),
            Annotation::Cardinality(_) => unreachable!("Cardinality annotation not available for Relation type."),
        }
    }
}

// TODO: can we inline this into the macro invocation?
fn storage_key_to_relation_type(storage_key_ref: StorageKeyReference<'_>) -> RelationType<'_> {
    RelationType::new(new_vertex_relation_type(Bytes::Reference(storage_key_ref.byte_ref())))
}

concept_iterator!(RelationTypeIterator, RelationType, storage_key_to_relation_type);
