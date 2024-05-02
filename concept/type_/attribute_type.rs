/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

use encoding::{
    graph::type_::vertex::TypeVertex,
    layout::prefix::Prefix,
    value::{label::Label, value_type::ValueType},
    Prefixed,
};
use primitive::maybe_owns::MaybeOwns;
use storage::snapshot::{ReadableSnapshot, WriteSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{Annotation, AnnotationAbstract, AnnotationIndependent},
        owns::Owns,
        type_manager::TypeManager,
        TypeAPI,
    },
    ConceptAPI,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AttributeType<'a> {
    vertex: TypeVertex<'a>,
}

impl<'a> AttributeType<'a> {
    pub fn new(vertex: TypeVertex<'a>) -> AttributeType<'_> {
        if vertex.prefix() != Prefix::VertexAttributeType {
            panic!(
                "Type IID prefix was expected to be Prefix::AttributeType ({:?}) but was {:?}",
                Prefix::VertexAttributeType,
                vertex.prefix()
            )
        }
        AttributeType { vertex }
    }
}

impl<'a> ConceptAPI<'a> for AttributeType<'a> {}

impl<'a> TypeAPI<'a> for AttributeType<'a> {
    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        self.vertex.as_reference()
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        self.vertex
    }

    fn is_abstract(&self, type_manager: &TypeManager<impl ReadableSnapshot>) -> Result<bool, ConceptReadError> {
        let annotations = self.get_annotations(type_manager)?;
        Ok(annotations.contains(&AttributeTypeAnnotation::Abstract(AnnotationAbstract::new())))
    }

    fn delete<D>(self, type_manager: &TypeManager<WriteSnapshot<D>>) -> Result<(), ConceptWriteError> {
        todo!()
    }
}

impl<'a> AttributeType<'a> {
    pub fn is_root(&self, type_manager: &TypeManager<impl ReadableSnapshot>) -> Result<bool, ConceptReadError> {
        type_manager.get_attribute_type_is_root(self.clone().into_owned())
    }

    pub fn set_value_type<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, value_type: ValueType) {
        type_manager.storage_set_value_type(self.clone().into_owned(), value_type)
    }

    pub fn get_value_type(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
    ) -> Result<Option<ValueType>, ConceptReadError> {
        type_manager.get_attribute_type_value_type(self.clone().into_owned())
    }

    pub fn get_label<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        type_manager.get_attribute_type_label(self.clone().into_owned())
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
    ) -> Result<Option<AttributeType<'static>>, ConceptReadError> {
        type_manager.get_attribute_type_supertype(self.clone().into_owned())
    }

    pub fn set_supertype<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        supertype: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.storage_set_supertype(self.clone().into_owned(), supertype);
        Ok(())
    }

    pub fn get_supertypes<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<AttributeType<'static>>>, ConceptReadError> {
        type_manager.get_attribute_type_supertypes(self.clone().into_owned())
    }

    pub fn get_subtypes<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<AttributeType<'static>>>, ConceptReadError> {
        type_manager.get_attribute_type_subtypes(self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, Vec<AttributeType<'static>>>, ConceptReadError> {
        type_manager.get_attribute_type_subtypes_transitive(self.clone().into_owned())
    }

    pub(crate) fn is_independent(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
    ) -> Result<bool, ConceptReadError> {
        Ok(self
            .get_annotations(type_manager)?
            .contains(&AttributeTypeAnnotation::Independent(AnnotationIndependent::new())))
    }

    pub fn get_annotations<'m>(
        &self,
        type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<AttributeTypeAnnotation>>, ConceptReadError> {
        type_manager.get_attribute_type_annotations(self.clone().into_owned())
    }

    pub fn set_annotation<D>(
        &self,
        type_manager: &TypeManager<WriteSnapshot<D>>,
        annotation: AttributeTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            AttributeTypeAnnotation::Abstract(_) => {
                type_manager.storage_set_annotation_abstract(self.clone().into_owned())
            }
            AttributeTypeAnnotation::Independent(_) => {
                type_manager.storage_set_annotation_independent(self.clone().into_owned())
            }
        };
        Ok(())
    }

    fn delete_annotation<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, annotation: AttributeTypeAnnotation) {
        match annotation {
            AttributeTypeAnnotation::Abstract(_) => {
                type_manager.storage_delete_annotation_abstract(self.clone().into_owned())
            }
            AttributeTypeAnnotation::Independent(_) => {
                type_manager.storage_storage_annotation_independent(self.clone().into_owned())
            }
        }
    }

    pub fn into_owned(self) -> AttributeType<'static> {
        AttributeType { vertex: self.vertex.into_owned() }
    }
}

// --- Owned API ---
impl<'a> AttributeType<'a> {
    fn get_owns<'m>(
        &self,
        _type_manager: &'m TypeManager<impl ReadableSnapshot>,
    ) -> MaybeOwns<'m, HashSet<Owns<'static>>> {
        todo!()
    }

    fn get_owns_owners(&self) {
        // return iterator of Owns
        todo!()
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum AttributeTypeAnnotation {
    Abstract(AnnotationAbstract),
    Independent(AnnotationIndependent),
}

impl From<Annotation> for AttributeTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Abstract(annotation) => AttributeTypeAnnotation::Abstract(annotation),
            Annotation::Independent(annotation) => AttributeTypeAnnotation::Independent(annotation),
            Annotation::Distinct(_) => unreachable!("Distinct annotation not available for Attribute type."),
            Annotation::Cardinality(_) => unreachable!("Cardinality annotation not available for Attribute type."),
        }
    }
}
