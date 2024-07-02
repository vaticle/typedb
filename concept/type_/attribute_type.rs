/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use encoding::{
    error::{EncodingError, EncodingError::UnexpectedPrefix},
    graph::type_::{
        vertex::{PrefixedTypeVertexEncoding, TypeVertex, TypeVertexEncoding},
        Kind,
    },
    layout::prefix::{Prefix, Prefix::VertexAttributeType},
    value::{label::Label, value_type::ValueType},
    Prefixed,
};
use primitive::maybe_owns::MaybeOwns;
use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use super::annotation::{AnnotationCategory, AnnotationRegex};
use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{Annotation, AnnotationAbstract, AnnotationIndependent},
        object_type::ObjectType,
        owns::Owns,
        type_manager::TypeManager,
        KindAPI, TypeAPI,
    },
    ConceptAPI,
};
use crate::type_::relation_type::RelationTypeAnnotation;
use crate::type_::role_type::RoleTypeAnnotation;
use crate::type_::type_manager::validation::SchemaValidationError;
use crate::type_::type_manager::validation::SchemaValidationError::UnsupportedAnnotationForType;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AttributeType<'a> {
    vertex: TypeVertex<'a>,
}

impl<'a> AttributeType<'a> {}

impl<'a> ConceptAPI<'a> for AttributeType<'a> {}

impl<'a> PrefixedTypeVertexEncoding<'a> for AttributeType<'a> {
    const PREFIX: Prefix = VertexAttributeType;
}

impl<'a> TypeVertexEncoding<'a> for AttributeType<'a> {
    fn from_vertex(vertex: TypeVertex<'a>) -> Result<Self, EncodingError> {
        debug_assert!(Self::PREFIX == VertexAttributeType);
        if vertex.prefix() != Prefix::VertexAttributeType {
            Err(UnexpectedPrefix { expected_prefix: Prefix::VertexAttributeType, actual_prefix: vertex.prefix() })
        } else {
            Ok(AttributeType { vertex })
        }
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        self.vertex
    }
}

impl<'a> primitive::prefix::Prefix for AttributeType<'a> {
    fn starts_with(&self, other: &Self) -> bool {
        self.vertex().starts_with(&other.vertex())
    }

    fn into_starts_with(self, other: Self) -> bool {
        self.vertex().as_reference().into_starts_with(other.vertex().as_reference())
    }
}

impl<'a> TypeAPI<'a> for AttributeType<'a> {
    type SelfStatic = AttributeType<'static>;

    fn new(vertex: TypeVertex<'a>) -> AttributeType<'a> {
        Self::from_vertex(vertex).unwrap()
    }

    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        self.vertex.as_reference()
    }

    fn is_abstract<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        let annotations = self.get_annotations(snapshot, type_manager)?;
        Ok(annotations.contains_key(&AttributeTypeAnnotation::Abstract(AnnotationAbstract)))
    }

    fn delete<Snapshot: WritableSnapshot>(
        self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        type_manager.delete_attribute_type(snapshot, self)
    }

    fn get_label<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        type_manager.get_attribute_type_label(snapshot, self.clone().into_owned())
    }
}

impl<'a> KindAPI<'a> for AttributeType<'a> {
    type AnnotationType = AttributeTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Attribute;
}

impl<'a> AttributeType<'a> {
    pub fn is_root<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        type_manager.get_attribute_type_is_root(snapshot, self.clone().into_owned())
    }

    pub fn get_value_type<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<Option<ValueType>, ConceptReadError> {
        type_manager
            .get_attribute_type_value_type(snapshot, self.clone().into_owned())
            .map(|value_type_opt| value_type_opt
                .map(|(value_type, source)| value_type))
    }

    pub fn set_value_type<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        value_type: ValueType,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_value_type(snapshot, self.clone().into_owned(), value_type)
    }

    pub fn unset_value_type<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.unset_value_type(snapshot, self.clone().into_owned())
    }

    pub fn set_label<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        label: &Label<'_>,
    ) -> Result<(), ConceptWriteError> {
        if self.is_root(snapshot, type_manager)? {
            Err(ConceptWriteError::RootModification) // TODO: Move into TypeManager?
        } else {
            type_manager.set_label(snapshot, self.clone().into_owned(), label)
        }
    }

    pub fn get_supertype<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<Option<AttributeType<'static>>, ConceptReadError> {
        type_manager.get_attribute_type_supertype(snapshot, self.clone().into_owned())
    }

    pub fn set_supertype<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        supertype: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_attribute_type_supertype(snapshot, self.clone().into_owned(), supertype)
    }

    pub fn get_supertypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<AttributeType<'static>>>, ConceptReadError> {
        type_manager.get_attribute_type_supertypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<AttributeType<'static>>>, ConceptReadError> {
        type_manager.get_attribute_type_subtypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<AttributeType<'static>>>, ConceptReadError> {
        type_manager.get_attribute_type_subtypes_transitive(snapshot, self.clone().into_owned())
    }

    pub(crate) fn is_independent<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        Ok(self
            .get_annotations(snapshot, type_manager)?
            .contains_key(&AttributeTypeAnnotation::Independent(AnnotationIndependent)))
    }

    pub fn get_annotations_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<AttributeTypeAnnotation>>, ConceptReadError> {
        type_manager.get_attribute_type_annotations_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<AttributeTypeAnnotation, AttributeType<'static>>>, ConceptReadError> {
        type_manager.get_attribute_type_annotations(snapshot, self.clone().into_owned())
    }

    pub fn set_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: AttributeTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            AttributeTypeAnnotation::Abstract(_) => {
                type_manager.set_annotation_abstract(snapshot, self.clone().into_owned())?
            }
            AttributeTypeAnnotation::Independent(_) => {
                type_manager.set_annotation_independent(snapshot, self.clone().into_owned())?
            }
            AttributeTypeAnnotation::Regex(regex) => {
                type_manager.set_annotation_regex(snapshot, self.clone().into_owned(), regex)?
            }
        };
        Ok(())
    }

    pub fn unset_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation_category: AnnotationCategory,
    ) -> Result<(), ConceptWriteError> {
        let relation_type_annotation = AttributeTypeAnnotation::try_getting_default(annotation_category)
            .map_err(|source| ConceptWriteError::Operation {source})?;
        match relation_type_annotation {
            AttributeTypeAnnotation::Abstract(_) => {
                type_manager.unset_attribute_type_annotation_abstract(snapshot, self.clone().into_owned())?
            }
            AttributeTypeAnnotation::Independent(_) => {
                type_manager.unset_annotation_independent(snapshot, self.clone().into_owned())?
            }
            AttributeTypeAnnotation::Regex(_) => {
                type_manager.unset_annotation_regex(snapshot, self.clone().into_owned())?
            }
        }
        Ok(()) // TODO
    }

    pub fn into_owned(self) -> AttributeType<'static> {
        AttributeType { vertex: self.vertex.into_owned() }
    }
}

// --- Owned API ---
impl<'a> AttributeType<'a> {
    pub fn get_owns_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError> {
        type_manager.get_owns_for_attribute_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_owns<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<ObjectType<'static>, Owns<'static>>>, ConceptReadError> {
        type_manager.get_owns_for_attribute(snapshot, self.clone().into_owned())
    }

    fn get_owns_owners<Snapshot: ReadableSnapshot>(&self) {
        // TODO: Why not just have owns?
        todo!()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum AttributeTypeAnnotation {
    Abstract(AnnotationAbstract),
    Independent(AnnotationIndependent),
    Regex(AnnotationRegex),
}

impl AttributeTypeAnnotation {
    pub fn try_getting_default(annotation_category: AnnotationCategory) -> Result<AttributeTypeAnnotation, SchemaValidationError> {
        annotation_category.to_default_annotation().into()
    }
}

impl From<Annotation> for Result<AttributeTypeAnnotation, SchemaValidationError> {
    fn from(annotation: Annotation) -> Result<AttributeTypeAnnotation, SchemaValidationError> {
        match annotation {
            Annotation::Abstract(annotation) => Ok(AttributeTypeAnnotation::Abstract(annotation)),
            Annotation::Independent(annotation) => Ok(AttributeTypeAnnotation::Independent(annotation)),
            Annotation::Regex(annotation) => Ok(AttributeTypeAnnotation::Regex(annotation)),

            Annotation::Distinct(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Unique(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Key(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Cardinality(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Cascade(_) => Err(UnsupportedAnnotationForType(annotation.category())),
        }
    }
}

impl From<Annotation> for AttributeTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        let into_annotation: Result<AttributeTypeAnnotation, SchemaValidationError> = annotation.into();
        match into_annotation {
            Ok(into_annotation) => into_annotation,
            Err(_) => unreachable!("Do not call this conversion from user-exposed code!"),
        }
    }
}

impl Into<Annotation> for AttributeTypeAnnotation {
    fn into(self) -> Annotation {
        match self {
            AttributeTypeAnnotation::Abstract(annotation)=> Annotation::Abstract(annotation),
            AttributeTypeAnnotation::Independent(annotation)=> Annotation::Independent(annotation),
            AttributeTypeAnnotation::Regex(annotation)=> Annotation::Regex(annotation),
        }
    }
}
