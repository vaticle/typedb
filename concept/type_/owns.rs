/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

use encoding::graph::type_::edge::{build_edge_owns, TypeEdge};
use primitive::maybe_owns::MaybeOwns;
use storage::snapshot::{ReadableSnapshot, WriteSnapshot};

use crate::{
    error::ConceptReadError,
    type_::{
        annotation::{Annotation, AnnotationCardinality, AnnotationDistinct},
        attribute_type::AttributeType,
        object_type::ObjectType,
        type_manager::TypeManager,
        IntoCanonicalTypeEdge, Ordering, TypeAPI,
    },
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Owns<'a> {
    owner: ObjectType<'a>,
    attribute: AttributeType<'a>,
}

impl<'a> Owns<'a> {
    pub fn new(owner_type: ObjectType<'a>, attribute_type: AttributeType<'a>) -> Self {
        Owns { owner: owner_type, attribute: attribute_type }
    }

    pub fn owner(&self) -> ObjectType<'a> {
        self.owner.clone()
    }

    pub fn attribute(&self) -> AttributeType<'a> {
        self.attribute.clone()
    }

    pub fn is_distinct<'this>(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
    ) -> Result<bool, ConceptReadError> {
        let is_ordered = false; // TODO
        if is_ordered {
            let annotations = self.get_annotations(type_manager)?;
            Ok(annotations.contains(&OwnsAnnotation::Distinct(AnnotationDistinct::new())))
        } else {
            Ok(true)
        }
    }

    pub(crate) fn get_annotations<'this>(
        &'this self,
        type_manager: &'this TypeManager<impl ReadableSnapshot>,
    ) -> Result<MaybeOwns<'this, HashSet<OwnsAnnotation>>, ConceptReadError> {
        type_manager.get_owns_annotations(self.clone())
    }

    pub fn set_annotation<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, annotation: OwnsAnnotation) {
        match annotation {
            OwnsAnnotation::Distinct(_) => type_manager.storage_set_edge_annotation_distinct(self.clone()),
            OwnsAnnotation::Cardinality(cardinality) => {
                type_manager.storage_set_edge_annotation_cardinality(self.clone(), cardinality)
            }
        }
    }

    pub fn delete_annotation<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, annotation: OwnsAnnotation) {
        match annotation {
            OwnsAnnotation::Distinct(_) => type_manager.storage_delete_edge_annotation_distinct(self.clone()),
            OwnsAnnotation::Cardinality(_) => type_manager.storage_delete_edge_annotation_cardinality(self.clone()),
        }
    }

    pub fn set_ordering<D>(&self, type_manager: &TypeManager<WriteSnapshot<D>>, ordering: Ordering) {
        type_manager.storage_set_owns_ordering(self.clone().into_type_edge(), ordering)
    }

    pub fn get_ordering(
        &self,
        type_manager: &TypeManager<impl ReadableSnapshot>,
    ) -> Result<Ordering, ConceptReadError> {
        type_manager.get_owns_ordering(self.clone().into_owned())
    }

    fn into_owned(self) -> Owns<'static> {
        Owns { owner: ObjectType::new(self.owner.vertex().into_owned()), attribute: self.attribute.into_owned() }
    }
}

impl<'a> IntoCanonicalTypeEdge<'a> for Owns<'a> {
    fn as_type_edge(&self) -> TypeEdge<'static> {
        build_edge_owns(self.owner.vertex().clone().into_owned(), self.attribute.vertex().clone().into_owned())
    }

    fn into_type_edge(self) -> TypeEdge<'static> {
        build_edge_owns(self.owner.vertex().clone().into_owned(), self.attribute.vertex().clone().into_owned())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum OwnsAnnotation {
    Distinct(AnnotationDistinct),
    Cardinality(AnnotationCardinality),
}

impl From<Annotation> for OwnsAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Distinct(annotation) => OwnsAnnotation::Distinct(annotation),
            Annotation::Cardinality(annotation) => OwnsAnnotation::Cardinality(annotation),
            Annotation::Abstract(_) => unreachable!("Independent annotation not available for Owns."),
            Annotation::Independent(_) => unreachable!("Independent annotation not available for Owns."),
        }
    }
}

