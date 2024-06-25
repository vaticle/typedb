/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};
use encoding::{graph::type_::edge::TypeEdgeEncoding, layout::prefix::Prefix};
use primitive::maybe_owns::MaybeOwns;
use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{Annotation, AnnotationCardinality},
        object_type::ObjectType, role_type::RoleType, type_manager::TypeManager,
        InterfaceImplementation, TypeAPI,
    },
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Plays<'a> {
    player: ObjectType<'a>,
    role: RoleType<'a>,
}

impl<'a> Plays<'a> {
    pub(crate) fn new(player: ObjectType<'a>, role: RoleType<'a>) -> Self {
        Self { player, role }
    }

    pub fn player(&self) -> ObjectType<'a> {
        self.player.clone()
    }

    pub fn role(&self) -> RoleType<'a> {
        self.role.clone()
    }

    pub fn get_override<'this, Snapshot: ReadableSnapshot>(
        &'this self,
        snapshot: &Snapshot,
        type_manager: &'this TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'this, Option<Plays<'static>>>, ConceptReadError> {
        type_manager.get_plays_overridden(snapshot, self.clone().into_owned())
    }

    pub fn set_override<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        overridden: Plays<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        type_manager.set_plays_overridden(snapshot, self.clone().into_owned(), overridden)
    }

    pub fn get_annotations_declared<'this, Snapshot: ReadableSnapshot>(
        &'this self,
        snapshot: &Snapshot,
        type_manager: &'this TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'this, HashSet<PlaysAnnotation>>, ConceptReadError> {
        type_manager.get_plays_annotations_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations<'this, Snapshot: ReadableSnapshot>(
        &'this self,
        snapshot: &Snapshot,
        type_manager: &'this TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'this, HashMap<PlaysAnnotation, Plays<'static>>>, ConceptReadError> {
        type_manager.get_plays_annotations(snapshot, self.clone().into_owned())
    }

    pub fn set_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: PlaysAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            PlaysAnnotation::Cardinality(cardinality) => {
                type_manager.set_edge_annotation_cardinality(snapshot, self.clone(), cardinality)?
            }
        }
        Ok(()) // TODO
    }

    pub fn unset_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: PlaysAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            // TODO: Add check that we unset annotation with same arguments??
            PlaysAnnotation::Cardinality(_) => type_manager.unset_edge_annotation_cardinality(snapshot, self.clone())?,
        }
        Ok(()) // TODO
    }

    fn into_owned(self) -> Plays<'static> {
        Plays { player: ObjectType::new(self.player.vertex().into_owned()), role: self.role.into_owned() }
    }
}

impl<'a> TypeEdgeEncoding<'a> for Plays<'a> {
    const CANONICAL_PREFIX: Prefix = Prefix::EdgePlays;
    const REVERSE_PREFIX: Prefix = Prefix::EdgePlaysReverse;
    type From = ObjectType<'a>;
    type To = RoleType<'a>;

    fn from_vertices(player: ObjectType<'a>, role: RoleType<'a>) -> Self {
        Plays { player, role }
    }

    fn canonical_from(&self) -> Self::From {
        self.player()
    }

    fn canonical_to(&self) -> Self::To {
        self.role()
    }
}

// Can plays not be annotated?
pub struct __PlaceholderPlaysAnnotation {}

impl<'a> InterfaceImplementation<'a> for Plays<'a> {
    type AnnotationType = __PlaceholderPlaysAnnotation;
    type ObjectType = ObjectType<'a>;
    type InterfaceType = RoleType<'a>;

    fn object(&self) -> ObjectType<'a> {
        self.player.clone()
    }

    fn interface(&self) -> RoleType<'a> {
        self.role.clone()
    }

    fn unwrap_annotation(annotation: __PlaceholderPlaysAnnotation) -> Annotation {
        unreachable!();
    }
}


#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum PlaysAnnotation {
    Cardinality(AnnotationCardinality),
}

impl From<Annotation> for PlaysAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Cardinality(annotation) => PlaysAnnotation::Cardinality(annotation),

            Annotation::Abstract(_) => unreachable!("Abstract annotation not available for Plays."),
            Annotation::Independent(_) => unreachable!("Independent annotation not available for Plays."),
            Annotation::Distinct(annotation) => unreachable!("Distinct annotation not available for Plays."),
            Annotation::Unique(annotation) => unreachable!("Unique annotation not available for Plays."),
            Annotation::Key(annotation) => unreachable!("Key annotation not available for Plays."),
            Annotation::Regex(annotation) => unreachable!("Regex annotation not available for Plays."),
        }
    }
}

impl Into<Annotation> for PlaysAnnotation {
    fn into(self) -> Annotation {
        match self {
            PlaysAnnotation::Cardinality(annotation) => Annotation::Cardinality(annotation),
        }
    }
}

impl PartialEq<Annotation> for PlaysAnnotation {
    fn eq(&self, annotation: &Annotation) -> bool {
        match annotation {
            Annotation::Cardinality(other_cardinality) => {
                if let Self::Cardinality(cardinality) = self {
                    cardinality == other_cardinality
                } else {
                    false
                }
            }

            Annotation::Abstract(_) => false,
            Annotation::Independent(_) => false,
            Annotation::Distinct(_) => false,
            Annotation::Unique(_) => false,
            Annotation::Key(_) => false,
            Annotation::Regex(_) => false,
        }
    }
}
