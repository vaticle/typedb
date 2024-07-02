/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{error::Error, fmt};

use encoding::{
    graph::Typed,
    value::{label::Label, value_type::ValueType},
};
use storage::snapshot::ReadableSnapshot;

use crate::{
    error::ConceptReadError,
    type_::{
        annotation::{AnnotationCategory, AnnotationCardinality, AnnotationRegex},
        attribute_type::AttributeType,
        object_type::ObjectType,
        role_type::RoleType,
        relation_type::RelationType,
        TypeAPI, Ordering
    },
};

pub mod annotation_compatibility;
pub mod commit_time_validation;
pub mod operation_time_validation;

#[derive(Debug, Clone)]
pub enum SchemaValidationError {
    ConceptRead(ConceptReadError),
    RootModification,
    LabelUniqueness(Label<'static>),
    NameUniqueness(String),
    RoleNameUniqueness(Label<'static>),
    CyclicTypeHierarchy(Label<'static>, Label<'static>), // TODO: Add details of what caused it
    RelatesNotInherited(RelationType<'static>, RoleType<'static>),
    OwnsNotInherited(ObjectType<'static>, AttributeType<'static>),
    PlaysNotInherited(ObjectType<'static>, RoleType<'static>),
    PlaysCannotBeDeclaredAsItHasBeenOverridden(Label<'static>, RoleType<'static>),
    OwnsCannotBeDeclaredAsItHasBeenOverridden(Label<'static>, AttributeType<'static>),
    OverriddenTypeNotSupertype(Label<'static>, Label<'static>),
    TypeDoesNotHaveAnnotation(Label<'static>),
    AnnotationCanOnlyBeSetOnAttributeOrOwns(Label<'static>, AnnotationCategory),
    NonAbstractCannotOwnAbstract(Label<'static>, Label<'static>),
    TypeIsNotAbstract(Label<'static>),
    NonAbstractSupertypeOfAbstractSubtype(Label<'static>, Label<'static>),
    OwnsAbstractType(Label<'static>),
    OrderingDoesNotMatchWithSupertype(Label<'static>, Label<'static>),
    InvalidOrderingForDistinctAnnotation(Label<'static>),
    AttributeTypeWithoutValueTypeShouldBeAbstract(Label<'static>),
    AnnotationRegexOnAttributeRequiresStringValueType(Label<'static>),
    AnnotationUniqueOnOwnsRequiresKeyableValueType(Label<'static>, Label<'static>),
    AnnotationKeyOnOwnsRequiresKeyableValueType(Label<'static>, Label<'static>),
    CannotSetAnnotationToInterfaceBecauseItAlreadyExistsForItsImplementation(Label<'static>, AnnotationCategory),
    CannotSetAnnotationToInterfaceImplementationBecauseItAlreadyExistsForItsInterface(Label<'static>, AnnotationCategory),
    CannotChangeValueTypeOfAttributeType(Label<'static>, Option<ValueType>),
    DeletingTypeWithSubtypes(Label<'static>),
    DeletingTypeWithInstances(Label<'static>),
    InvalidCardinalityArguments(AnnotationCardinality),
    InvalidRegexArguments(AnnotationRegex),
    CardinalityShouldNarrowInheritedCardinality(AnnotationCardinality),
    RegexCannotBeRedeclaredOnSubtypes(AnnotationRegex),
    CannotUnsetInheritedOwns(Label<'static>, Label<'static>),
    CannotUnsetInheritedPlays(Label<'static>, Label<'static>),
    CannotUnsetInheritedAnnotation(AnnotationCategory, Label<'static>),
    CannotUnsetInheritedEdgeAnnotation(AnnotationCategory),
    UnsupportedAnnotationForType(AnnotationCategory), // TODO: Also works for owns, relates and plays, consider renaming... How to pass the type as well? Considering edges!
    ValueTypeNotCompatibleWithInheritedValueTypeOf(Label<'static>, Label<'static>, ValueType),
    ValueTypeNotCompatibleWithSubtypesValueType(Label<'static>, Label<'static>, ValueType),
    NonAbstractSubtypeWithoutValueTypeExists(Label<'static>, Label<'static>),
    ValueTypeIsNotKeyable(Label<'static>, Label<'static>, Option<ValueType>),
    ValueTypeIsNotKeyableForKeyAnnotation(Label<'static>, Label<'static>, Option<ValueType>),
    ValueTypeIsNotKeyableForUniqueAnnotation(Label<'static>, Label<'static>, Option<ValueType>),
    DeclaredAnnotationIsNotCompatibleWithInheritedAnnotation(AnnotationCategory, AnnotationCategory, Label<'static>),
    AnnotationIsNotCompatibleWithDeclaredAnnotation(AnnotationCategory, AnnotationCategory, Label<'static>),
}

impl fmt::Display for SchemaValidationError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for SchemaValidationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::ConceptRead(source) => Some(source),
            Self::LabelUniqueness(_) => None,
            Self::NameUniqueness(_) => None,
            Self::RoleNameUniqueness(_) => None,
            Self::RootModification => None,
            Self::CyclicTypeHierarchy(_, _) => None,
            Self::RelatesNotInherited(_, _) => None,
            Self::OwnsNotInherited(_, _) => None,
            Self::PlaysNotInherited(_, _) => None,
            Self::PlaysCannotBeDeclaredAsItHasBeenOverridden(_, _) => None,
            Self::OwnsCannotBeDeclaredAsItHasBeenOverridden(_, _) => None,
            Self::OverriddenTypeNotSupertype(_, _) => None,
            Self::OrderingDoesNotMatchWithSupertype(_, _) => None,
            Self::InvalidOrderingForDistinctAnnotation(_) => None,
            Self::AnnotationCanOnlyBeSetOnAttributeOrOwns(_, _) => None,
            Self::TypeDoesNotHaveAnnotation(_) => None,
            Self::NonAbstractCannotOwnAbstract(_, _) => None,
            Self::TypeIsNotAbstract(_) => None,
            Self::NonAbstractSupertypeOfAbstractSubtype(_, _) => None,
            Self::OwnsAbstractType(_) => None,
            Self::AttributeTypeWithoutValueTypeShouldBeAbstract(_) => None,
            Self::AnnotationRegexOnAttributeRequiresStringValueType(_) => None,
            Self::AnnotationUniqueOnOwnsRequiresKeyableValueType(_, _) => None,
            Self::AnnotationKeyOnOwnsRequiresKeyableValueType(_, _) => None,
            Self::CannotSetAnnotationToInterfaceBecauseItAlreadyExistsForItsImplementation(_, _) => None,
            Self::CannotSetAnnotationToInterfaceImplementationBecauseItAlreadyExistsForItsInterface(_, _) => None,
            Self::CannotChangeValueTypeOfAttributeType(_, _) => None,
            Self::DeletingTypeWithSubtypes(_) => None,
            Self::DeletingTypeWithInstances(_) => None,
            Self::InvalidCardinalityArguments(_) => None,
            Self::InvalidRegexArguments(_) => None,
            Self::CardinalityShouldNarrowInheritedCardinality(_) => None,
            Self::RegexCannotBeRedeclaredOnSubtypes(_) => None,
            Self::CannotUnsetInheritedOwns(_, _) => None,
            Self::CannotUnsetInheritedPlays(_, _) => None,
            Self::CannotUnsetInheritedAnnotation(_, _) => None,
            Self::CannotUnsetInheritedEdgeAnnotation(_) => None,
            Self::UnsupportedAnnotationForType(_) => None,
            Self::ValueTypeNotCompatibleWithInheritedValueTypeOf(_, _, _) => None,
            Self::ValueTypeNotCompatibleWithSubtypesValueType(_, _, _) => None,
            Self::NonAbstractSubtypeWithoutValueTypeExists(_, _) => None,
            Self::ValueTypeIsNotKeyable(_, _, _) => None,
            Self::ValueTypeIsNotKeyableForKeyAnnotation(_, _, _) => None,
            Self::ValueTypeIsNotKeyableForUniqueAnnotation(_, _, _) => None,
            Self::DeclaredAnnotationIsNotCompatibleWithInheritedAnnotation(_, _, _) => None,
            Self::AnnotationIsNotCompatibleWithDeclaredAnnotation(_, _, _) => None,
        }
    }
}
