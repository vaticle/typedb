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
    type_::{annotation::AnnotationCategory, attribute_type::AttributeType, object_type::ObjectType, role_type::RoleType, TypeAPI, Ordering},
};

pub mod annotation_compatibility;
pub mod commit_time_validation;
pub mod operation_time_validation;

#[derive(Debug, Clone)]
pub enum SchemaValidationError {
    ConceptRead(ConceptReadError),
    RootModification,
    LabelUniqueness(Label<'static>),
    RoleNameUniqueness(Label<'static>),
    CyclicTypeHierarchy(Label<'static>, Label<'static>), // TODO: Add details of what caused it
    RelatesNotInherited(RoleType<'static>),
    OwnsNotInherited(AttributeType<'static>),
    PlaysNotInherited(ObjectType<'static>, RoleType<'static>),
    OverriddenTypeNotSupertype(Label<'static>, Label<'static>),
    PlaysNotDeclared(ObjectType<'static>, RoleType<'static>),
    TypeDoesNotHaveAnnotation(Label<'static>),
    AnnotationCanOnlyBeSetOnAttributeOrOwns(Label<'static>, AnnotationCategory),
    NonAbstractCannotOwnAbstract(Label<'static>, Label<'static>),
    TypeIsNotAbstract(Label<'static>),
    OwnsAbstractType(Label<'static>),
    TypeOrderingIsIncompatible(Ordering),
    AbsentValueType,
    IncompatibleValueType(Option<ValueType>),
    IncompatibleValueTypes(Option<ValueType>, Option<ValueType>),
    DeletingTypeWithSubtypes(Label<'static>),
    DeletingTypeWithInstances(Label<'static>),
    InvalidCardinalityArguments(u64, Option<u64>),
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
            Self::RoleNameUniqueness(_) => None,
            Self::RootModification => None,
            Self::CyclicTypeHierarchy(_, _) => None,
            Self::RelatesNotInherited(_) => None,
            Self::OwnsNotInherited(_) => None,
            Self::PlaysNotInherited(_, _) => None,
            Self::OverriddenTypeNotSupertype(_, _) => None,
            Self::PlaysNotDeclared(_, _) => None,
            Self::TypeOrderingIsIncompatible(_) => None,
            Self::AnnotationCanOnlyBeSetOnAttributeOrOwns(_, _) => None,
            Self::TypeDoesNotHaveAnnotation(_) => None,
            Self::NonAbstractCannotOwnAbstract(_, _) => None,
            Self::TypeIsNotAbstract(_) => None,
            Self::OwnsAbstractType(_) => None,
            Self::AbsentValueType => None,
            Self::IncompatibleValueType(_) => None,
            Self::IncompatibleValueTypes(_, _) => None,
            Self::DeletingTypeWithSubtypes(_) => None,
            Self::DeletingTypeWithInstances(_) => None,
            Self::InvalidCardinalityArguments(_, _) => None,
        }
    }
}
