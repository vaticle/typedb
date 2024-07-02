/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{error::Error, fmt, sync::Arc};

use encoding::{
    error::EncodingError,
    value::{value::Value, value_type::ValueType},
};
use storage::snapshot::{iterator::SnapshotIteratorError, SnapshotGetError};

use crate::{
    thing::{object::Object, relation::Relation},
    type_::{
        annotation::AnnotationCardinality, attribute_type::AttributeType, object_type::ObjectType, role_type::RoleType,
        type_manager::validation::SchemaValidationError,
    },
};
use crate::type_::type_manager::validation::operation_time_validation::OperationTimeValidation;

#[derive(Debug)]
pub struct ConceptError {
    pub kind: ConceptErrorKind,
}

#[derive(Debug)]
pub enum ConceptErrorKind {
    AttributeValueTypeMismatch { attribute_type_value_type: Option<ValueType>, provided_value_type: ValueType },
}

impl fmt::Display for ConceptError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for ConceptError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            ConceptErrorKind::AttributeValueTypeMismatch { .. } => None,
        }
    }
}

#[derive(Debug)]
pub enum ConceptWriteError {
    RootModification,
    SnapshotGet {
        source: SnapshotGetError,
    },
    SnapshotIterate {
        source: Arc<SnapshotIteratorError>,
    },
    ConceptRead {
        source: ConceptReadError,
    },
    SchemaValidation {
        source: SchemaValidationError,
    },
    Encoding {
        source: EncodingError,
    },
    ValueTypeMismatch {
        expected: Option<ValueType>,
        provided: ValueType,
    },
    RelationRoleCardinality {
        relation: Relation<'static>,
        role_type: RoleType<'static>,
        cardinality: AnnotationCardinality,
        actual_cardinality: u64,
    },
    StringAttributeRegex {
        regex: String,
        value: String,
    },

    MultipleKeys {
        owner: Object<'static>,
        key_type: AttributeType<'static>,
    },
    KeyMissing {
        owner: Object<'static>,
        key_type: AttributeType<'static>,
    },
    KeyTaken {
        owner: Object<'static>,
        key_type: AttributeType<'static>,
        value: Value<'static>,
        owner_type: ObjectType<'static>,
    },

    SetHasOnDeleted {
        owner: Object<'static>,
    },
    AddPlayerOnDeleted {
        relation: Relation<'static>,
    },

    CardinalityViolation {
        owner: Object<'static>,
        attribute_type: AttributeType<'static>,
        cardinality: AnnotationCardinality,
    },

    SetHasOrderedOwnsUnordered {},
    SetHasUnorderedOwnsOrdered {},

    Operation { source: SchemaValidationError }, // TODO: Find a better place for it... It is used for annotations now
}

impl fmt::Display for ConceptWriteError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for ConceptWriteError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::SnapshotGet { source, .. } => Some(source),
            Self::SnapshotIterate { source, .. } => Some(source),
            Self::ConceptRead { source } => Some(source),
            Self::Encoding { source, .. } => Some(source),
            Self::SchemaValidation { source, .. } => Some(source),
            Self::ValueTypeMismatch { .. } => None,
            Self::RelationRoleCardinality { .. } => None,
            Self::RootModification { .. } => None,
            Self::StringAttributeRegex { .. } => None,
            Self::KeyMissing { .. } => None,
            Self::KeyTaken { .. } => None,
            Self::SetHasOnDeleted { .. } => None,
            Self::MultipleKeys { .. } => None,
            Self::AddPlayerOnDeleted { .. } => None,
            Self::CardinalityViolation { .. } => None,
            Self::SetHasOrderedOwnsUnordered { .. } => None,
            Self::SetHasUnorderedOwnsOrdered { .. } => None,
            Self::Operation { .. } => None,
        }
    }
}

impl From<ConceptReadError> for ConceptWriteError {
    fn from(error: ConceptReadError) -> Self {
        match error {
            ConceptReadError::SnapshotGet { source } => Self::SnapshotGet { source },
            ConceptReadError::SnapshotIterate { source } => Self::SnapshotIterate { source },
            ConceptReadError::Encoding { source, .. } => Self::Encoding { source },
        }
    }
}

#[derive(Debug, Clone)]
pub enum ConceptReadError {
    SnapshotGet { source: SnapshotGetError },
    SnapshotIterate { source: Arc<SnapshotIteratorError> },
    Encoding { source: EncodingError },
}

impl fmt::Display for ConceptReadError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for ConceptReadError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::SnapshotGet { source, .. } => Some(source),
            Self::SnapshotIterate { source, .. } => Some(source),
            ConceptReadError::Encoding { source, .. } => Some(source),
        }
    }
}
