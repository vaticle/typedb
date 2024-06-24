/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{error::Error, fmt, str::Utf8Error};

use storage::snapshot::iterator::SnapshotIteratorError;

use crate::{layout::prefix::Prefix, value::value_type::ValueType};

#[derive(Debug, Clone)]
pub enum EncodingError {
    UFT8Decode { bytes: Box<[u8]>, source: Utf8Error },
    SchemaIDAllocate { source: std::sync::Arc<SnapshotIteratorError> },
    ExistingTypesRead { source: std::sync::Arc<SnapshotIteratorError> },
    TypeIDsExhausted { kind: crate::graph::type_::Kind },
    UnexpectedPrefix { expected_prefix: Prefix, actual_prefix: Prefix },
    DefinitionIDsExhausted { prefix: Prefix },
    StructDuplicateFieldDefinition { struct_name: String, field_name: String },
    StructFieldValueTypeMismatch { struct_name: String, field_name: String, expected: ValueType },
    StructMissingRequiredField { struct_name: String, field_name: String },
    StructMultipleValuesForField { struct_name: String, field_name: String }, // TODO: This is unused because the API on ThingManager accepts a HashMap, but will be needed when we're parsing structs.
    StructFieldUnresolvable { struct_name: String, field_path: Vec<String> },
    IndexingIntoNonStructField { struct_name: String, field_path: Vec<String> },
    StructPathIncomplete { struct_name: String, field_path: Vec<String> },
    StructFieldValueTooLarge(usize),
    UnexpectedEndOfEncodedStruct,
    StructAlreadyHasMaximumNumberOfFields { struct_name: String },
}

impl fmt::Display for EncodingError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for EncodingError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::UFT8Decode { source, .. } => Some(source),
            Self::SchemaIDAllocate { source, .. } => Some(source),
            Self::ExistingTypesRead { source, .. } => Some(source),
            Self::TypeIDsExhausted { .. } => None,
            Self::DefinitionIDsExhausted { .. } => None,
            Self::UnexpectedPrefix { .. } => None,
            Self::StructDuplicateFieldDefinition { .. } => None,
            Self::StructAlreadyHasMaximumNumberOfFields { .. } => None,
            Self::StructFieldValueTypeMismatch { .. } => None,
            Self::StructMissingRequiredField { .. } => None,
            Self::StructMultipleValuesForField { .. } => None,
            Self::StructFieldUnresolvable { .. } => None,
            Self::IndexingIntoNonStructField { .. } => None,
            Self::StructFieldValueTooLarge(_) => None,
            Self::UnexpectedEndOfEncodedStruct => None,
            Self::StructPathIncomplete { .. } => None,
        }
    }
}
