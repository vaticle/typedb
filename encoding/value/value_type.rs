/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{fmt, ops::Range};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use resource::constants::snapshot::BUFFER_VALUE_INLINE;
use serde::{
    de,
    de::{Error, Unexpected, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{
    graph::{definition::definition_key::DefinitionKey, type_::property::TypeVertexPropertyEncoding},
    layout::infix::Infix,
    AsBytes,
};

// We can support Prefix::ATTRIBUTE_MAX - Prefix::ATTRIBUTE_MIN different built-in value types
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ValueType {
    Boolean,
    Long,
    Double,
    Decimal,

    DateTime,
    DateTimeTZ,
    Duration,

    String,

    Struct(DefinitionKey<'static>),
}

impl ValueType {
    pub fn category(&self) -> ValueTypeCategory {
        match self {
            ValueType::Boolean => ValueTypeCategory::Boolean,
            ValueType::Long => ValueTypeCategory::Long,
            ValueType::Double => ValueTypeCategory::Double,
            ValueType::Decimal => ValueTypeCategory::Decimal,
            ValueType::DateTime => ValueTypeCategory::DateTime,
            ValueType::DateTimeTZ => ValueTypeCategory::DateTimeTZ,
            ValueType::Duration => ValueTypeCategory::Duration,
            ValueType::String => ValueTypeCategory::String,
            ValueType::Struct(_) => ValueTypeCategory::Struct,
        }
    }

    fn from_category_and_tail(category: ValueTypeCategory, tail: [u8; ValueTypeBytes::TAIL_LENGTH]) -> Self {
        match category {
            ValueTypeCategory::Boolean => Self::Boolean,
            ValueTypeCategory::Long => Self::Long,
            ValueTypeCategory::Double => Self::Double,
            ValueTypeCategory::Decimal => Self::Decimal,
            ValueTypeCategory::DateTime => Self::DateTime,
            ValueTypeCategory::DateTimeTZ => Self::DateTimeTZ,
            ValueTypeCategory::Duration => Self::Duration,
            ValueTypeCategory::String => Self::String,
            ValueTypeCategory::Struct => {
                let definition_key = DefinitionKey::new(Bytes::Array(ByteArray::copy(&tail)));
                Self::Struct(definition_key)
            }
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ValueTypeCategory {
    Boolean,
    Long,
    Double,
    Decimal,
    DateTime,
    DateTimeTZ,
    Duration,
    String,
    Struct,
}

impl ValueTypeCategory {
    pub(crate) fn to_bytes(&self) -> [u8; ValueTypeBytes::CATEGORY_LENGTH] {
        match self {
            Self::Boolean => [0],
            Self::Long => [1],
            Self::Double => [2],
            Self::Decimal => [3],
            Self::DateTime => [4],
            Self::DateTimeTZ => [5],
            Self::Duration => [6],
            Self::String => [7],
            Self::Struct => [40],
        }
    }

    pub(crate) fn from_bytes(bytes: [u8; ValueTypeBytes::CATEGORY_LENGTH]) -> Self {
        let category = match bytes {
            [0] => ValueTypeCategory::Boolean,
            [1] => ValueTypeCategory::Long,
            [2] => ValueTypeCategory::Double,
            [3] => ValueTypeCategory::Decimal,
            [4] => ValueTypeCategory::DateTime,
            [5] => ValueTypeCategory::DateTimeTZ,
            [6] => ValueTypeCategory::Duration,
            [7] => ValueTypeCategory::String,
            [40] => ValueTypeCategory::Struct,
            _ => panic!("Unrecognised value type category byte: {:?}", bytes),
        };
        debug_assert_eq!(bytes, category.to_bytes());
        category
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ValueTypeBytes {
    bytes: [u8; Self::LENGTH],
}

impl ValueTypeBytes {
    const CATEGORY_LENGTH: usize = 1;
    const TAIL_LENGTH: usize = DefinitionKey::LENGTH;
    const LENGTH: usize = Self::CATEGORY_LENGTH + Self::TAIL_LENGTH;
    const RANGE_CATEGORY: Range<usize> = 0..Self::CATEGORY_LENGTH;
    const RANGE_TAIL: Range<usize> = Self::RANGE_CATEGORY.end..Self::RANGE_CATEGORY.end + Self::TAIL_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub fn build(value_type: &ValueType) -> Self {
        let mut array = [0; Self::LENGTH];
        array[Self::RANGE_CATEGORY].copy_from_slice(&value_type.category().to_bytes());
        if let ValueType::Struct(definition_key) = value_type {
            array[Self::RANGE_TAIL].copy_from_slice(definition_key.bytes().bytes());
        }
        Self { bytes: array }
    }

    pub fn to_value_type(&self) -> ValueType {
        ValueType::from_category_and_tail(
            ValueTypeCategory::from_bytes(self.bytes[Self::RANGE_CATEGORY].try_into().unwrap()),
            self.bytes[Self::RANGE_TAIL].try_into().unwrap(),
        )
    }

    pub fn into_bytes(self) -> [u8; Self::LENGTH] {
        self.bytes
    }
}

impl Serialize for ValueType {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&ValueTypeBytes::build(self).into_bytes())
    }
}

impl TypeVertexPropertyEncoding<'static> for ValueType {
    const INFIX: Infix = Infix::PropertyValueType;

    fn from_value_bytes<'b>(value: ByteReference<'b>) -> Self {
        let mut bytes: [u8; ValueTypeBytes::LENGTH] = [0; ValueTypeBytes::LENGTH];
        bytes.copy_from_slice(&value.bytes()[0..ValueTypeBytes::LENGTH]);
        ValueTypeBytes::new(bytes).to_value_type()
    }

    fn to_value_bytes(self) -> Option<Bytes<'static, BUFFER_VALUE_INLINE>> {
        Some(Bytes::Array(ByteArray::copy(&ValueTypeBytes::build(&self).into_bytes())))
    }
}

impl<'de> Deserialize<'de> for ValueType {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueTypeVisitor;

        impl<'de> Visitor<'de> for ValueTypeVisitor {
            type Value = ValueType;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("`ValueType`")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<ValueType, E>
            where
                E: de::Error,
            {
                if v.len() == ValueTypeBytes::LENGTH {
                    Ok(ValueType::from_value_bytes(ByteReference::new(v)))
                } else {
                    Err(E::invalid_value(Unexpected::Bytes(v), &self))
                }
            }
        }
        deserializer.deserialize_bytes(ValueTypeVisitor)
    }
}
