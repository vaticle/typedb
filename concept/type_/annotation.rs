/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use encoding::{
    graph::type_::property::{TypeEdgePropertyEncoding, TypeVertexPropertyEncoding},
    layout::infix::{
        Infix,
        Infix::{
            PropertyAnnotationAbstract, PropertyAnnotationDistinct, PropertyAnnotationIndependent,
            PropertyAnnotationKey, PropertyAnnotationUnique, PropertyAnnotationCascade
        },
    },
    AsBytes,
};
use resource::constants::snapshot::BUFFER_VALUE_INLINE;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Annotation {
    Abstract(AnnotationAbstract),
    Distinct(AnnotationDistinct),
    Independent(AnnotationIndependent),
    Unique(AnnotationUnique),
    Key(AnnotationKey),
    Cardinality(AnnotationCardinality),
    Regex(AnnotationRegex),
    Cascade(AnnotationCascade),
    // TODO: Subkey
    // TODO: Values
    // TODO: Range
    // TODO: Replace
}

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationAbstract;

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationDistinct;

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationUnique;

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationKey;

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationIndependent;

#[derive(Serialize, Deserialize, Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationCardinality {
    // ##########################################################################
    // ###### WARNING: any changes here may break backwards compatibility! ######
    // ##########################################################################
    start_inclusive: u64,
    end_inclusive: Option<u64>,
}

impl AnnotationCardinality {
    pub const fn new(start_inclusive: u64, end_inclusive: Option<u64>) -> Self {
        Self { start_inclusive, end_inclusive }
    }

    pub const fn default() -> Self {
        Self::new(0, Some(1))
    }

    pub fn is_valid(&self, count: u64) -> bool {
        self.start_inclusive <= count && (self.end_inclusive.is_none() || count <= self.end_inclusive.unwrap())
    }

    pub fn start(&self) -> u64 {
        self.start_inclusive
    }

    pub fn end(&self) -> Option<u64> {
        self.end_inclusive
    }

    pub fn narrowed_correctly_by(&self, other: &Self) -> bool {
        self.start_narrowed_correctly_by(other.start())
            && self.end_narrowed_correctly_by(other.end())
    }

    fn start_narrowed_correctly_by(&self, other_start_inclusive: u64) -> bool {
        self.start_inclusive <= other_start_inclusive
    }

    fn end_narrowed_correctly_by(&self, other_end_inclusive: Option<u64>) -> bool {
        self.end_inclusive.unwrap_or(u64::MAX) >= other_end_inclusive.unwrap_or(u64::MAX)
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationRegex {
    regex: String,
}

impl AnnotationRegex {
    pub const fn new(regex: String) -> Self {
        Self { regex }
    }

    pub fn default() -> Self {
        Self::new(".*".to_owned())
    }

    pub fn regex(&self) -> &str {
        &self.regex
    }
}

impl Annotation {
    pub fn category(&self) -> AnnotationCategory {
        match self {
            Self::Abstract(_) => AnnotationCategory::Abstract,
            Self::Distinct(_) => AnnotationCategory::Distinct,
            Self::Independent(_) => AnnotationCategory::Independent,
            Self::Unique(_) => AnnotationCategory::Unique,
            Self::Key(_) => AnnotationCategory::Key,
            Self::Cardinality(_) => AnnotationCategory::Cardinality,
            Self::Regex(_) => AnnotationCategory::Regex,
            Self::Cascade(_) => AnnotationCategory::Cascade,
        }
    }
}

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AnnotationCascade;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AnnotationCategory {
    Abstract,
    Distinct,
    Independent,
    Unique,
    Key,
    Cardinality,
    Regex,
    Cascade,
    // TODO: Subkey
    // TODO: Values
    // TODO: Range
    // TODO: Replace
}

impl AnnotationCategory {
    pub fn to_default_annotation(&self) -> Annotation { // TODO: fn const for regex default
        match self {
            AnnotationCategory::Abstract => Annotation::Abstract(AnnotationAbstract),
            AnnotationCategory::Distinct => Annotation::Distinct(AnnotationDistinct),
            AnnotationCategory::Independent => Annotation::Independent(AnnotationIndependent),
            AnnotationCategory::Unique => Annotation::Unique(AnnotationUnique),
            AnnotationCategory::Key => Annotation::Key(AnnotationKey),
            AnnotationCategory::Cardinality => Annotation::Cardinality(AnnotationCardinality::default()),
            AnnotationCategory::Regex => Annotation::Regex(AnnotationRegex::default()),
            AnnotationCategory::Cascade => Annotation::Cascade(AnnotationCascade),
        }
    }
}

macro_rules! empty_type_vertex_property_encoding {
    ($property:ident, $infix:ident) => {
        impl<'a> TypeVertexPropertyEncoding<'a> for $property {
            const INFIX: Infix = $infix;

            fn from_value_bytes<'b>(value: ByteReference<'b>) -> $property {
                debug_assert!(value.bytes().is_empty());
                $property
            }

            fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
                None
            }
        }
    };
}

empty_type_vertex_property_encoding!(AnnotationAbstract, PropertyAnnotationAbstract);
empty_type_vertex_property_encoding!(AnnotationIndependent, PropertyAnnotationIndependent);
empty_type_vertex_property_encoding!(AnnotationDistinct, PropertyAnnotationDistinct);

impl<'a> TypeVertexPropertyEncoding<'a> for AnnotationCardinality {
    const INFIX: Infix = Infix::PropertyAnnotationCardinality;
    fn from_value_bytes<'b>(value: ByteReference<'b>) -> Self {
        // TODO this .unwrap() should be handled as an error
        // although it does indicate data corruption
        bincode::deserialize(value.bytes()).unwrap()
    }

    fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
        Some(Bytes::copy(bincode::serialize(&self).unwrap().as_slice()))
    }
}

impl<'a> TypeVertexPropertyEncoding<'a> for AnnotationRegex {
    const INFIX: Infix = Infix::PropertyAnnotationRegex;

    fn from_value_bytes<'b>(value: ByteReference<'b>) -> AnnotationRegex {
        // TODO this .unwrap() should be handled as an error
        // although it does indicate data corruption
        AnnotationRegex::new(std::str::from_utf8(value.bytes()).unwrap().to_owned())
    }

    fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
        Some(Bytes::Array(ByteArray::copy(self.regex().as_bytes())))
    }
}

empty_type_vertex_property_encoding!(AnnotationCascade, PropertyAnnotationCascade);

macro_rules! empty_type_edge_property_encoder {
    ($property:ident, $infix:ident) => {
        impl<'a> TypeEdgePropertyEncoding<'a> for $property {
            const INFIX: Infix = $infix;

            fn from_value_bytes<'b>(value: ByteReference<'b>) -> $property {
                debug_assert!(value.bytes().is_empty());
                $property
            }

            fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
                None
            }
        }
    };
}

empty_type_edge_property_encoder!(AnnotationDistinct, PropertyAnnotationDistinct);
empty_type_edge_property_encoder!(AnnotationKey, PropertyAnnotationKey);
empty_type_edge_property_encoder!(AnnotationUnique, PropertyAnnotationUnique);

impl<'a> TypeEdgePropertyEncoding<'a> for AnnotationCardinality {
    const INFIX: Infix = Infix::PropertyAnnotationCardinality;
    fn from_value_bytes<'b>(value: ByteReference<'b>) -> Self {
        // TODO this .unwrap() should be handled as an error
        // although it does indicate data corruption
        bincode::deserialize(value.bytes()).unwrap()
    }

    fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
        Some(Bytes::copy(bincode::serialize(&self).unwrap().as_slice()))
    }
}

impl<'a> TypeEdgePropertyEncoding<'a> for AnnotationRegex {
    const INFIX: Infix = Infix::PropertyAnnotationRegex;
    fn from_value_bytes<'b>(value: ByteReference<'b>) -> Self {
        // TODO this .unwrap() should be handled as an error
        // although it does indicate data corruption
        AnnotationRegex::new(std::str::from_utf8(value.bytes()).unwrap().to_owned())
    }

    fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
        Some(Bytes::Array(ByteArray::copy(self.regex().as_bytes())))
    }
}
