/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{ops::Range, sync::Arc};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use lending_iterator::LendingIterator;
use primitive::either::Either;
use resource::constants::snapshot::BUFFER_KEY_INLINE;
use storage::{
    key_range::KeyRange,
    key_value::{StorageKey, StorageKeyReference},
    keyspace::KeyspaceSet,
    snapshot::{iterator::SnapshotIteratorError, ReadableSnapshot},
};

use crate::{
    graph::{type_::vertex::TypeID, Typed},
    layout::prefix::{Prefix, PrefixID},
    value::{
        boolean_bytes::BooleanBytes,
        date_time_bytes::DateTimeBytes,
        date_time_tz_bytes::DateTimeTZBytes,
        double_bytes::DoubleBytes,
        duration_bytes::DurationBytes,
        fixed_point_bytes::FixedPointBytes,
        long_bytes::LongBytes,
        string_bytes::StringBytes,
        value_type::{ValueType, ValueTypeCategory},
        ValueEncodable,
    },
    AsBytes, EncodingKeyspace, Keyable, Prefixed,
};

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct AttributeVertex<'a> {
    bytes: Bytes<'a, BUFFER_KEY_INLINE>,
}

impl<'a> AttributeVertex<'a> {
    const KEYSPACE: EncodingKeyspace = EncodingKeyspace::Data;

    pub(crate) const LENGTH_PREFIX_PREFIX: usize = PrefixID::LENGTH;
    pub(crate) const LENGTH_PREFIX_TYPE: usize = PrefixID::LENGTH + TypeID::LENGTH;

    pub fn new(bytes: Bytes<'a, BUFFER_KEY_INLINE>) -> Self {
        debug_assert!(bytes.length() > Self::LENGTH_PREFIX_TYPE);
        AttributeVertex { bytes }
    }

    pub fn build(value_type_category: ValueTypeCategory, type_id: TypeID, attribute_id: AttributeID) -> Self {
        let mut bytes = ByteArray::zeros(Self::LENGTH_PREFIX_TYPE + attribute_id.length());
        bytes.bytes_mut()[Self::RANGE_PREFIX]
            .copy_from_slice(&Self::value_type_category_to_prefix_type(value_type_category).prefix_id().bytes());
        bytes.bytes_mut()[Self::RANGE_TYPE_ID].copy_from_slice(&type_id.bytes());
        bytes.bytes_mut()[Self::range_for_attribute_id(attribute_id.length())].copy_from_slice(attribute_id.bytes());
        Self { bytes: Bytes::Array(bytes) }
    }

    pub(crate) fn build_prefix_type_attribute_id(
        value_type_category: ValueTypeCategory,
        type_id: TypeID,
        attribute_id_part: &[u8],
    ) -> StorageKey<'static, BUFFER_KEY_INLINE> {
        let mut bytes = ByteArray::zeros(Self::LENGTH_PREFIX_TYPE + attribute_id_part.len());
        bytes.bytes_mut()[Self::RANGE_PREFIX]
            .copy_from_slice(&Self::value_type_category_to_prefix_type(value_type_category).prefix_id().bytes());
        bytes.bytes_mut()[Self::RANGE_TYPE_ID].copy_from_slice(&type_id.bytes());
        bytes.bytes_mut()[Self::range_for_attribute_id(attribute_id_part.len())].copy_from_slice(attribute_id_part);
        StorageKey::new_owned(Self::KEYSPACE, bytes)
    }

    pub fn build_prefix_type(
        prefix: Prefix,
        type_id: TypeID,
    ) -> StorageKey<'static, { AttributeVertex::LENGTH_PREFIX_TYPE }> {
        let mut bytes = ByteArray::zeros(Self::LENGTH_PREFIX_TYPE);
        bytes.bytes_mut()[Self::RANGE_PREFIX].copy_from_slice(&prefix.prefix_id().bytes());
        bytes.bytes_mut()[Self::RANGE_TYPE_ID].copy_from_slice(&type_id.bytes());
        StorageKey::new_owned(Self::KEYSPACE, bytes)
    }

    pub fn is_attribute_vertex(storage_key: StorageKeyReference<'_>) -> bool {
        storage_key.keyspace_id() == Self::KEYSPACE.id()
            && !storage_key.bytes().is_empty()
            && (Prefix::ATTRIBUTE_MIN.prefix_id().bytes()[..] <= storage_key.bytes()[Self::RANGE_PREFIX]
                && storage_key.bytes()[Self::RANGE_PREFIX] <= Prefix::ATTRIBUTE_MAX.prefix_id().bytes()[..])
    }

    pub fn value_type_category_to_prefix_type(value_type_category: ValueTypeCategory) -> Prefix {
        match value_type_category {
            ValueTypeCategory::Boolean => Prefix::VertexAttributeBoolean,
            ValueTypeCategory::Long => Prefix::VertexAttributeLong,
            ValueTypeCategory::Double => Prefix::VertexAttributeDouble,
            ValueTypeCategory::FixedPoint => Prefix::VertexAttributeFixedPoint,
            ValueTypeCategory::DateTime => Prefix::VertexAttributeDateTime,
            ValueTypeCategory::DateTimeTZ => Prefix::VertexAttributeDateTimeTZ,
            ValueTypeCategory::Duration => Prefix::VertexAttributeDuration,
            ValueTypeCategory::String => Prefix::VertexAttributeString,
            ValueTypeCategory::Struct => Prefix::VertexAttributeStruct,
        }
    }

    pub fn prefix_type_to_value_id_encoding_length(prefix: Prefix) -> usize {
        match prefix {
            Prefix::VertexAttributeBoolean => BooleanAttributeID::LENGTH,
            Prefix::VertexAttributeLong => LongAttributeID::LENGTH,
            Prefix::VertexAttributeDouble => DoubleAttributeID::LENGTH,
            Prefix::VertexAttributeFixedPoint => FixedPointAttributeID::LENGTH,
            Prefix::VertexAttributeDateTime => DateTimeAttributeID::LENGTH,
            Prefix::VertexAttributeDateTimeTZ => DateTimeTZAttributeID::LENGTH,
            Prefix::VertexAttributeDuration => DurationAttributeID::LENGTH,
            Prefix::VertexAttributeString => StringAttributeID::LENGTH,
            Prefix::VertexAttributeStruct => StructAttributeID::LENGTH,
            _ => unreachable!("Unrecognised attribute vertex prefix type"),
        }
    }

    pub fn build_prefix_prefix(prefix: Prefix) -> StorageKey<'static, { AttributeVertex::LENGTH_PREFIX_PREFIX }> {
        let mut array = ByteArray::zeros(Self::LENGTH_PREFIX_PREFIX);
        array.bytes_mut()[Self::RANGE_PREFIX].copy_from_slice(&prefix.prefix_id().bytes());
        StorageKey::new(Self::KEYSPACE, Bytes::Array(array))
    }

    pub fn value_type_category(&self) -> ValueTypeCategory {
        match self.prefix() {
            Prefix::VertexAttributeBoolean => ValueTypeCategory::Boolean,
            Prefix::VertexAttributeLong => ValueTypeCategory::Long,
            Prefix::VertexAttributeDouble => ValueTypeCategory::Double,
            Prefix::VertexAttributeFixedPoint => ValueTypeCategory::FixedPoint,
            Prefix::VertexAttributeDateTime => ValueTypeCategory::DateTime,
            Prefix::VertexAttributeDateTimeTZ => ValueTypeCategory::DateTimeTZ,
            Prefix::VertexAttributeDuration => ValueTypeCategory::Duration,
            Prefix::VertexAttributeString => ValueTypeCategory::String,
            Prefix::VertexAttributeStruct => ValueTypeCategory::Struct,
            _ => unreachable!("Unexpected prefix."),
        }
    }

    pub fn attribute_id(&self) -> AttributeID {
        AttributeID::new(self.value_type_category(), &self.bytes.bytes()[self.range_of_attribute_id()])
    }

    fn range_of_attribute_id(&self) -> Range<usize> {
        Self::RANGE_TYPE_ID.end..self.length()
    }

    fn range_for_attribute_id(id_length: usize) -> Range<usize> {
        Self::RANGE_TYPE_ID.end..Self::RANGE_TYPE_ID.end + id_length
    }

    pub(crate) fn length(&self) -> usize {
        self.bytes.length()
    }

    pub fn as_reference<'this: 'a>(&'this self) -> AttributeVertex<'this> {
        Self::new(Bytes::Reference(self.bytes.as_reference()))
    }

    pub fn into_owned(self) -> AttributeVertex<'static> {
        AttributeVertex { bytes: self.bytes.into_owned() }
    }
}

impl<'a> AsBytes<'a, BUFFER_KEY_INLINE> for AttributeVertex<'a> {
    fn bytes(&'a self) -> ByteReference<'a> {
        self.bytes.as_reference()
    }

    fn into_bytes(self) -> Bytes<'a, BUFFER_KEY_INLINE> {
        self.bytes
    }
}

impl<'a> Prefixed<'a, BUFFER_KEY_INLINE> for AttributeVertex<'a> {}

impl<'a> Typed<'a, BUFFER_KEY_INLINE> for AttributeVertex<'a> {}

impl<'a> Keyable<'a, BUFFER_KEY_INLINE> for AttributeVertex<'a> {
    fn keyspace(&self) -> EncodingKeyspace {
        EncodingKeyspace::Data
    }
}

pub(crate) enum AttributeIDLength {
    Short,
    Long,
}

impl AttributeIDLength {
    const SHORT_LENGTH: usize = 8;
    const LONG_LENGTH: usize = 17;

    pub(crate) const fn length(&self) -> usize {
        match self {
            AttributeIDLength::Short => Self::SHORT_LENGTH,
            AttributeIDLength::Long => Self::LONG_LENGTH,
        }
    }

    const fn max_length() -> usize {
        // TODO: this is brittle - ideally we'd compute this over the max of the enum variants
        Self::LONG_LENGTH
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AttributeID {
    Boolean(BooleanAttributeID),
    Long(LongAttributeID),
    Double(DoubleAttributeID),
    FixedPoint(FixedPointAttributeID),
    DateTime(DateTimeAttributeID),
    DateTimeTZ(DateTimeTZAttributeID),
    Duration(DurationAttributeID),
    String(StringAttributeID),
    Struct(StructAttributeID),
}

impl AttributeID {
    pub fn new(value_type_category: ValueTypeCategory, bytes: &[u8]) -> Self {
        match value_type_category {
            ValueTypeCategory::Boolean => Self::Boolean(BooleanAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::Long => Self::Long(LongAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::Double => Self::Double(DoubleAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::FixedPoint => Self::FixedPoint(FixedPointAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::DateTime => Self::DateTime(DateTimeAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::DateTimeTZ => Self::DateTimeTZ(DateTimeTZAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::Duration => Self::Duration(DurationAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::String => Self::String(StringAttributeID::new(bytes.try_into().unwrap())),
            ValueTypeCategory::Struct => Self::Struct(StructAttributeID::new(bytes.try_into().unwrap())),
        }
    }

    pub fn build_inline(value: impl ValueEncodable) -> Self {
        debug_assert!(Self::is_inlineable(value.clone()));
        match value.value_type() {
            ValueType::Boolean => Self::Boolean(BooleanAttributeID::build(value.encode_boolean())),
            ValueType::Long => Self::Long(LongAttributeID::build(value.encode_long())),
            ValueType::Double => Self::Double(DoubleAttributeID::build(value.encode_double())),
            ValueType::FixedPoint => Self::FixedPoint(FixedPointAttributeID::build(value.encode_fixed_point())),
            ValueType::DateTime => Self::DateTime(DateTimeAttributeID::build(value.encode_date_time())),
            ValueType::DateTimeTZ => Self::DateTimeTZ(DateTimeTZAttributeID::build(value.encode_date_time_tz())),
            ValueType::Duration => Self::Duration(DurationAttributeID::build(value.encode_duration())),
            ValueType::String => Self::String(StringAttributeID::build_inline_id(value.encode_string::<256>())),
            ValueType::Struct(_) => {
                todo!()
            }
        }
    }

    pub fn value_type_encoding_length(value_type_category: ValueTypeCategory) -> usize {
        match value_type_category {
            ValueTypeCategory::Boolean => BooleanAttributeID::LENGTH,
            ValueTypeCategory::Long => LongAttributeID::LENGTH,
            ValueTypeCategory::Double => DoubleAttributeID::LENGTH,
            ValueTypeCategory::FixedPoint => FixedPointAttributeID::LENGTH,
            ValueTypeCategory::DateTime => DateTimeAttributeID::LENGTH,
            ValueTypeCategory::DateTimeTZ => DateTimeTZAttributeID::LENGTH,
            ValueTypeCategory::Duration => DurationAttributeID::LENGTH,
            ValueTypeCategory::String => StringAttributeID::LENGTH,
            ValueTypeCategory::Struct => StructAttributeID::LENGTH,
        }
    }

    ///
    /// Return true if values in the value type are always fully encoded in the ID
    /// Return false if the values are hashed or incomplete and may require a secondary lookup
    ///
    pub fn is_inlineable(value: impl ValueEncodable) -> bool {
        match value.value_type() {
            ValueType::Boolean => BooleanAttributeID::is_inlineable(),
            ValueType::Long => LongAttributeID::is_inlineable(),
            ValueType::Double => DoubleAttributeID::is_inlineable(),
            ValueType::FixedPoint => FixedPointAttributeID::is_inlineable(),
            ValueType::DateTime => DateTimeAttributeID::is_inlineable(),
            ValueType::DateTimeTZ => DateTimeTZAttributeID::is_inlineable(),
            ValueType::Duration => DurationAttributeID::is_inlineable(),
            ValueType::String => StringAttributeID::is_inlineable(value.encode_string::<256>()),
            ValueType::Struct(definition_key) => {
                todo!()
                // StructAttributeID::is_inlineable()
            }
        }
    }

    pub fn bytes(&self) -> &[u8] {
        match self {
            AttributeID::Boolean(boolean_id) => boolean_id.bytes_ref(),
            AttributeID::Long(long_id) => long_id.bytes_ref(),
            AttributeID::Double(double_id) => double_id.bytes_ref(),
            AttributeID::FixedPoint(fixed_point_id) => fixed_point_id.bytes_ref(),
            AttributeID::DateTime(date_time_id) => date_time_id.bytes_ref(),
            AttributeID::DateTimeTZ(date_time_tz_id) => date_time_tz_id.bytes_ref(),
            AttributeID::Duration(duration_id) => duration_id.bytes_ref(),
            AttributeID::String(string_id) => string_id.bytes_ref(),
            AttributeID::Struct(struct_id) => struct_id.bytes_ref(),
        }
    }

    pub(crate) const fn length(&self) -> usize {
        match self {
            AttributeID::Boolean(_) => BooleanAttributeID::LENGTH,
            AttributeID::Long(_) => LongAttributeID::LENGTH,
            AttributeID::Double(_) => DoubleAttributeID::LENGTH,
            AttributeID::FixedPoint(_) => FixedPointAttributeID::LENGTH,
            AttributeID::DateTime(_) => DateTimeAttributeID::LENGTH,
            AttributeID::DateTimeTZ(_) => DateTimeTZAttributeID::LENGTH,
            AttributeID::Duration(_) => DurationAttributeID::LENGTH,
            AttributeID::String(_) => StringAttributeID::LENGTH,
            AttributeID::Struct(_) => StructAttributeID::LENGTH,
        }
    }

    pub(crate) const fn max_length() -> usize {
        AttributeIDLength::max_length()
    }

    pub fn unwrap_boolean(self) -> BooleanAttributeID {
        match self {
            AttributeID::Boolean(boolean_id) => boolean_id,
            _ => panic!("Cannot unwrap Boolean ID from non-boolean attribute ID."),
        }
    }

    pub fn unwrap_long(self) -> LongAttributeID {
        match self {
            AttributeID::Long(long_id) => long_id,
            _ => panic!("Cannot unwrap Long ID from non-long attribute ID."),
        }
    }

    pub fn unwrap_double(self) -> DoubleAttributeID {
        match self {
            AttributeID::Double(double_id) => double_id,
            _ => panic!("Cannot unwrap Double ID from non-double attribute ID."),
        }
    }

    pub fn unwrap_fixed_point(self) -> FixedPointAttributeID {
        match self {
            AttributeID::FixedPoint(fixed_point_id) => fixed_point_id,
            _ => panic!("Cannot unwrap FixedPoint ID from non-fixed_point attribute ID."),
        }
    }

    pub fn unwrap_date_time(self) -> DateTimeAttributeID {
        match self {
            AttributeID::DateTime(date_time_id) => date_time_id,
            _ => panic!("Cannot unwrap DateTime ID from non-datetime attribute ID."),
        }
    }

    pub fn unwrap_date_time_tz(self) -> DateTimeTZAttributeID {
        match self {
            AttributeID::DateTimeTZ(date_time_tz_id) => date_time_tz_id,
            _ => panic!("Cannot unwrap DateTime ID from non-datetime attribute ID."),
        }
    }

    pub fn unwrap_duration(self) -> DurationAttributeID {
        match self {
            AttributeID::Duration(duration_id) => duration_id,
            _ => panic!("Cannot unwrap Duration ID from non-duration attribute ID."),
        }
    }

    pub fn unwrap_string(self) -> StringAttributeID {
        match self {
            AttributeID::String(string_id) => string_id,
            _ => panic!("Cannot unwrap String ID from non-long attribute ID."),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BooleanAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl BooleanAttributeID {
    const LENGTH: usize = AttributeIDLength::SHORT_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn build(value: BooleanBytes) -> Self {
        Self { bytes: value.bytes() }
    }

    pub(crate) const fn is_inlineable() -> bool {
        true
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

// TODO: this is just a really thin wrapper around value::Long -- perhaps we can merge them?
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct LongAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl LongAttributeID {
    const LENGTH: usize = AttributeIDLength::SHORT_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn build(value: LongBytes) -> Self {
        Self { bytes: value.bytes() }
    }

    pub(crate) const fn is_inlineable() -> bool {
        true
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct DoubleAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl DoubleAttributeID {
    const LENGTH: usize = AttributeIDLength::SHORT_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn build(value: DoubleBytes) -> Self {
        Self { bytes: value.bytes() }
    }

    pub(crate) const fn is_inlineable() -> bool {
        true
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct FixedPointAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl FixedPointAttributeID {
    const LENGTH: usize = AttributeIDLength::LONG_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn build(value: FixedPointBytes) -> Self {
        Self { bytes: value.bytes() }
    }

    pub(crate) const fn is_inlineable() -> bool {
        true
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct DateTimeAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl DateTimeAttributeID {
    const LENGTH: usize = AttributeIDLength::LONG_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn build(value: DateTimeBytes) -> Self {
        Self { bytes: value.bytes() }
    }

    pub(crate) const fn is_inlineable() -> bool {
        true
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct DateTimeTZAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl DateTimeTZAttributeID {
    const LENGTH: usize = AttributeIDLength::LONG_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn build(value: DateTimeTZBytes) -> Self {
        Self { bytes: value.bytes() }
    }

    pub(crate) const fn is_inlineable() -> bool {
        true
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct DurationAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl DurationAttributeID {
    const LENGTH: usize = AttributeIDLength::LONG_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn build(value: DurationBytes) -> Self {
        Self { bytes: value.bytes() }
    }

    pub(crate) const fn is_inlineable() -> bool {
        true
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

///
/// String encoding scheme uses 17 bytes:
///
///   Case 1: string fits in 16 bytes
///     [16: string][1: 0b0[length]]
///
///   Case 2: string does not fit in 16 bytes:
///     [8: prefix][8: hash][1: 0b1[disambiguator]]
///
///  4 byte hash: collision probability of 50% at 77k elements
///  5 byte hash: collision probability of 50% at 1.25m elements
///  6 byte hash: collision probability of 50% at 20m elements
///  7 byte hash: collision probability of 50% at 320m elements
///  8 byte hash: collision probability of 50% at 5b elements
///
///  With an 8 byte prefix and 7 byte hash we can insert up to 100 million elements behind the same prefix
///  before we have a 5% chance of collision. With 100 million entries with 100 bytes each, we can store 20GB of data in the same prefix.
///  We also allow disambiguation in the tail byte of the ID, so we can tolerate up to 127 collsions, or approximately 2TB of data with above assumptions.
///
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct StringAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl StringAttributeID {
    const LENGTH: usize = AttributeIDLength::LONG_LENGTH;

    pub(crate) const ENCODING_INLINE_CAPACITY: usize = Self::LENGTH - 1;
    const ENCODING_STRING_PREFIX_LENGTH: usize = 8;
    pub const ENCODING_STRING_PREFIX_RANGE: Range<usize> = 0..Self::ENCODING_STRING_PREFIX_LENGTH;
    pub const ENCODING_STRING_HASH_LENGTH: usize = 8;
    const ENCODING_STRING_HASH_RANGE: Range<usize> = Self::ENCODING_STRING_PREFIX_RANGE.end
        ..Self::ENCODING_STRING_PREFIX_RANGE.end + Self::ENCODING_STRING_HASH_LENGTH;
    const ENCODING_STRING_PREFIX_HASH_LENGTH: usize =
        Self::ENCODING_STRING_PREFIX_LENGTH + Self::ENCODING_STRING_HASH_LENGTH;
    const ENCODING_STRING_PREFIX_HASH_RANGE: Range<usize> = Self::ENCODING_STRING_PREFIX_RANGE.start
        ..Self::ENCODING_STRING_PREFIX_RANGE.start + Self::ENCODING_STRING_PREFIX_HASH_LENGTH;

    const ENCODING_STRING_TAIL_BYTE_INDEX: usize = Self::ENCODING_STRING_HASH_RANGE.end;
    const ENCODING_STRING_TAIL_MASK: u8 = 0b10000000;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn is_inlineable<const INLINE_LENGTH: usize>(string: StringBytes<'_, INLINE_LENGTH>) -> bool {
        string.length() <= Self::ENCODING_INLINE_CAPACITY
    }

    pub(crate) fn build_inline_id<const INLINE_LENGTH: usize>(string: StringBytes<'_, INLINE_LENGTH>) -> Self {
        debug_assert!(Self::is_inlineable(string.as_reference()));
        let mut bytes = [0u8; Self::LENGTH];
        bytes[0..string.length()].copy_from_slice(string.bytes().bytes());
        Self::set_tail_inline_length(&mut bytes, string.length() as u8);
        Self::new(bytes)
    }

    ///
    /// Encode the last byte by setting 0b0[7 bits representing length of the prefix characters]
    ///
    fn set_tail_inline_length(bytes: &mut [u8; Self::LENGTH], length: u8) {
        assert!(length & Self::ENCODING_STRING_TAIL_MASK == 0); // ie < 128, high bit not set
                                                                // because the high bit is not set, we already conform to the required mask of high bit = 0
        bytes[Self::ENCODING_STRING_TAIL_BYTE_INDEX] = length;
    }

    ///
    /// Build a hashed string ID, including picking the tail disambiguator bits.
    /// If a matching existing String with ID is found, return it.
    /// Otherwise, create an ID using the next available tail ID.
    ///
    pub(crate) fn build_hashed_id<const INLINE_LENGTH: usize, Snapshot>(
        type_id: TypeID,
        string: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &Snapshot,
        hasher: &impl Fn(&[u8]) -> u64,
    ) -> Result<Self, Arc<SnapshotIteratorError>>
    where
        Snapshot: ReadableSnapshot,
    {
        debug_assert!(!Self::is_inlineable(string.as_reference()));
        let mut id_bytes = Self::build_hashed_id_without_tail(string.as_reference(), hasher);
        let existing_or_tail = Self::find_hashed_id_or_next_tail(type_id, string, id_bytes, snapshot)?;
        match existing_or_tail {
            Either::First(existing) => Ok(existing),
            Either::Second(tail) => {
                if tail & Self::ENCODING_STRING_TAIL_MASK != 0 {
                    // over 127
                    // TODO: should we panic?
                    panic!("String encoding space has no space remaining within the prefix and hash prefix.")
                }
                Self::set_tail_hash_disambiguator(&mut id_bytes, tail);
                Ok(Self::new(id_bytes))
            }
        }
    }

    pub(crate) fn find_hashed_id<const INLINE_LENGTH: usize, Snapshot>(
        type_id: TypeID,
        string: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &Snapshot,
        hasher: &impl Fn(&[u8]) -> u64,
    ) -> Result<Option<Self>, Arc<SnapshotIteratorError>>
    where
        Snapshot: ReadableSnapshot,
    {
        debug_assert!(!Self::is_inlineable(string.as_reference()));
        let existing_or_tail = Self::find_hashed_id_or_next_tail(
            type_id,
            string.as_reference(),
            Self::build_hashed_id_without_tail(string.as_reference(), hasher),
            snapshot,
        )?;
        match existing_or_tail {
            Either::First(existing) => Ok(Some(existing)),
            Either::Second(_) => Ok(None),
        }
    }

    fn build_hashed_id_without_tail<const INLINE_LENGTH: usize>(
        string: StringBytes<'_, INLINE_LENGTH>,
        hasher: &impl Fn(&[u8]) -> u64,
    ) -> [u8; Self::LENGTH] {
        let mut bytes = [0u8; Self::LENGTH];
        bytes[Self::ENCODING_STRING_PREFIX_RANGE]
            .copy_from_slice(&string.bytes().bytes()[Self::ENCODING_STRING_PREFIX_RANGE]);
        let hash_bytes: [u8; Self::ENCODING_STRING_HASH_LENGTH] = Self::apply_hash(string, hasher);
        bytes[Self::ENCODING_STRING_HASH_RANGE].copy_from_slice(&hash_bytes);
        bytes[Self::ENCODING_STRING_TAIL_BYTE_INDEX] = Self::ENCODING_STRING_TAIL_MASK;
        bytes
    }

    fn find_hashed_id_or_next_tail<const INLINE_LENGTH: usize, Snapshot>(
        type_id: TypeID,
        string: StringBytes<'_, INLINE_LENGTH>,
        id_without_tail: [u8; Self::LENGTH],
        snapshot: &Snapshot,
    ) -> Result<Either<Self, u8>, Arc<SnapshotIteratorError>>
    where
        Snapshot: ReadableSnapshot,
    {
        debug_assert!(!Self::is_inlineable(string.as_reference()));
        let prefix_search = KeyRange::new_within(
            AttributeVertex::build_prefix_type_attribute_id(ValueTypeCategory::String, type_id, &id_without_tail),
            AttributeVertex::value_type_category_to_prefix_type(ValueTypeCategory::String).fixed_width_keys(),
        );
        let mut iter = snapshot.iterate_range(prefix_search);
        let mut next = iter.next().transpose()?;
        let mut tail: u8 = 0;
        while let Some((key, value)) = next {
            let existing_attribute_id = AttributeVertex::new(Bytes::reference(key.bytes())).attribute_id();
            let existing_string_id = Self::new(existing_attribute_id.bytes().try_into().unwrap());
            if StringBytes::new(value) == string {
                return Ok(Either::First(existing_string_id));
            } else if tail != existing_string_id.get_hash_disambiguator() {
                // found unused tail ID
                return Ok(Either::Second(tail));
            }
            tail += 1;
            next = iter.next().transpose()?;
        }
        Ok(Either::Second(tail))
    }

    fn apply_hash<const INLINE_LENGTH: usize>(
        string: StringBytes<'_, INLINE_LENGTH>,
        hasher: &impl Fn(&[u8]) -> u64,
    ) -> [u8; Self::ENCODING_STRING_HASH_LENGTH] {
        hasher(string.bytes().bytes()).to_be_bytes()
    }

    ///
    /// Encode the last byte by setting 0b1[7 bits representing disambiguator]
    ///
    fn set_tail_hash_disambiguator(bytes: &mut [u8; Self::LENGTH], disambiguator: u8) {
        debug_assert!(disambiguator & Self::ENCODING_STRING_TAIL_MASK == 0); // ie. disambiguator < 128, not using high bit
                                                                             // sets 0x1[disambiguator]
        bytes[Self::ENCODING_STRING_TAIL_BYTE_INDEX] = disambiguator | Self::ENCODING_STRING_TAIL_MASK;
    }

    pub fn is_inline(&self) -> bool {
        self.bytes[Self::ENCODING_STRING_TAIL_BYTE_INDEX] & Self::ENCODING_STRING_TAIL_MASK == 0
    }

    pub fn get_inline_string_bytes(&self) -> StringBytes<'static, 16> {
        debug_assert!(self.is_inline());
        let mut bytes = ByteArray::zeros(Self::LENGTH);
        let inline_string_length = self.get_inline_length();
        bytes.bytes_mut()[0..inline_string_length as usize]
            .copy_from_slice(&self.bytes[0..inline_string_length as usize]);
        bytes.truncate(inline_string_length as usize);
        StringBytes::new(Bytes::Array(bytes))
    }

    pub fn get_inline_length(&self) -> u8 {
        debug_assert!(self.is_inline());
        self.bytes[Self::ENCODING_STRING_TAIL_BYTE_INDEX]
    }

    pub fn get_hash_prefix(&self) -> [u8; Self::ENCODING_STRING_PREFIX_LENGTH] {
        debug_assert!(!self.is_inline());
        (&self.bytes[Self::ENCODING_STRING_PREFIX_RANGE]).try_into().unwrap()
    }

    pub fn get_hash_hash(&self) -> [u8; Self::ENCODING_STRING_HASH_LENGTH] {
        debug_assert!(!self.is_inline());
        (&self.bytes[Self::ENCODING_STRING_HASH_RANGE]).try_into().unwrap()
    }

    pub fn get_hash_prefix_hash(&self) -> [u8; Self::ENCODING_STRING_PREFIX_HASH_LENGTH] {
        debug_assert!(!self.is_inline());
        (&self.bytes[Self::ENCODING_STRING_PREFIX_HASH_RANGE]).try_into().unwrap()
    }

    pub fn get_hash_disambiguator(&self) -> u8 {
        debug_assert!(!self.is_inline());
        let byte = self.bytes[Self::ENCODING_STRING_TAIL_BYTE_INDEX];
        byte & !Self::ENCODING_STRING_TAIL_MASK // unsets 0x1___ high bit
    }

    pub fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }

    pub fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct StructAttributeID {
    bytes: [u8; Self::LENGTH],
}

impl StructAttributeID {
    const LENGTH: usize = AttributeIDLength::LONG_LENGTH;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub(crate) fn bytes_ref(&self) -> &[u8] {
        &self.bytes
    }
}