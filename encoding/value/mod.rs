/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use bytes::{byte_array::ByteArray, byte_reference::ByteReference};
use resource::constants::snapshot::BUFFER_VALUE_INLINE;

use self::{
    boolean_bytes::BooleanBytes, date_bytes::DateBytes, date_time_bytes::DateTimeBytes,
    date_time_tz_bytes::DateTimeTZBytes, decimal_bytes::DecimalBytes, double_bytes::DoubleBytes,
    duration_bytes::DurationBytes, long_bytes::LongBytes, string_bytes::StringBytes, struct_bytes::StructBytes,
    value_type::ValueType,
};

pub mod boolean_bytes;
pub mod date_bytes;
pub mod date_time_bytes;
pub mod date_time_tz_bytes;
pub mod decimal_bytes;
pub mod decimal_value;
pub mod double_bytes;
pub mod duration_bytes;
pub mod duration_value;
pub mod label;
pub mod long_bytes;
pub mod primitive_encoding;
pub mod string_bytes;
pub mod struct_bytes;
pub mod value;
pub mod value_struct;
pub mod value_type;

pub fn decode_value_u64(bytes: ByteReference<'_>) -> u64 {
    primitive_encoding::decode_u64(bytes.bytes().try_into().unwrap())
}

pub trait ValueEncodable: Clone {
    fn value_type(&self) -> ValueType;

    fn encode_boolean(&self) -> BooleanBytes;

    fn encode_long(&self) -> LongBytes;

    fn encode_double(&self) -> DoubleBytes;

    fn encode_decimal(&self) -> DecimalBytes;

    fn encode_date(&self) -> DateBytes;

    fn encode_date_time(&self) -> DateTimeBytes;

    fn encode_date_time_tz(&self) -> DateTimeTZBytes;

    fn encode_duration(&self) -> DurationBytes;

    fn encode_string<const INLINE_LENGTH: usize>(&self) -> StringBytes<INLINE_LENGTH>;

    fn encode_struct<const INLINE_LENGTH: usize>(&self) -> StructBytes<INLINE_LENGTH>;
}
