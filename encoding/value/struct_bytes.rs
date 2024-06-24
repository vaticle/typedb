/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    borrow::{Borrow, Cow},
    collections::HashMap,
    fmt,
};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use resource::constants::encoding::StructFieldIDUInt;

use crate::{
    error::EncodingError,
    graph::definition::{
        definition_key::{DefinitionID, DefinitionKey},
        r#struct::StructDefinition,
    },
    value::{
        boolean_bytes::BooleanBytes, date_bytes::DateBytes, date_time_bytes::DateTimeBytes,
        date_time_tz_bytes::DateTimeTZBytes, decimal_bytes::DecimalBytes, double_bytes::DoubleBytes,
        duration_bytes::DurationBytes, long_bytes::LongBytes, string_bytes::StringBytes, value::Value,
        value_struct::StructValue, value_type::ValueTypeCategory, ValueEncodable,
    },
    AsBytes,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct StructBytes<'a, const INLINE_LENGTH: usize> {
    bytes: Bytes<'a, INLINE_LENGTH>,
}

impl<'a, const INLINE_LENGTH: usize> StructBytes<'a, INLINE_LENGTH> {
    const VLE_IS_U32_FLAG: u8 = 0b1000_0000; // To check when reading
    const VLE_U32_LEN_MASK: u32 = 1 << 31; // When encoding & decoding
    const MAX_VALUE_SIZE: usize = ((Self::VLE_U32_LEN_MASK) - 1) as usize;
    const VLE_SINGLE_BYTE_MAX_SIZE: usize = { Self::VLE_IS_U32_FLAG as usize - 1 };

    pub fn new(value: Bytes<'a, INLINE_LENGTH>) -> Self {
        StructBytes { bytes: value }
    }

    pub fn build(struct_value: &StructValue<'a>) -> StructBytes<'static, INLINE_LENGTH> {
        let mut buf: Vec<u8> = Vec::new();
        encode_struct_into(struct_value, &mut buf).unwrap();
        StructBytes::new(Bytes::Array(ByteArray::boxed(buf.into_boxed_slice())))
    }

    pub fn as_struct(self) -> StructValue<'static> {
        let mut offset: usize = 0;
        decode_struct_increment_offset(&mut offset, self.bytes.bytes()).unwrap()
    }

    pub fn length(&self) -> usize {
        self.bytes.length()
    }

    pub fn as_reference(&'a self) -> StructBytes<'a, INLINE_LENGTH> {
        StructBytes { bytes: Bytes::Reference(self.bytes.as_reference()) }
    }

    pub fn into_owned(self) -> StructBytes<'static, INLINE_LENGTH> {
        StructBytes { bytes: self.bytes.into_owned() }
    }
}

impl<'a, const INLINE_LENGTH: usize> AsBytes<'a, INLINE_LENGTH> for StructBytes<'a, INLINE_LENGTH> {
    fn bytes(&'a self) -> ByteReference<'a> {
        self.bytes.as_reference()
    }

    fn into_bytes(self) -> Bytes<'a, INLINE_LENGTH> {
        self.bytes
    }
}

impl<'a, const INLINE_LENGTH: usize> fmt::Display for StructBytes<'a, INLINE_LENGTH> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bytes(len={})={:?}", self.length(), self.bytes())
    }
}

// Encode
fn encode_struct_into<'a>(struct_value: &StructValue<'a>, buf: &mut Vec<u8>) -> Result<(), EncodingError> {
    buf.extend_from_slice(&struct_value.definition_key().definition_id().bytes());
    let sorted_fields: Vec<(&StructFieldIDUInt, &Value<'a>)> = struct_value.fields().iter().collect();
    append_length_as_vle(sorted_fields.len(), buf)?;
    for (idx, value) in sorted_fields {
        buf.extend_from_slice(&idx.to_be_bytes());
        buf.extend_from_slice(&value.value_type().category().to_bytes());
        match value {
            Value::Boolean(value) => buf.extend_from_slice(&BooleanBytes::build(*value).bytes()),
            Value::Long(value) => buf.extend_from_slice(&LongBytes::build(*value).bytes()),
            Value::Double(value) => buf.extend_from_slice(&DoubleBytes::build(*value).bytes()),
            Value::Decimal(value) => buf.extend_from_slice(&DecimalBytes::build(*value).bytes()),
            Value::Date(value) => buf.extend_from_slice(&DateBytes::build(*value).bytes()),
            Value::DateTime(value) => buf.extend_from_slice(&DateTimeBytes::build(*value).bytes()),
            Value::DateTimeTZ(value) => buf.extend_from_slice(&DateTimeTZBytes::build(*value).bytes()),
            Value::Duration(value) => buf.extend_from_slice(&DurationBytes::build(*value).bytes()),
            Value::String(value) => {
                append_length_as_vle(value.len(), buf)?;
                buf.extend_from_slice(StringBytes::<0>::build_ref(value.borrow()).bytes().bytes())
            }
            Value::Struct(value) => encode_struct_into(value.borrow(), buf)?,
        }
    }
    Ok(())
}

fn append_length_as_vle(len: usize, buf: &mut Vec<u8>) -> Result<(), EncodingError> {
    if len <= StructBytes::<0>::VLE_SINGLE_BYTE_MAX_SIZE {
        debug_assert_eq!(0, (len as u8) & StructBytes::<0>::VLE_IS_U32_FLAG);
        buf.push(len as u8);
        Ok(())
    } else if len <= StructBytes::<0>::MAX_VALUE_SIZE {
        debug_assert_eq!(0, (len as u32) & StructBytes::<0>::VLE_U32_LEN_MASK);
        let be_bytes = (len as u32 | StructBytes::<0>::VLE_U32_LEN_MASK).to_be_bytes();
        buf.extend_from_slice(&be_bytes);
        Ok(())
    } else {
        Err(EncodingError::StructFieldValueTooLarge(len))
    }
}

// Decode
fn decode_struct_increment_offset(offset: &mut usize, buf: &[u8]) -> Result<StructValue<'static>, EncodingError> {
    let definition_id_u16 =
        DefinitionID::build(u16::from_be_bytes(read_bytes_increment_offset::<{ DefinitionID::LENGTH }>(offset, buf)?));
    let definition_key = DefinitionKey::build(StructDefinition::PREFIX, definition_id_u16);
    let n_fields = read_vle_increment_offset(offset, buf)?;
    let mut fields: HashMap<StructFieldIDUInt, Value<'static>> = HashMap::new();
    for _ in 0..n_fields {
        let field_idx: StructFieldIDUInt = u16::from_be_bytes(read_bytes_increment_offset::<2>(offset, buf)?);
        let value_type_category = ValueTypeCategory::from_bytes(read_bytes_increment_offset::<1>(offset, buf)?);
        let value = match value_type_category {
            ValueTypeCategory::Boolean => Value::Boolean(
                BooleanBytes::new(read_bytes_increment_offset::<{ BooleanBytes::LENGTH }>(offset, buf)?).as_bool(),
            ),
            ValueTypeCategory::Long => {
                Value::Long(LongBytes::new(read_bytes_increment_offset::<{ LongBytes::LENGTH }>(offset, buf)?).as_i64())
            }
            ValueTypeCategory::Double => Value::Double(
                DoubleBytes::new(read_bytes_increment_offset::<{ DoubleBytes::LENGTH }>(offset, buf)?).as_f64(),
            ),
            ValueTypeCategory::Decimal => Value::Decimal(
                DecimalBytes::new(read_bytes_increment_offset::<{ DecimalBytes::LENGTH }>(offset, buf)?).as_decimal(),
            ),
            ValueTypeCategory::Date => Value::Date(
                DateBytes::new(read_bytes_increment_offset::<{ DateBytes::LENGTH }>(offset, buf)?).as_naive_date(),
            ),
            ValueTypeCategory::DateTime => Value::DateTime(
                DateTimeBytes::new(read_bytes_increment_offset::<{ DateTimeBytes::LENGTH }>(offset, buf)?)
                    .as_naive_date_time(),
            ),
            ValueTypeCategory::DateTimeTZ => Value::DateTimeTZ(
                DateTimeTZBytes::new(read_bytes_increment_offset::<{ DateTimeTZBytes::LENGTH }>(offset, buf)?)
                    .as_date_time(),
            ),
            ValueTypeCategory::Duration => Value::Duration(
                DurationBytes::new(read_bytes_increment_offset::<{ DurationBytes::LENGTH }>(offset, buf)?)
                    .as_duration(),
            ),
            ValueTypeCategory::String => {
                let len: usize = read_vle_increment_offset(offset, buf)?;
                Value::String(Cow::Owned(
                    StringBytes::new(Bytes::<0>::reference(read_slice_increment_offset(offset, len, buf)?))
                        .as_str()
                        .to_owned(),
                ))
            }
            ValueTypeCategory::Struct => Value::Struct(Cow::Owned(decode_struct_increment_offset(offset, buf)?)),
        };
        fields.insert(field_idx, value);
    }
    Ok(StructValue::new(definition_key, fields))
}

fn read_vle_increment_offset(offset: &mut usize, buf: &[u8]) -> Result<usize, EncodingError> {
    let is_single_byte = buf[*offset] & StructBytes::<0>::VLE_IS_U32_FLAG == 0;
    if is_single_byte {
        Ok(u8::from_be_bytes(read_bytes_increment_offset::<1>(offset, buf)?) as usize)
    } else {
        let mut len = u32::from_be_bytes(read_bytes_increment_offset::<4>(offset, buf)?);
        len &= !StructBytes::<0>::VLE_U32_LEN_MASK;
        Ok(len as usize)
    }
}

fn read_slice_increment_offset<'a>(
    offset: &mut usize,
    n_bytes: usize,
    buf: &'a [u8],
) -> Result<&'a [u8], EncodingError> {
    if buf.len() < ((*offset) + n_bytes) {
        Err(EncodingError::UnexpectedEndOfEncodedStruct)
    } else {
        let slice = &buf[*offset..*offset + n_bytes];
        *offset += n_bytes;
        Ok(slice)
    }
}

fn read_bytes_increment_offset<const N_BYTES: usize>(
    offset: &mut usize,
    buf: &[u8],
) -> Result<[u8; N_BYTES], EncodingError> {
    if buf.len() < *offset + N_BYTES {
        Err(EncodingError::UnexpectedEndOfEncodedStruct)
    } else {
        let slice: [u8; N_BYTES] = buf[*offset..*offset + N_BYTES].try_into().unwrap();
        *offset += N_BYTES;
        Ok(slice)
    }
}

#[cfg(test)]
pub mod test {
    use std::{borrow::Cow, collections::HashMap};

    use resource::constants::snapshot::BUFFER_VALUE_INLINE;

    use crate::{
        graph::definition::{
            definition_key::{DefinitionID, DefinitionKey},
            r#struct::StructDefinition,
        },
        value::{
            struct_bytes::{append_length_as_vle, read_vle_increment_offset, StructBytes},
            value::Value,
            value_struct::StructValue,
        },
    };

    #[test]
    fn vle() {
        {
            let len = 3;
            let mut vec: Vec<u8> = Vec::new();
            append_length_as_vle(len, &mut vec).unwrap();
            assert_eq!(&[3], vec.as_slice());
            assert_eq!(len, read_vle_increment_offset(&mut 0, vec.as_slice()).unwrap());
        }
        {
            let len = 127;
            let mut vec: Vec<u8> = Vec::new();
            append_length_as_vle(len, &mut vec).unwrap();
            assert_eq!(&[127], vec.as_slice());
            assert_eq!(len, read_vle_increment_offset(&mut 0, vec.as_slice()).unwrap());
        }
        {
            let len = 128;
            let mut vec: Vec<u8> = Vec::new();
            append_length_as_vle(len, &mut vec).unwrap();
            assert_eq!(&[128, 0, 0, 128], vec.as_slice());
            assert_eq!(len, read_vle_increment_offset(&mut 0, vec.as_slice()).unwrap());
        }
        {
            let len = (1 + u32::MAX / 2) as usize;
            let mut vec: Vec<u8> = Vec::new();
            assert!(append_length_as_vle(len, &mut vec).is_err());
        }
        {
            let len = (u32::MAX / 2) as usize;
            let mut vec: Vec<u8> = Vec::new();
            append_length_as_vle(len, &mut vec).unwrap();
            assert_eq!(&[255, 255, 255, 255], vec.as_slice());
            assert_eq!(len, read_vle_increment_offset(&mut 0, vec.as_slice()).unwrap());
        }
    }

    #[test]
    fn encoding_decoding() {
        let test_values = [
            (Value::String(Cow::Borrowed("abc")), Value::Long(0xbeef)),
            (Value::String(Cow::Owned(String::from_utf8(vec![b'X'; 512]).unwrap())), Value::Long(0xf00d)), // Bigger than 256 characters
        ];
        for (string_value, long_value) in test_values {
            let nested_key = DefinitionKey::build(StructDefinition::PREFIX, DefinitionID::build(0));
            let nested_fields = HashMap::from([(0, string_value), (1, long_value)]);
            let nested_struct = StructValue::new(nested_key, nested_fields);

            let struct_key = DefinitionKey::build(StructDefinition::PREFIX, DefinitionID::build(0));
            let struct_fields = HashMap::from([(0, Value::Struct(Cow::Owned(nested_struct.clone())))]);
            let struct_value = StructValue::new(struct_key, struct_fields);

            let struct_bytes: StructBytes<'static, BUFFER_VALUE_INLINE> =
                StructBytes::build(&Cow::Borrowed(&struct_value));
            let decoded = struct_bytes.as_struct();
            assert_eq!(decoded.fields(), struct_value.fields());
        }
    }
}
