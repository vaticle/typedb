/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{collections::HashMap, ops::Range, sync::Arc};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use primitive::either::Either;
use resource::constants::{
    encoding::StructFieldIDUInt,
    snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE},
};
use storage::{
    key_value::StorageKey,
    snapshot::{iterator::SnapshotIteratorError, ReadableSnapshot, WritableSnapshot},
};

use crate::{
    error::EncodingError,
    graph::{
        common::value_hasher::HashedID,
        definition::{
            definition_key::DefinitionKey,
            r#struct::{StructDefinition, StructDefinitionField},
        },
        thing::{
            vertex_attribute::{AttributeID, AttributeIDLength, AttributeVertex, StructAttributeID},
            vertex_generator::ThingVertexGenerator,
        },
        type_::vertex::{TypeID, TypeVertex},
        Typed,
    },
    layout::prefix::{Prefix, PrefixID},
    value::{
        boolean_bytes::BooleanBytes, date_bytes::DateBytes, date_time_bytes::DateTimeBytes,
        date_time_tz_bytes::DateTimeTZBytes, decimal_bytes::DecimalBytes, double_bytes::DoubleBytes,
        duration_bytes::DurationBytes, long_bytes::LongBytes, string_bytes::StringBytes, value::Value,
        value_type::ValueTypeCategory, ValueEncodable,
    },
    AsBytes, EncodingKeyspace, Keyable, Prefixed,
};

// TODO: Do we want to encode / decode the full struct all the time? or just wrap bytes and
// write some accessor logic so we efficiently deserialize only the fields we need.
#[derive(Debug, Clone, PartialEq)]
pub struct StructValue<'a> {
    definition_key: DefinitionKey<'a>,
    // a map allows empty fields to not be recorded at all
    fields: HashMap<StructFieldIDUInt, Value<'a>>,
}

impl<'a> StructValue<'a> {
    pub fn new(definition_key: DefinitionKey<'a>, fields: HashMap<StructFieldIDUInt, Value<'a>>) -> StructValue<'a> {
        StructValue { definition_key, fields }
    }

    pub fn build(
        definition_key: DefinitionKey<'a>,
        struct_definition: StructDefinition,
        value: HashMap<String, Value<'a>>,
    ) -> Result<StructValue<'a>, Vec<EncodingError>> {
        let mut fields: HashMap<StructFieldIDUInt, Value<'a>> = HashMap::new();
        let mut errors: Vec<EncodingError> = Vec::new();
        for (field_name, field_id) in struct_definition.field_names {
            let field_definition: &StructDefinitionField = &struct_definition.fields.get(&field_id).unwrap();
            if let Some(value) = value.get(&field_name) {
                if field_definition.value_type == value.value_type() {
                    if !fields.contains_key(&field_id) {
                        fields.insert(field_id, value.clone());
                    }
                } else {
                    errors.push(EncodingError::StructFieldValueTypeMismatch {
                        struct_name: struct_definition.name.clone(),
                        field_name,
                        expected: field_definition.value_type.clone(),
                    })
                }
            } else if !field_definition.optional {
                errors.push(EncodingError::StructMissingRequiredField {
                    struct_name: struct_definition.name.clone(),
                    field_name,
                })
            }
        }

        if errors.is_empty() {
            Ok(StructValue { definition_key, fields })
        } else {
            Err(errors)
        }
    }

    pub fn definition_key(&self) -> &DefinitionKey<'a> {
        &self.definition_key
    }

    pub fn fields(&self) -> &HashMap<StructFieldIDUInt, Value<'a>> {
        &self.fields
    }

    // Deeply nested structs may take up a lot of space with the u16 path.
    pub fn create_index_entries(
        &self,
        snapshot: &impl WritableSnapshot,
        thing_vertex_generator: &ThingVertexGenerator,
        attribute: &AttributeVertex<'_>,
    ) -> Result<Vec<StructIndexEntry>, Arc<SnapshotIteratorError>> {
        let mut acc: Vec<StructIndexEntry> = Vec::new();
        let mut path: Vec<StructFieldIDUInt> = Vec::new();
        Self::create_index_entries_recursively(
            snapshot,
            thing_vertex_generator.hasher(),
            attribute,
            &self.fields,
            &mut path,
            &mut acc,
        )?;
        Ok(acc)
    }

    fn create_index_entries_recursively<'b>(
        snapshot: &impl WritableSnapshot,
        hasher: &impl Fn(&[u8]) -> u64,
        attribute: &AttributeVertex<'b>,
        fields: &HashMap<StructFieldIDUInt, Value<'a>>,
        path: &mut Vec<StructFieldIDUInt>,
        acc: &mut Vec<StructIndexEntry<'static>>,
    ) -> Result<(), Arc<SnapshotIteratorError>> {
        for (idx, value) in fields.iter() {
            path.push(*idx);
            if let Value::Struct(struct_val) = value {
                Self::create_index_entries_recursively(
                    snapshot,
                    hasher.clone(),
                    attribute,
                    struct_val.fields(),
                    path,
                    acc,
                )?;
            } else {
                acc.push(StructIndexEntry::build(snapshot, hasher.clone(), path, value, attribute)?);
            }
            let popped = path.pop().unwrap();
            debug_assert_eq!(*idx, popped);
        }
        Ok(())
    }
}

pub struct StructIndexEntryKey<'a> {
    key_bytes: Bytes<'a, BUFFER_KEY_INLINE>,
}

pub struct StructIndexEntry<'a> {
    pub key: StructIndexEntryKey<'a>,
    pub value: Option<Bytes<'a, BUFFER_VALUE_INLINE>>,
}

impl<'a> StructIndexEntryKey<'a> {
    pub fn new(key_bytes: Bytes<'a, BUFFER_KEY_INLINE>) -> Self {
        Self { key_bytes }
    }
}

impl<'a> StructIndexEntry<'a> {
    pub fn new(key: StructIndexEntryKey<'a>, value: Option<Bytes<'a, BUFFER_VALUE_INLINE>>) -> Self {
        Self { key, value }
    }

    pub fn attribute_vertex(&self) -> AttributeVertex<'static> {
        let bytes = self.key.key_bytes.bytes();
        let attribute_type_id = TypeID::new(bytes[StructIndexEntry::ENCODING_TYPEID_RANGE].try_into().unwrap());
        let attribute_id =
            AttributeID::new(ValueTypeCategory::Struct, &bytes[(bytes.len() - StructAttributeID::LENGTH)..bytes.len()]);
        AttributeVertex::build(ValueTypeCategory::Struct, attribute_type_id, attribute_id)
    }
}

impl StructIndexEntry<'static> {
    const PREFIX: Prefix = Prefix::IndexValueToStruct;

    const ENCODING_PREFIX_RANGE: Range<usize> = 0..PrefixID::LENGTH;
    const ENCODING_VALUE_TYPE_RANGE: Range<usize> =
        Self::ENCODING_PREFIX_RANGE.end..{ Self::ENCODING_PREFIX_RANGE.end + 1 };
    const ENCODING_TYPEID_RANGE: Range<usize> =
        Self::ENCODING_VALUE_TYPE_RANGE.end..{ Self::ENCODING_VALUE_TYPE_RANGE.end + TypeID::LENGTH };

    const ENCODING_VALUE_RANGE_SHORT: Range<usize> =
        Self::ENCODING_TYPEID_RANGE.end..{ Self::ENCODING_TYPEID_RANGE.end + AttributeIDLength::Short.length() };
    const ENCODING_STRUCT_ATTRIBUTE_ID_RANGE_LONG: Range<usize> =
        Self::ENCODING_VALUE_RANGE_LONG.end..{ Self::ENCODING_VALUE_RANGE_LONG.end + StructAttributeID::LENGTH };

    const ENCODING_VALUE_RANGE_LONG: Range<usize> =
        Self::ENCODING_TYPEID_RANGE.end..{ Self::ENCODING_TYPEID_RANGE.end + AttributeIDLength::Long.length() };
    const ENCODING_STRUCT_ATTRIBUTE_ID_RANGE_SHORT: Range<usize> =
        Self::ENCODING_VALUE_RANGE_SHORT.end..{ Self::ENCODING_VALUE_RANGE_SHORT.end + StructAttributeID::LENGTH };

    pub fn build<'b, 'c>(
        snapshot: &impl ReadableSnapshot,
        hasher: &impl Fn(&[u8]) -> u64,
        path_to_field: &Vec<StructFieldIDUInt>,
        value: &Value<'b>,
        attribute: &AttributeVertex<'c>,
    ) -> Result<StructIndexEntry<'static>, Arc<SnapshotIteratorError>> {
        debug_assert_eq!(Prefix::VertexAttributeStruct, attribute.prefix());
        let mut buf = Self::build_prefix_typeid_path_value_into_buf(
            snapshot,
            hasher,
            path_to_field,
            value,
            attribute.type_id_(),
        )?;
        buf.extend_from_slice(attribute.attribute_id().bytes());

        let value = match &value {
            Value::Boolean(_)
            | Value::Long(_)
            | Value::Double(_)
            | Value::Decimal(_)
            | Value::Date(_)
            | Value::DateTime(_)
            | Value::DateTimeTZ(_)
            | Value::Duration(_) => None,
            Value::String(value) => Some(StringBytes::<BUFFER_VALUE_INLINE>::build_owned(value).into_bytes()),
            Value::Struct(_) => unreachable!(),
        };
        Ok(Self { key: StructIndexEntryKey::new(Bytes::copy(buf.as_slice())), value })
    }

    pub fn build_prefix_typeid_path_value<'b, 'c>(
        snapshot: &impl ReadableSnapshot,
        thing_vertex_generator: &ThingVertexGenerator,
        path_to_field: &Vec<StructFieldIDUInt>,
        value: &Value<'b>,
        attribute_type: &TypeVertex<'c>,
    ) -> Result<StorageKey<'static, BUFFER_KEY_INLINE>, Arc<SnapshotIteratorError>> {
        let buf = Self::build_prefix_typeid_path_value_into_buf(
            snapshot,
            thing_vertex_generator.hasher(),
            path_to_field,
            value,
            attribute_type.type_id_(),
        )?;
        Ok(StorageKey::new_owned(Self::KEYSPACE, ByteArray::copy(buf.as_slice())))
    }

    fn build_prefix_typeid_path_value_into_buf<'b>(
        snapshot: &impl ReadableSnapshot,
        hasher: &impl Fn(&[u8]) -> u64,
        path_to_field: &Vec<StructFieldIDUInt>,
        value: &Value<'b>,
        attribute_type_id: TypeID,
    ) -> Result<Vec<u8>, Arc<SnapshotIteratorError>> {
        let mut buf: Vec<u8> = Vec::with_capacity(
            PrefixID::LENGTH +  // Prefix::IndexValueToStruct
                PrefixID::LENGTH +      // ValueTypeCategory of indexed value
                TypeID::LENGTH +        // TypeID of Attribute being indexed
                path_to_field.len() +   // Path to the field
                AttributeIDLength::Long.length() + // Value for the field.
                StructAttributeID::LENGTH, // ID of the attribute being indexed
        );

        buf.extend_from_slice(&Prefix::IndexValueToStruct.prefix_id().bytes);
        buf.extend_from_slice(&value.value_type().category().to_bytes());
        buf.extend_from_slice(&attribute_type_id.bytes());
        for p in path_to_field {
            buf.extend_from_slice(&p.to_be_bytes())
        }
        match &value {
            Value::Boolean(value) => buf.extend_from_slice(&BooleanBytes::build(*value).bytes()),
            Value::Long(value) => buf.extend_from_slice(&LongBytes::build(*value).bytes()),
            Value::Double(value) => buf.extend_from_slice(&DoubleBytes::build(*value).bytes()),
            Value::Decimal(value) => buf.extend_from_slice(&DecimalBytes::build(*value).bytes()),
            Value::Date(value) => buf.extend_from_slice(&DateBytes::build(*value).bytes()),
            Value::DateTime(value) => buf.extend_from_slice(&DateTimeBytes::build(*value).bytes()),
            Value::DateTimeTZ(value) => buf.extend_from_slice(&DateTimeTZBytes::build(*value).bytes()),
            Value::Duration(value) => buf.extend_from_slice(&DurationBytes::build(*value).bytes()),
            Value::String(value) => {
                let string_bytes = StringBytes::<0>::build_ref(value);
                Self::encode_string_into(snapshot, hasher, string_bytes.as_reference(), &mut buf)?;
            }
            Value::Struct(_) => unreachable!(),
        };
        Ok(buf)
    }
}

impl<'a> StructIndexEntry<'a> {
    const STRING_FIELD_LENGTH: usize = 17;
    const STRING_FIELD_HASHID_LENGTH: usize = 9;
    const STRING_FIELD_HASHED_PREFIX_LENGTH: usize = { Self::STRING_FIELD_LENGTH - Self::STRING_FIELD_HASHID_LENGTH };
    const STRING_FIELD_HASHED_FLAG: u8 = 0b1000_0000;
    const STRING_FIELD_HASHED_FLAG_INDEX: usize = Self::STRING_FIELD_HASHED_HASH_LENGTH;
    const STRING_FIELD_HASHED_HASH_LENGTH: usize = Self::STRING_FIELD_HASHID_LENGTH - 1;
    const STRING_FIELD_INLINE_LENGTH: usize = { Self::STRING_FIELD_LENGTH - 1 };

    fn encode_string_into<const INLINE_SIZE: usize>(
        snapshot: &impl ReadableSnapshot,
        hasher: &impl Fn(&[u8]) -> u64,
        string_bytes: StringBytes<'_, INLINE_SIZE>,
        buf: &mut Vec<u8>,
    ) -> Result<(), Arc<SnapshotIteratorError>> {
        if Self::is_string_inlineable(string_bytes.as_reference()) {
            let mut inline_bytes: [u8; StructIndexEntry::STRING_FIELD_INLINE_LENGTH] =
                [0; { StructIndexEntry::STRING_FIELD_INLINE_LENGTH }];
            inline_bytes[0..string_bytes.bytes().length()].copy_from_slice(string_bytes.bytes().bytes());
            buf.extend_from_slice(&inline_bytes);
            buf.push(string_bytes.length() as u8);
        } else {
            buf.extend_from_slice(&string_bytes.bytes().bytes()[0..Self::STRING_FIELD_HASHED_PREFIX_LENGTH]);
            let prefix_key: Bytes<'_, BUFFER_KEY_INLINE> = Bytes::reference(buf.as_slice());
            let disambiguated_hash_bytes: [u8; StructIndexEntry::STRING_FIELD_HASHID_LENGTH] =
                match Self::find_existing_or_next_disambiguated_hash(
                    snapshot,
                    hasher,
                    prefix_key,
                    string_bytes.bytes().bytes(),
                )? {
                    Either::First(hash) => hash,
                    Either::Second(hash) => hash,
                };
            buf.extend_from_slice(&disambiguated_hash_bytes);
        }
        Ok(())
    }

    fn is_string_inlineable<'b, const INLINE_SIZE: usize>(string_bytes: StringBytes<'b, INLINE_SIZE>) -> bool {
        string_bytes.length() < Self::STRING_FIELD_HASHED_PREFIX_LENGTH + Self::STRING_FIELD_HASHID_LENGTH
    }
}

impl<'a> HashedID<{ StructIndexEntry::STRING_FIELD_HASHID_LENGTH }> for StructIndexEntry<'a> {
    const KEYSPACE: EncodingKeyspace = EncodingKeyspace::Data;
    const FIXED_WIDTH_KEYS: bool = { Prefix::IndexValueToStruct.fixed_width_keys() };
}

impl<'a> AsBytes<'a, BUFFER_KEY_INLINE> for StructIndexEntryKey<'a> {
    fn bytes(&'a self) -> ByteReference<'a> {
        self.key_bytes.as_reference()
    }

    fn into_bytes(self) -> Bytes<'a, BUFFER_KEY_INLINE> {
        self.key_bytes
    }
}

impl<'a> Keyable<'a, BUFFER_KEY_INLINE> for StructIndexEntryKey<'a> {
    fn keyspace(&self) -> EncodingKeyspace {
        StructIndexEntry::KEYSPACE
    }
}
