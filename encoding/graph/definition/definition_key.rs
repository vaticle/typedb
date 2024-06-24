/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    fmt::{Display, Formatter},
    ops::Range,
};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use resource::constants::{encoding::DefinitionIDUInt, snapshot::BUFFER_KEY_INLINE};
use serde::{
    de::{Error, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};
use storage::key_value::StorageKey;

use crate::{
    layout::prefix::{Prefix, PrefixID},
    AsBytes, EncodingKeyspace, Keyable, Prefixed,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct DefinitionKey<'a> {
    bytes: Bytes<'a, { BUFFER_KEY_INLINE }>,
}

impl<'a> DefinitionKey<'a> {
    pub(crate) const KEYSPACE: EncodingKeyspace = EncodingKeyspace::Schema;
    pub const FIXED_WIDTH_ENCODING: bool = true;

    pub(crate) const LENGTH: usize = PrefixID::LENGTH + DefinitionID::LENGTH;
    pub(crate) const LENGTH_PREFIX: usize = PrefixID::LENGTH;
    pub(crate) const RANGE_DEFINITION_ID: Range<usize> =
        Self::RANGE_PREFIX.end..Self::RANGE_PREFIX.end + DefinitionID::LENGTH;

    pub(crate) const LABEL_KEYSPACE: EncodingKeyspace = EncodingKeyspace::Schema;

    pub fn new(bytes: Bytes<'a, BUFFER_KEY_INLINE>) -> Self {
        debug_assert_eq!(bytes.length(), Self::LENGTH);
        Self { bytes }
    }

    pub fn definition_id(&self) -> DefinitionID {
        DefinitionID::new(self.bytes().bytes()[Self::RANGE_DEFINITION_ID].try_into().unwrap())
    }

    pub fn build(prefix: Prefix, definition_id: DefinitionID) -> Self {
        let mut array = ByteArray::zeros(Self::LENGTH);
        array.bytes_mut()[Self::RANGE_PREFIX].copy_from_slice(&prefix.prefix_id().bytes());
        array.bytes_mut()[Self::RANGE_DEFINITION_ID].copy_from_slice(&definition_id.bytes());
        Self { bytes: Bytes::Array(array) }
    }

    pub fn build_prefix(prefix: Prefix) -> StorageKey<'static, { DefinitionKey::LENGTH_PREFIX }> {
        StorageKey::new(
            DefinitionKey::KEYSPACE,
            // TODO: Can we use a static const byte reference
            Bytes::Array(ByteArray::inline(prefix.prefix_id().bytes(), DefinitionKey::LENGTH_PREFIX)),
        )
    }

    pub fn as_reference<'this: 'a>(&'this self) -> DefinitionKey<'this> {
        Self::new(Bytes::Reference(self.bytes.as_reference()))
    }

    pub fn into_owned(self) -> DefinitionKey<'static> {
        DefinitionKey { bytes: self.bytes.into_owned() }
    }
}

impl<'a> AsBytes<'a, BUFFER_KEY_INLINE> for DefinitionKey<'a> {
    fn bytes(&'a self) -> ByteReference<'a> {
        self.bytes.as_reference()
    }

    fn into_bytes(self) -> Bytes<'a, BUFFER_KEY_INLINE> {
        self.bytes
    }
}

impl<'a> Keyable<'a, BUFFER_KEY_INLINE> for DefinitionKey<'a> {
    fn keyspace(&self) -> EncodingKeyspace {
        Self::KEYSPACE
    }
}

impl<'a> Prefixed<'a, BUFFER_KEY_INLINE> for DefinitionKey<'a> {}

impl<'a> Display for DefinitionKey<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // we'll just arbitrarily write it out as an u64 in Big Endian
        debug_assert!(self.bytes.length() < (u64::BITS / 8) as usize);
        let mut bytes = [0u8; (u64::BITS / 8) as usize];
        bytes[0..self.bytes.length()].copy_from_slice(self.bytes.bytes());
        let as_u64 = u64::from_be_bytes(bytes);
        write!(f, "{}", as_u64)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct DefinitionID {
    bytes: [u8; DefinitionID::LENGTH],
}

impl DefinitionID {
    pub(crate) const LENGTH: usize = std::mem::size_of::<DefinitionIDUInt>();

    pub fn new(bytes: [u8; DefinitionID::LENGTH]) -> DefinitionID {
        DefinitionID { bytes }
    }

    pub fn build(id: DefinitionIDUInt) -> Self {
        debug_assert_eq!(std::mem::size_of_val(&id), DefinitionID::LENGTH);
        DefinitionID { bytes: id.to_be_bytes() }
    }

    pub fn as_uint(&self) -> DefinitionIDUInt {
        DefinitionIDUInt::from_be_bytes(self.bytes)
    }

    pub fn bytes(&self) -> [u8; DefinitionID::LENGTH] {
        self.bytes
    }
}

impl<'a> Serialize for DefinitionKey<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self.bytes.bytes())
    }
}

impl<'de> Deserialize<'de> for DefinitionKey<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        pub struct DefinitionKeyVisitor;
        impl<'de> Visitor<'de> for DefinitionKeyVisitor {
            type Value = DefinitionKey<'static>;

            fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
                formatter.write_str("`DefinitionKey`")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(DefinitionKey { bytes: Bytes::Array(ByteArray::copy(v)) })
            }
        }

        deserializer.deserialize_bytes(DefinitionKeyVisitor)
    }
}
