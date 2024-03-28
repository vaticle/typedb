/*
 * Copyright (C) 2023 Vaticle
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

use std::{borrow::Borrow, cmp::Ordering};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use primitive::prefix_range::Prefix;
use serde::{Deserialize, Serialize};

use crate::{keyspace::KeyspaceId, KeyspaceSet};

#[derive(Debug, Clone)]
pub enum StorageKey<'bytes, const S: usize> {
    Array(StorageKeyArray<S>),
    Reference(StorageKeyReference<'bytes>),
}

impl<'bytes, const S: usize> StorageKey<'bytes, S> {
    pub fn new<KS: KeyspaceSet>(keyspace: KS, bytes: Bytes<'bytes, S>) -> Self {
        match bytes {
            Bytes::Array(array) => Self::Array(StorageKeyArray::new(keyspace, array)),
            Bytes::Reference(reference) => Self::Reference(StorageKeyReference::new(keyspace, reference)),
        }
    }

    pub fn new_ref<KS: KeyspaceSet>(keyspace: KS, bytes: ByteReference<'bytes>) -> Self {
        StorageKey::Reference(StorageKeyReference::new(keyspace, bytes))
    }

    pub fn new_owned<KS: KeyspaceSet>(keyspace: KS, bytes: ByteArray<S>) -> Self {
        StorageKey::Array(StorageKeyArray::new(keyspace, bytes))
    }

    pub fn bytes(&'bytes self) -> &'bytes [u8] {
        match self {
            StorageKey::Array(array) => array.bytes(),
            StorageKey::Reference(reference) => reference.bytes(),
        }
    }

    pub fn into_byte_array_or_ref(self) -> Bytes<'bytes, S> {
        match self {
            StorageKey::Array(array) => Bytes::Array(array.into_byte_array()),
            StorageKey::Reference(reference) => Bytes::Reference(reference.into_byte_ref()),
        }
    }

    pub(crate) fn keyspace_id(&self) -> KeyspaceId {
        match self {
            StorageKey::Array(bytes) => bytes.keyspace_id,
            StorageKey::Reference(bytes) => bytes.keyspace_id,
        }
    }

    pub fn as_reference(&'bytes self) -> StorageKeyReference<'bytes> {
        match self {
            StorageKey::Array(array) => StorageKeyReference::from(array),
            StorageKey::Reference(reference) => {
                StorageKeyReference::new_raw(reference.keyspace_id(), reference.byte_ref())
            }
        }
    }

    pub fn into_owned_array(self) -> StorageKeyArray<S> {
        match self {
            StorageKey::Array(array) => array,
            StorageKey::Reference(reference) => StorageKeyArray::from(reference),
        }
    }
}

impl<'bytes, const SZ: usize> PartialEq<Self> for StorageKey<'bytes, SZ> {
    fn eq(&self, other: &Self) -> bool {
        self.keyspace_id() == other.keyspace_id() && self.bytes() == other.bytes()
    }
}

impl<'bytes, const SZ: usize> Eq for StorageKey<'bytes, SZ> {}

impl<'bytes, const SZ: usize> PartialOrd<Self> for StorageKey<'bytes, SZ> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // TODO: should this take into account Keyspace ID?
        Some(self.cmp(other))
    }
}

impl<'bytes, const SZ: usize> Ord for StorageKey<'bytes, SZ> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.bytes().cmp(other.bytes())
    }
}

impl<'bytes, const SZ: usize> Prefix for StorageKey<'bytes, SZ> {
    fn starts_with(&self, other: &Self) -> bool {
        self.bytes().starts_with(other.bytes())
    }
}

// TODO: we may want to fix the SZ for all storage keys here
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct StorageKeyArray<const SZ: usize> {
    keyspace_id: KeyspaceId,
    byte_array: ByteArray<SZ>,
}

impl<const SZ: usize> StorageKeyArray<SZ> {
    pub fn new<KS: KeyspaceSet>(keyspace_id: KS, array: ByteArray<SZ>) -> Self {
        Self::new_raw(KeyspaceId(keyspace_id.id()), array)
    }

    pub(crate) fn new_raw(keyspace_id: KeyspaceId, array: ByteArray<SZ>) -> Self {
        Self { keyspace_id, byte_array: array }
    }

    pub(crate) fn keyspace_id(&self) -> KeyspaceId {
        self.keyspace_id
    }

    pub fn bytes(&self) -> &[u8] {
        self.byte_array.bytes()
    }

    pub fn byte_array(&self) -> &ByteArray<SZ> {
        &self.byte_array
    }

    pub fn into_byte_array(self) -> ByteArray<SZ> {
        self.byte_array
    }
}

impl<const SZ: usize> PartialEq<Self> for StorageKeyArray<SZ> {
    fn eq(&self, other: &Self) -> bool {
        self.keyspace_id() == other.keyspace_id() && self.bytes() == other.bytes()
    }
}

impl<const SZ: usize> Eq for StorageKeyArray<SZ> {}

impl<const SZ: usize> PartialOrd<Self> for StorageKeyArray<SZ> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // TODO: should this take into account Keyspace ID?
        Some(self.cmp(other))
    }
}

impl<const SZ: usize> Ord for StorageKeyArray<SZ> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.bytes().cmp(other.bytes())
    }
}

impl<const SZ: usize> Borrow<[u8]> for StorageKeyArray<SZ> {
    fn borrow(&self) -> &[u8] {
        self.bytes()
    }
}

impl<const SZ: usize> From<StorageKeyReference<'_>> for StorageKeyArray<SZ> {
    fn from(key: StorageKeyReference<'_>) -> Self {
        StorageKeyArray { keyspace_id: key.keyspace_id(), byte_array: ByteArray::copy(key.bytes()) }
    }
}

impl<const SZ: usize, KS: KeyspaceSet> From<(Vec<u8>, KS)> for StorageKeyArray<SZ> {
    // For tests
    fn from((bytes, keyspace): (Vec<u8>, KS)) -> Self {
        From::from((bytes.as_slice(), keyspace))
    }
}

impl<const SZ: usize, KS: KeyspaceSet> From<(&[u8], KS)> for StorageKeyArray<SZ> {
    // For tests
    fn from((bytes, keyspace): (&[u8], KS)) -> Self {
        let bytes = ByteArray::<SZ>::copy(bytes);
        StorageKeyArray { keyspace_id: KeyspaceId(keyspace.id()), byte_array: bytes }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct StorageKeyReference<'bytes> {
    keyspace_id: KeyspaceId,
    reference: ByteReference<'bytes>,
}

impl<'bytes> StorageKeyReference<'bytes> {
    pub fn new<KS: KeyspaceSet>(keyspace: KS, reference: ByteReference<'bytes>) -> StorageKeyReference<'bytes> {
        Self::new_raw(KeyspaceId(keyspace.id()), reference)
    }

    pub(crate) const fn new_raw(keyspace_id: KeyspaceId, reference: ByteReference<'bytes>) -> Self {
        Self { keyspace_id, reference }
    }

    pub(crate) fn keyspace_id(&self) -> KeyspaceId {
        self.keyspace_id
    }

    pub fn bytes(&self) -> &[u8] {
        self.reference.bytes()
    }

    pub fn byte_ref(&self) -> ByteReference<'bytes> {
        self.reference
    }

    pub(crate) fn into_byte_ref(self) -> ByteReference<'bytes> {
        self.reference
    }
}

impl<'bytes, const SZ: usize> From<&'bytes StorageKeyArray<SZ>> for StorageKeyReference<'bytes> {
    fn from(array_ref: &'bytes StorageKeyArray<SZ>) -> Self {
        StorageKeyReference::new_raw(array_ref.keyspace_id, ByteReference::from(array_ref.byte_array()))
    }
}

impl<'bytes> PartialEq<Self> for StorageKeyReference<'bytes> {
    fn eq(&self, other: &Self) -> bool {
        self.keyspace_id() == other.keyspace_id() && self.bytes() == other.bytes()
    }
}

impl<'bytes> Eq for StorageKeyReference<'bytes> {}

impl<'bytes> PartialOrd<Self> for StorageKeyReference<'bytes> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // TODO: should this take into account Keyspace ID?
        Some(self.cmp(other))
    }
}

impl<'bytes> Ord for StorageKeyReference<'bytes> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.bytes().cmp(other.bytes())
    }
}
