/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;

use bytes::{byte_array::ByteArray, Bytes};
use lending_iterator::LendingIterator;
use primitive::either::Either;
use resource::constants::snapshot::BUFFER_KEY_INLINE;
use storage::{
    key_range::KeyRange,
    key_value::StorageKey,
    snapshot::{iterator::SnapshotIteratorError, ReadableSnapshot},
};

use crate::EncodingKeyspace;

pub(crate) trait HashedID<const TOTAL_LENGTH: usize> {
    const HASHID_HASH_LENGTH: usize = TOTAL_LENGTH - 1;
    const HASHID_DISAMBIGUATOR_BYTE_INDEX: usize = Self::HASHID_HASH_LENGTH;
    const HASHID_DISAMBIGUATOR_BYTE_IS_HASH_FLAG: u8 = 0b1000_0000;
    const KEYSPACE: EncodingKeyspace;
    const FIXED_WIDTH_KEYS: bool;
    fn find_existing_or_next_disambiguated_hash<Snapshot, const INLINE_SIZE: usize>(
        snapshot: &Snapshot,
        hasher: &impl Fn(&[u8]) -> u64,
        key_without_hash: Bytes<'_, INLINE_SIZE>,
        value_bytes: &[u8],
    ) -> Result<Either<[u8; TOTAL_LENGTH], [u8; TOTAL_LENGTH]>, Arc<SnapshotIteratorError>>
    where
        Snapshot: ReadableSnapshot,
    {
        let mut hash_bytes = &hasher(value_bytes).to_be_bytes()[0..Self::HASHID_HASH_LENGTH];
        let key_without_tail_byte = ByteArray::copy_concat([key_without_hash.bytes(), hash_bytes]);
        match Self::disambiguate(snapshot, key_without_tail_byte, value_bytes)? {
            Either::First(tail) => Ok(Either::First(Self::concat_hash_and_tail(&hash_bytes, tail))),
            Either::Second(tail) => Ok(Either::Second(Self::concat_hash_and_tail(&hash_bytes, tail))),
        }
    }

    fn concat_hash_and_tail(hash_bytes: &[u8], tail: u8) -> [u8; TOTAL_LENGTH] {
        let mut bytes: [u8; TOTAL_LENGTH] = [0; TOTAL_LENGTH];
        bytes[0..Self::HASHID_HASH_LENGTH].copy_from_slice(hash_bytes);
        bytes[Self::HASHID_HASH_LENGTH] = tail;
        bytes
    }

    fn disambiguate<Snapshot>(
        snapshot: &Snapshot,
        key_without_tail_byte: ByteArray<BUFFER_KEY_INLINE>,
        value_bytes: &[u8],
    ) -> Result<Either<u8, u8>, Arc<SnapshotIteratorError>>
    where
        Snapshot: ReadableSnapshot,
    {
        let tail_byte_index = key_without_tail_byte.length();
        let mut iter = snapshot.iterate_range(KeyRange::new_within(
            StorageKey::<BUFFER_KEY_INLINE>::new_ref(Self::KEYSPACE, key_without_tail_byte.as_ref()),
            Self::FIXED_WIDTH_KEYS,
        ));
        let mut next = iter.next().transpose()?;
        let mut first_unused_tail: Option<u8> = None;

        let mut next_tail: u8 = 0 | Self::HASHID_DISAMBIGUATOR_BYTE_IS_HASH_FLAG; // Start with the byte set
        while let Some((key, value)) = next {
            let key_tail = key.bytes()[tail_byte_index];
            if value.bytes() == value_bytes {
                return Ok(Either::First(key_tail));
            } else if next_tail != key_tail {
                // found unused tail ID. This could be a hole. We have to complete iteration.
                first_unused_tail = Some(next_tail);
            }
            if next_tail == u8::MAX {
                panic!("Too many hash collisions when allocating hash for prefix: {:?}", key_without_tail_byte);
            }
            next_tail += 1;
            next = iter.next().transpose()?;
        }
        Ok(Either::Second(first_unused_tail.unwrap_or(next_tail)))
    }
}
