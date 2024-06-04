/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::{BTreeMap, Bound},
    fmt,
    iter::{IntoIterator, Peekable},
    sync::{atomic::AtomicBool, Arc},
};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, util::increment, Bytes};
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use serde::{
    de::{self, MapAccess, SeqAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{
    key_range::{KeyRange, RangeEnd},
    key_value::StorageKeyArray,
    keyspace::{KeyspaceId, KEYSPACE_MAXIMUM_COUNT},
    snapshot::{lock::LockType, write::Write},
};

#[derive(Debug)]
pub struct OperationsBuffer {
    write_buffers: [WriteBuffer; KEYSPACE_MAXIMUM_COUNT],
    locks: BTreeMap<ByteArray<BUFFER_KEY_INLINE>, LockType>,
}

impl OperationsBuffer {
    pub(crate) fn new() -> OperationsBuffer {
        OperationsBuffer {
            write_buffers: core::array::from_fn(|i| WriteBuffer::new(KeyspaceId(i as u8))),
            locks: BTreeMap::new(),
        }
    }

    pub(crate) fn is_writes_empty(&self) -> bool {
        self.write_buffers.iter().all(|buffer| buffer.is_empty())
    }

    pub(crate) fn writes_in(&self, keyspace_id: KeyspaceId) -> &WriteBuffer {
        &self.write_buffers[keyspace_id.0 as usize]
    }

    pub(crate) fn writes_in_mut(&mut self, keyspace_id: KeyspaceId) -> &mut WriteBuffer {
        &mut self.write_buffers[keyspace_id.0 as usize]
    }

    pub(crate) fn write_buffers(&self) -> impl Iterator<Item = &WriteBuffer> {
        self.write_buffers.iter()
    }

    pub(crate) fn write_buffers_mut(&mut self) -> impl Iterator<Item = &mut WriteBuffer> {
        self.write_buffers.iter_mut()
    }

    pub(crate) fn lock_add(&mut self, key: ByteArray<BUFFER_KEY_INLINE>, lock_type: LockType) {
        self.locks.insert(key, lock_type);
    }

    pub(crate) fn lock_remove(&mut self, key: &ByteArray<BUFFER_KEY_INLINE>) {
        self.locks.remove(key);
    }

    pub(crate) fn locks(&self) -> &BTreeMap<ByteArray<BUFFER_KEY_INLINE>, LockType> {
        &self.locks
    }

    pub(crate) fn locks_empty(&self) -> bool {
        self.locks.is_empty()
    }

    pub(crate) fn iterate_writes(&self) -> impl Iterator<Item = (StorageKeyArray<{ BUFFER_KEY_INLINE }>, Write)> + '_ {
        self.write_buffers().flat_map(|buffer| {
            buffer.iterate_range(KeyRange::new_unbounded(Bytes::Array(ByteArray::<BUFFER_KEY_INLINE>::empty())))
        })
    }
}

impl<'a> IntoIterator for &'a OperationsBuffer {
    type Item = &'a WriteBuffer;
    type IntoIter = <&'a [WriteBuffer] as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.write_buffers.iter()
    }
}

// TODO: implement our own alternative to BTreeMap, which
//       1) allows storing StorageKeyArray's directly, while doing lookup with any StorageKey. Then
//          we would not need to allocate one buffer per keyspace ahead of time.
//       2) stores an initial set of ordered keys inline - BTreeMap immediately allocates on the
//          heap for the first element and amortize allocating all Writes into one.
//       3) We would benefit hugely from a table where writes are never moved, so we can freely
//          take references to existing writes without having to Clone them out every time... This
//          might lead us to a RocksDB-like Buffer+Index structure
#[derive(Debug)]
pub struct WriteBuffer {
    pub(crate) keyspace_id: KeyspaceId,
    writes: BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write>,
}

impl WriteBuffer {
    pub(crate) fn new(keyspace_id: KeyspaceId) -> WriteBuffer {
        WriteBuffer { keyspace_id, writes: BTreeMap::new() }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.writes.is_empty()
    }

    pub(crate) fn insert(&mut self, key: ByteArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        self.writes.insert(key, Write::Insert { value });
    }

    pub(crate) fn uninsert(
        &mut self,
        key: ByteArray<BUFFER_KEY_INLINE>,
        expected_value: ByteArray<BUFFER_VALUE_INLINE>,
    ) {
        match self.writes.remove(&key) {
            Some(Write::Insert { value, .. }) => {
                if value != expected_value {
                    panic!("Unexpected value `{:?}` when trying to uninsert; expected `{:?}`", value, expected_value)
                }
            }
            Some(_other_write) => panic!("Attempting to uninsert a key that was put or deleted"),
            None => panic!("Attempting to uninsert a key that was not inserted"),
        }
    }

    pub(crate) fn put(&mut self, key: ByteArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        self.writes
            .insert(key, Write::Put { value, reinsert: Arc::new(AtomicBool::new(false)), known_to_exist: false });
    }

    pub(crate) fn put_existing(&mut self, key: ByteArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        self.writes.insert(key, Write::Put { value, reinsert: Arc::new(AtomicBool::new(false)), known_to_exist: true });
    }

    pub(crate) fn unput(&mut self, key: ByteArray<BUFFER_KEY_INLINE>, expected_value: ByteArray<BUFFER_VALUE_INLINE>) {
        match self.writes.remove(&key) {
            Some(Write::Put { value, .. }) => {
                if value != expected_value {
                    panic!("Unexpected value `{:?}` when trying to unput; expected `{:?}`", value, expected_value)
                }
            }
            Some(_other_write) => panic!("Attempting to unput a key that was inserted or deleted"),
            None => panic!("Attempting to unput a key that was not put"),
        }
    }

    pub(crate) fn delete(&mut self, key: ByteArray<BUFFER_KEY_INLINE>) {
        // note: If this snapshot has Inserted the key, we don't know if it's a preexisting key
        // with a different value for overwrite or a brand new key so we always have to write a
        // delete marker instead of removing an element from the map in some cases
        self.writes.insert(key, Write::Delete);
    }

    pub(crate) fn contains(&self, key: &ByteArray<BUFFER_KEY_INLINE>) -> bool {
        self.writes.get(key.bytes()).is_some()
    }

    pub(crate) fn get(&self, key: &[u8]) -> Option<&Write> {
        self.writes.get(key)
    }

    pub(crate) fn iterate_range<const INLINE: usize>(&self, range: KeyRange<Bytes<'_, INLINE>>) -> BufferRangeIterator {
        let (range_start, range_end, _) = range.into_raw();
        let exclusive_end_bytes = Self::compute_exclusive_end(range_start.as_reference(), &range_end);
        let end = if matches!(range_end, RangeEnd::Unbounded) {
            Bound::Unbounded
        } else {
            Bound::Excluded(exclusive_end_bytes.bytes())
        };
        // TODO: we shouldn't have to copy now that we use single-writer semantics
        BufferRangeIterator::new(
            self.writes
                .range::<[u8], _>((Bound::Included(range_start.bytes()), end))
                .map(|(key, val)| (StorageKeyArray::new_raw(self.keyspace_id, key.clone()), val.clone()))
                .collect::<Vec<_>>(),
        )
    }

    // TODO: if the iterate_range becomes zero-copy, then we can eliminate this method
    pub(crate) fn any_in_range<const INLINE: usize>(&self, range: KeyRange<Bytes<'_, INLINE>>) -> bool {
        let (range_start, range_end, _) = range.into_raw();
        let exclusive_end_bytes = Self::compute_exclusive_end(range_start.as_reference(), &range_end);
        let end = if matches!(range_end, RangeEnd::Unbounded) {
            Bound::Unbounded
        } else {
            Bound::Excluded(exclusive_end_bytes.bytes())
        };
        self.writes.range::<[u8], _>((Bound::Included(range_start.bytes()), end)).any(|(_, write)| !write.is_delete())
    }

    fn compute_exclusive_end<const INLINE: usize>(
        start: ByteReference<'_>,
        end: &RangeEnd<Bytes<'_, INLINE>>,
    ) -> ByteArray<INLINE> {
        match end {
            RangeEnd::SameAsStart => {
                let mut start_plus_1 = ByteArray::from(start);
                increment(start_plus_1.bytes_mut()).unwrap();
                start_plus_1
            }
            RangeEnd::Inclusive(value) => {
                let mut end_plus_1 = value.clone().into_array();
                increment(end_plus_1.bytes_mut()).unwrap();
                end_plus_1
            }
            RangeEnd::Exclusive(value) => value.clone().into_array(),
            RangeEnd::Unbounded => ByteArray::empty(),
        }
    }

    pub(crate) fn writes(&self) -> &BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write> {
        &self.writes
    }

    pub(crate) fn writes_mut(&mut self) -> &mut BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write> {
        &mut self.writes
    }

    pub(crate) fn get_write(&self, key: ByteReference<'_>) -> Option<&Write> {
        self.writes.get(key.bytes())
    }
}

// TODO: this iterator takes a 'snapshot' of the time it was opened at - we could have it read without clones and have it 'live' if the buffers are immutable
pub struct BufferRangeIterator {
    inner: Peekable<<Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, Write)> as IntoIterator>::IntoIter>,
}

impl BufferRangeIterator {
    fn new(range: Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, Write)>) -> Self {
        Self { inner: range.into_iter().peekable() }
    }

    pub(crate) fn empty() -> Self {
        Self { inner: Vec::new().into_iter().peekable() }
    }

    pub(crate) fn peek(&mut self) -> Option<&(StorageKeyArray<BUFFER_KEY_INLINE>, Write)> {
        self.inner.peek()
    }

    // TODO: This is a 'dumb' seek, in that it simply consumes values until the criteria is no longer matched
    //       When buffers are not too large, this is likely to be fast.
    //       This can be improved by opening a new range over the buffer directly.
    //         --> perhaps when the buffer is "large" and the distance to the next key is "large"?
    pub(crate) fn seek(&mut self, target: impl Borrow<[u8]>) {
        while let Some((key, _)) = self.peek() {
            if key.bytes().cmp(target.borrow()) == Ordering::Less {
                self.next();
            } else {
                return;
            }
        }
    }
}

impl Iterator for BufferRangeIterator {
    type Item = (StorageKeyArray<BUFFER_KEY_INLINE>, Write);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl Serialize for OperationsBuffer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("OperationsBuffer", 2)?;
        state.serialize_field("WriteBuffers", &self.write_buffers)?;
        state.serialize_field("Locks", &self.locks)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for OperationsBuffer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        enum Field {
            WriteBuffers,
            Locks,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FieldVisitor;

                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                        formatter.write_str("`WriteBuffers` or `Locks`.")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: de::Error,
                    {
                        match value {
                            "WriteBuffers" => Ok(Field::WriteBuffers),
                            "Locks" => Ok(Field::Locks),
                            _ => Err(de::Error::unknown_field(value, &["WriteBuffers"])),
                        }
                    }
                }

                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        struct OperationsBufferVisitor;

        impl<'de> Visitor<'de> for OperationsBufferVisitor {
            type Value = OperationsBuffer;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("struct OperationsBufferVisitor")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<OperationsBuffer, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let write_buffers = seq.next_element()?.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                let locks: BTreeMap<ByteArray<BUFFER_KEY_INLINE>, LockType> =
                    seq.next_element()?.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                Ok(OperationsBuffer { write_buffers, locks })
            }
        }

        deserializer.deserialize_tuple(KEYSPACE_MAXIMUM_COUNT, OperationsBufferVisitor)
    }
}

impl Serialize for WriteBuffer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("KeyspaceBuffer", 2)?;
        state.serialize_field("KeyspaceId", &self.keyspace_id)?;
        state.serialize_field("Buffer", &self.writes)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for WriteBuffer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        enum Field {
            KeyspaceId,
            Buffer,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FieldVisitor;

                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                        formatter.write_str("`KeyspaceId` or `Buffer`")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: de::Error,
                    {
                        match value {
                            "KeyspaceId" => Ok(Field::KeyspaceId),
                            "Buffer" => Ok(Field::Buffer),
                            _ => Err(de::Error::unknown_field(value, &["KeyspaceId", "Buffer"])),
                        }
                    }
                }

                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        struct KeyspaceBufferVisitor;

        impl<'de> Visitor<'de> for KeyspaceBufferVisitor {
            type Value = WriteBuffer;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("struct KeyspaceBufferVisitor")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<WriteBuffer, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let keyspace_id = seq.next_element()?.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                let buffer: BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write> =
                    seq.next_element()?.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                Ok(WriteBuffer { keyspace_id, writes: buffer })
            }

            fn visit_map<V>(self, mut map: V) -> Result<WriteBuffer, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut keyspace_id: Option<KeyspaceId> = None;
                let mut buffer: Option<BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write>> = None;
                while let Some(key) = map.next_key()? {
                    match key {
                        Field::KeyspaceId => {
                            if keyspace_id.is_some() {
                                return Err(de::Error::duplicate_field("KeyspaceId"));
                            }
                            keyspace_id = Some(map.next_value()?);
                        }
                        Field::Buffer => {
                            if buffer.is_some() {
                                return Err(de::Error::duplicate_field("Buffer"));
                            }
                            buffer = Some(map.next_value()?);
                        }
                    }
                }

                let keyspace_id = keyspace_id.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                let buffer: BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write> =
                    buffer.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                Ok(WriteBuffer { keyspace_id, writes: buffer })
            }
        }

        deserializer.deserialize_struct("KeyspaceBuffer", &["KeyspaceID", "Buffer"], KeyspaceBufferVisitor)
    }
}
