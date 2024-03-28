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

use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::{BTreeMap, Bound},
    fmt, mem,
    mem::MaybeUninit,
    sync::{Arc, RwLock},
};

use bytes::{byte_array::ByteArray, util::increment, Bytes};
use iterator::State;
use primitive::prefix_range::{PrefixRange, RangeEnd};
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use serde::{
    de,
    de::{MapAccess, SeqAccess, Visitor},
    ser::{SerializeStruct, SerializeTuple},
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{
    key_value::StorageKeyArray,
    keyspace::{KeyspaceId, KEYSPACE_MAXIMUM_COUNT},
    snapshot::{snapshot::SnapshotError, write::Write},
};

#[derive(Debug)]
pub(crate) struct KeyspaceBuffers {
    buffers: [KeyspaceBuffer; KEYSPACE_MAXIMUM_COUNT],
}

impl KeyspaceBuffers {
    pub(crate) fn new() -> KeyspaceBuffers {
        KeyspaceBuffers { buffers: core::array::from_fn(|i| KeyspaceBuffer::new(KeyspaceId(i as u8))) }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.buffers.iter().all(|buffer| buffer.is_empty())
    }

    pub(crate) fn get(&self, keyspace_id: KeyspaceId) -> &KeyspaceBuffer {
        &self.buffers[keyspace_id.0 as usize]
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &KeyspaceBuffer> {
        self.buffers.iter()
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
pub(crate) struct KeyspaceBuffer {
    keyspace_id: KeyspaceId,
    buffer: RwLock<BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write>>,
}

impl KeyspaceBuffer {
    pub(crate) fn new(keyspace_id: KeyspaceId) -> KeyspaceBuffer {
        KeyspaceBuffer { keyspace_id, buffer: RwLock::new(BTreeMap::new()) }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.buffer.read().unwrap().is_empty()
    }

    pub(crate) fn insert(&self, key: ByteArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        self.buffer.write().unwrap().insert(key, Write::Insert { value });
    }

    pub(crate) fn insert_preexisting(&self, key: ByteArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        self.buffer.write().unwrap().insert(key, Write::InsertPreexisting { value, reinsert: Arc::default() });
    }

    pub(crate) fn require_exists(&self, key: ByteArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let mut map = self.buffer.write().unwrap();
        // TODO: what if it already has been inserted? Ie. InsertPreexisting?
        map.insert(key, Write::RequireExists { value });
    }

    pub(crate) fn delete(&self, key: ByteArray<BUFFER_KEY_INLINE>) {
        let mut map = self.buffer.write().unwrap();
        // note: If this snapshot has Inserted the key, we don't know if it's a preexisting key
        // with a different value for overwrite or a brand new key so we always have to write a
        // delete marker instead of removing an element from the map in some cases
        map.insert(key, Write::Delete);
    }

    pub(crate) fn contains(&self, key: &ByteArray<BUFFER_KEY_INLINE>) -> bool {
        self.buffer.read().unwrap().get(key.bytes()).is_some()
    }

    pub(crate) fn get<const INLINE_BYTES: usize>(&self, key: &[u8]) -> Option<ByteArray<INLINE_BYTES>> {
        let map = self.buffer.read().unwrap();
        match map.get(key) {
            | Some(Write::Insert { value })
            | Some(Write::InsertPreexisting { value, .. })
            | Some(Write::RequireExists { value }) => Some(ByteArray::copy(value.bytes())),
            Some(Write::Delete) | None => None,
        }
    }

    pub(crate) fn iterate_range<const INLINE: usize>(
        &self,
        range: PrefixRange<Bytes<'_, INLINE>>,
    ) -> BufferedPrefixIterator {
        let map = self.buffer.read().unwrap();
        let (start, end) = range.into_raw();
        let range_start = Bound::Included(start.bytes());

        let exclusive_end_bytes = match &end {
            RangeEnd::SameAsStart => {
                let mut start_plus_1 = start.clone().into_array();
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
        };
        let range_end = if matches!(end, RangeEnd::Unbounded) {
            Bound::Unbounded
        } else {
            Bound::Excluded(exclusive_end_bytes.bytes())
        };

        let values = map
            .range::<[u8], _>((range_start, range_end))
            .map(|(key, val)| (StorageKeyArray::new_raw(self.keyspace_id, key.clone()), val.clone()))
            .collect::<Vec<_>>();
        BufferedPrefixIterator::new(values)
    }

    pub(crate) fn map(&self) -> &RwLock<BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write>> {
        &self.buffer
    }
}

// TODO: this iterator takes a 'snapshot' of the time it was opened at - we could have it read without clones and have it 'live' if the buffers are immutable
pub(crate) struct BufferedPrefixIterator {
    state: State<SnapshotError>,
    index: usize,
    range: Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, Write)>,
}

impl BufferedPrefixIterator {
    fn new(range: Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, Write)>) -> Self {
        Self { state: State::Init, index: 0, range }
    }

    pub(crate) fn peek(&mut self) -> Option<Result<(&StorageKeyArray<BUFFER_KEY_INLINE>, &Write), SnapshotError>> {
        match &self.state {
            State::Done => None,
            State::Init => {
                self.update_state();
                self.peek()
            }
            State::ItemReady => {
                let (key, value) = &self.range[self.index];
                Some(Ok((key, value)))
            }
            State::ItemUsed => {
                self.advance_and_update_state();
                self.peek()
            }
            State::Error(_) => unreachable!("Unused state."),
        }
    }

    pub(crate) fn next(&mut self) -> Option<Result<(&StorageKeyArray<BUFFER_KEY_INLINE>, &Write), SnapshotError>> {
        match &self.state {
            State::Done => None,
            State::Init => {
                self.update_state();
                self.next()
            }
            State::ItemReady => {
                let (key, value) = &self.range[self.index];
                let value = Some(Ok((key, value)));
                self.state = State::ItemUsed;
                value
            }
            State::ItemUsed => {
                self.advance_and_update_state();
                self.next()
            }
            State::Error(_) => unreachable!("Unused state."),
        }
    }

    fn advance_and_update_state(&mut self) {
        assert_eq!(self.state, State::ItemUsed);
        self.index += 1;
        self.update_state();
    }

    fn update_state(&mut self) {
        assert!(matches!(self.state, State::ItemUsed) || matches!(self.state, State::Init));
        if self.index < self.range.len() {
            self.state = State::ItemReady;
        } else {
            self.state = State::Done;
        }
    }

    fn seek(&mut self, target: impl Borrow<[u8]>) {
        match &self.state {
            State::Done => {}
            State::Init => {
                self.update_state();
                self.seek(target);
            }
            State::ItemReady => loop {
                let peek = self.peek();
                if let Some(Ok((key, _))) = peek {
                    if key.bytes().cmp(target.borrow()) == Ordering::Less {
                        let _ = self.next();
                        self.update_state();
                    } else {
                        return;
                    }
                } else {
                    return;
                }
            },
            State::ItemUsed => {
                self.update_state();
                self.seek(target);
            }
            State::Error(_) => unreachable!("Unused state."),
        }
    }
}

impl Serialize for KeyspaceBuffers {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_tuple(KEYSPACE_MAXIMUM_COUNT)?;
        for buffer in &self.buffers {
            state.serialize_element(&buffer)?;
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for KeyspaceBuffers {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        enum Field {
            Buffers,
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
                        formatter.write_str("`Buffers`")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: de::Error,
                    {
                        match value {
                            "Buffers" => Ok(Field::Buffers),
                            _ => Err(de::Error::unknown_field(value, &["Buffers"])),
                        }
                    }
                }

                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        struct KeyspaceBuffersVisitor;

        impl<'de> Visitor<'de> for KeyspaceBuffersVisitor {
            type Value = KeyspaceBuffers;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("struct KeyspaceBuffersVisitor")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<KeyspaceBuffers, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let mut buffers_init: [MaybeUninit<KeyspaceBuffer>; KEYSPACE_MAXIMUM_COUNT] =
                    core::array::from_fn(|_| MaybeUninit::uninit());

                while let Some(keyspace_buffer) = seq.next_element()? {
                    let keyspace_buffer: KeyspaceBuffer = keyspace_buffer;
                    buffers_init[keyspace_buffer.keyspace_id.0 as usize].write(keyspace_buffer);
                }

                let buffers = unsafe { mem::transmute(buffers_init) };
                Ok(KeyspaceBuffers { buffers })
            }

            // fn visit_map<V>(self, mut map: V) -> Result<KeyspaceBuffers, V::Error>
            //     where
            //         V: MapAccess<'de>,
            // {
            //     let mut buffers: Option<[KeyspaceBuffer; KEYSPACE_ID_MAX]> = None;
            //     while let Some(key) = map.next_key()? {
            //         match key {
            //             Field::Buffers => {
            //                 if buffers.is_some() {
            //                     return Err(de::Error::duplicate_field("Buffers"));
            //                 }
            //                 buffers = Some(map.next_value()?);
            //             }
            //         }
            //     }
            //     let buffers: [KeyspaceBuffer; KEYSPACE_ID_MAX] = buffers.ok_or_else(|| de::Error::invalid_length(1, &self))?;
            //     Ok(KeyspaceBuffers {
            //         buffers: buffers
            //     })
            // }
        }

        deserializer.deserialize_tuple(KEYSPACE_MAXIMUM_COUNT, KeyspaceBuffersVisitor)
    }
}

impl Serialize for KeyspaceBuffer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("KeyspaceBuffer", 2)?;
        state.serialize_field("KeyspaceId", &self.keyspace_id)?;
        state.serialize_field("Buffer", &*self.buffer.read().unwrap())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for KeyspaceBuffer {
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
            type Value = KeyspaceBuffer;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("struct KeyspaceBufferVisitor")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<KeyspaceBuffer, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let keyspace_id = seq.next_element()?.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                let buffer: BTreeMap<ByteArray<BUFFER_KEY_INLINE>, Write> =
                    seq.next_element()?.ok_or_else(|| de::Error::invalid_length(1, &self))?;
                Ok(KeyspaceBuffer { keyspace_id, buffer: RwLock::new(buffer) })
            }

            fn visit_map<V>(self, mut map: V) -> Result<KeyspaceBuffer, V::Error>
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
                Ok(KeyspaceBuffer { keyspace_id, buffer: RwLock::new(buffer) })
            }
        }

        deserializer.deserialize_struct("KeyspaceBuffer", &["KeyspaceID", "Buffer"], KeyspaceBufferVisitor)
    }
}
