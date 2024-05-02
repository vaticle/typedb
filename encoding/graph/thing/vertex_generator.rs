/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc,
};

use bytes::{byte_array::ByteArray, Bytes};
use storage::{
    key_range::KeyRange,
    key_value::StorageKey,
    snapshot::{iterator::SnapshotIteratorError, ReadableSnapshot, WriteSnapshot},
    MVCCKey, MVCCStorage,
};

use crate::{
    error::EncodingError,
    graph::{
        thing::{
            vertex_attribute::{AttributeID, AttributeVertex, LongAttributeID, StringAttributeID},
            vertex_object::{ObjectID, ObjectVertex},
        },
        type_::vertex::{
            build_vertex_entity_type_prefix, build_vertex_relation_type_prefix, TypeID, TypeIDUInt, TypeVertex,
        },
        Typed,
    },
    layout::prefix::Prefix,
    value::{long_bytes::LongBytes, string_bytes::StringBytes, value_type::ValueType},
    AsBytes, Keyable, Prefixed,
};

pub struct ThingVertexGenerator {
    entity_ids: Box<[AtomicU64]>,
    relation_ids: Box<[AtomicU64]>,
    large_value_hasher: fn(&[u8]) -> u64,
}

impl Default for ThingVertexGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl ThingVertexGenerator {
    pub fn new() -> Self {
        // TODO: we should create a resizable Vector linked to the id of types/highest id of each type
        //       this will speed up booting time on load (loading this will require MAX types * 3 iterator searches) and reduce memory footprint
        Self::new_with_hasher(seahash::hash)
    }

    pub fn new_with_hasher(large_value_hasher: fn(&[u8]) -> u64) -> Self {
        // TODO: we should create a resizable Vector linked to the id of types/highest id of each type
        //       this will speed up booting time on load (loading this will require MAX types * 3 iterator searches) and reduce memory footprint
        ThingVertexGenerator {
            entity_ids: (0..=TypeIDUInt::MAX).map(|_| AtomicU64::new(0)).collect::<Box<[AtomicU64]>>(),
            relation_ids: (0..=TypeIDUInt::MAX).map(|_| AtomicU64::new(0)).collect::<Box<[AtomicU64]>>(),
            large_value_hasher,
        }
    }

    pub fn load<D>(storage: Arc<MVCCStorage<D>>) -> Result<Self, EncodingError> {
        Self::load_with_hasher(storage, seahash::hash)
    }

    pub fn load_with_hasher<D>(
        storage: Arc<MVCCStorage<D>>,
        large_value_hasher: fn(&[u8]) -> u64,
    ) -> Result<Self, EncodingError> {
        let read_snapshot = storage.clone().open_snapshot_read();
        let entity_types = read_snapshot
            .iterate_range(KeyRange::new_within(
                build_vertex_entity_type_prefix(),
                Prefix::VertexEntityType.fixed_width_keys(),
            ))
            .collect_cloned_vec(|k, _v| TypeVertex::new(Bytes::Reference(k.byte_ref())).type_id_().as_u16())
            .map_err(|err| EncodingError::ExistingTypesRead { source: err })?;
        let relation_types = read_snapshot
            .iterate_range(KeyRange::new_within(
                build_vertex_relation_type_prefix(),
                Prefix::VertexRelationType.fixed_width_keys(),
            ))
            .collect_cloned_vec(|k, _v| TypeVertex::new(Bytes::Reference(k.byte_ref())).type_id_().as_u16())
            .map_err(|err| EncodingError::ExistingTypesRead { source: err })?;
        read_snapshot.close_resources();

        let entity_ids = (0..=TypeIDUInt::MAX).map(|_| AtomicU64::new(0)).collect::<Box<[AtomicU64]>>();
        let relation_ids = (0..=TypeIDUInt::MAX).map(|_| AtomicU64::new(0)).collect::<Box<[AtomicU64]>>();
        for type_id in entity_types {
            let mut max_object_id =
                ObjectVertex::build_entity(TypeID::build(type_id), ObjectID::build(u64::MAX)).into_bytes().into_array();
            bytes::util::increment(max_object_id.bytes_mut()).unwrap();
            let next_storage_key: StorageKey<{ ObjectVertex::LENGTH }> =
                StorageKey::new_ref(ObjectVertex::KEYSPACE, max_object_id.as_ref());
            if let Some(prev_vertex) = storage.get_prev_raw(next_storage_key.as_reference(), Self::extract_object_id) {
                if prev_vertex.prefix() == Prefix::VertexEntity && prev_vertex.type_id_() == TypeID::build(type_id) {
                    entity_ids[type_id as usize].store(prev_vertex.object_id().as_u64() + 1, Ordering::Relaxed);
                }
            }
        }
        for type_id in relation_types {
            let mut max_object_id = ObjectVertex::build_relation(TypeID::build(type_id), ObjectID::build(u64::MAX))
                .into_bytes()
                .into_array();
            bytes::util::increment(max_object_id.bytes_mut()).unwrap();
            let next_storage_key: StorageKey<{ ObjectVertex::LENGTH }> =
                StorageKey::new_ref(ObjectVertex::KEYSPACE, max_object_id.as_ref());
            if let Some(prev_vertex) = storage.get_prev_raw(next_storage_key.as_reference(), Self::extract_object_id) {
                if prev_vertex.prefix() == Prefix::VertexRelation && prev_vertex.type_id_() == TypeID::build(type_id) {
                    relation_ids[type_id as usize].store(prev_vertex.object_id().as_u64() + 1, Ordering::Relaxed);
                }
            }
        }

        Ok(ThingVertexGenerator { entity_ids, relation_ids, large_value_hasher })
    }

    fn extract_object_id(k: &MVCCKey<'_>, _: &[u8]) -> ObjectVertex<'static> {
        ObjectVertex::new(Bytes::Array(ByteArray::copy(k.key())))
    }

    pub fn create_entity<D>(&self, type_id: TypeID, snapshot: &WriteSnapshot<D>) -> ObjectVertex<'static> {
        let entity_id = self.entity_ids[type_id.as_u16() as usize].fetch_add(1, Ordering::Relaxed);
        let vertex = ObjectVertex::build_entity(type_id, ObjectID::build(entity_id));
        snapshot.insert(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_relation<D>(&self, type_id: TypeID, snapshot: &WriteSnapshot<D>) -> ObjectVertex<'static> {
        let relation_id = self.relation_ids[type_id.as_u16() as usize].fetch_add(1, Ordering::Relaxed);
        let vertex = ObjectVertex::build_relation(type_id, ObjectID::build(relation_id));
        snapshot.insert(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_long<D>(
        &self,
        type_id: TypeID,
        value: LongBytes,
        snapshot: &WriteSnapshot<D>,
    ) -> AttributeVertex<'static> {
        let long_attribute_id = self.create_attribute_id_long(value);
        let vertex = AttributeVertex::build(ValueType::Long, type_id, AttributeID::Long(long_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_id_long(&self, value: LongBytes) -> LongAttributeID {
        LongAttributeID::build(value)
    }

    ///
    /// We create a unique attribute ID representing the string value.
    /// We guarantee that the same value will map the same ID as long as the value remains mapped, and concurrent creation
    ///   will lead to an isolation error to maintain this invariant. The user should retry.
    ///
    /// If the value is fully removed and recreated it is possible to get a different tail of the ID.
    ///
    /// We do not need to retain a reverse index from String -> ID, since 99.9% of the time the prefix + hash
    /// lets us retrieve the ID from the forward index by prefix (ID -> String).
    ///
    pub fn create_attribute_string<const INLINE_LENGTH: usize, D>(
        &self,
        type_id: TypeID,
        value: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &WriteSnapshot<D>,
    ) -> Result<AttributeVertex<'static>, Arc<SnapshotIteratorError>> {
        let string_attribute_id = self.create_attribute_id_string(type_id, value.as_reference(), snapshot)?;
        let vertex = AttributeVertex::build(ValueType::String, type_id, AttributeID::String(string_attribute_id));
        snapshot.put_val(vertex.as_storage_key().into_owned_array(), ByteArray::from(value.bytes()));
        Ok(vertex)
    }

    pub fn create_attribute_id_string<const INLINE_LENGTH: usize, D>(
        &self,
        type_id: TypeID,
        string: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &WriteSnapshot<D>,
    ) -> Result<StringAttributeID, Arc<SnapshotIteratorError>> {
        if string.length() <= StringAttributeID::ENCODING_INLINE_CAPACITY {
            Ok(StringAttributeID::build_inline_id(string))
        } else {
            let id = StringAttributeID::build_hashed_id(type_id, string, snapshot, &self.large_value_hasher)?;
            let hash = id.get_hash_prefix_hash();
            let lock = ByteArray::copy_concat([&type_id.bytes(), &hash]);
            snapshot.exclusive_lock_add(lock);
            Ok(id)
        }
    }

    pub fn find_attribute_id_string_noinline<const INLINE_LENGTH: usize>(
        &self,
        type_id: TypeID,
        string: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &impl ReadableSnapshot,
    ) -> Result<Option<StringAttributeID>, Arc<SnapshotIteratorError>> {
        assert!(!StringAttributeID::is_inlineable(string.as_reference()));
        StringAttributeID::find_hashed_id(type_id, string, snapshot, &self.large_value_hasher)
    }
}
