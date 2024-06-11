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
    snapshot::{iterator::SnapshotIteratorError, ReadableSnapshot, WritableSnapshot},
    MVCCKey, MVCCStorage,
};

use super::vertex_attribute::{
    BooleanAttributeID, DateAttributeID, DateTimeAttributeID, DateTimeTZAttributeID, DecimalAttributeID, DoubleAttributeID, DurationAttributeID, StructAttributeID
};
use crate::{
    error::EncodingError,
    graph::{
        thing::{
            vertex_attribute::{AttributeID, AttributeVertex, LongAttributeID, StringAttributeID},
            vertex_object::{ObjectID, ObjectVertex},
        },
        type_::vertex::{build_type_vertex_prefix_key, TypeID, TypeIDUInt, TypeVertex},
        Typed,
    },
    layout::prefix::Prefix,
    value::{
        boolean_bytes::BooleanBytes, date_bytes::DateBytes, date_time_bytes::DateTimeBytes, date_time_tz_bytes::DateTimeTZBytes, decimal_bytes::DecimalBytes, double_bytes::DoubleBytes, duration_bytes::DurationBytes, long_bytes::LongBytes, string_bytes::StringBytes, struct_bytes::StructBytes, value_type::ValueTypeCategory
    },
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
                build_type_vertex_prefix_key(Prefix::VertexEntityType),
                Prefix::VertexEntityType.fixed_width_keys(),
            ))
            .collect_cloned_vec(|k, _v| TypeVertex::new(Bytes::Reference(k.byte_ref())).type_id_().as_u16())
            .map_err(|err| EncodingError::ExistingTypesRead { source: err })?;
        let relation_types = read_snapshot
            .iterate_range(KeyRange::new_within(
                build_type_vertex_prefix_key(Prefix::VertexRelationType),
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

    pub fn hasher(&self) -> &impl Fn(&[u8]) -> u64 {
        &self.large_value_hasher
    }

    fn extract_object_id(k: &MVCCKey<'_>, _: &[u8]) -> ObjectVertex<'static> {
        ObjectVertex::new(Bytes::Array(ByteArray::copy(k.key())))
    }

    pub fn create_entity<Snapshot>(&self, type_id: TypeID, snapshot: &mut Snapshot) -> ObjectVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let entity_id = self.entity_ids[type_id.as_u16() as usize].fetch_add(1, Ordering::Relaxed);
        let vertex = ObjectVertex::build_entity(type_id, ObjectID::build(entity_id));
        snapshot.insert(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_relation<Snapshot>(&self, type_id: TypeID, snapshot: &mut Snapshot) -> ObjectVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let relation_id = self.relation_ids[type_id.as_u16() as usize].fetch_add(1, Ordering::Relaxed);
        let vertex = ObjectVertex::build_relation(type_id, ObjectID::build(relation_id));
        snapshot.insert(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_boolean<Snapshot>(
        &self,
        type_id: TypeID,
        value: BooleanBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let boolean_attribute_id = self.create_attribute_id_boolean(value);
        let vertex =
            AttributeVertex::build(ValueTypeCategory::Boolean, type_id, AttributeID::Boolean(boolean_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_long<Snapshot>(
        &self,
        type_id: TypeID,
        value: LongBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let long_attribute_id = self.create_attribute_id_long(value);
        let vertex = AttributeVertex::build(ValueTypeCategory::Long, type_id, AttributeID::Long(long_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_double<Snapshot>(
        &self,
        type_id: TypeID,
        value: DoubleBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let double_attribute_id = self.create_attribute_id_double(value);
        let vertex =
            AttributeVertex::build(ValueTypeCategory::Double, type_id, AttributeID::Double(double_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_decimal<Snapshot>(
        &self,
        type_id: TypeID,
        value: DecimalBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let decimal_attribute_id = self.create_attribute_id_decimal(value);
        let vertex =
            AttributeVertex::build(ValueTypeCategory::Decimal, type_id, AttributeID::Decimal(decimal_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_date<Snapshot>(
        &self,
        type_id: TypeID,
        value: DateBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let date_attribute_id = self.create_attribute_id_date(value);
        let vertex = AttributeVertex::build(ValueTypeCategory::Date, type_id, AttributeID::Date(date_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_date_time<Snapshot>(
        &self,
        type_id: TypeID,
        value: DateTimeBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let date_time_attribute_id = self.create_attribute_id_date_time(value);
        let vertex =
            AttributeVertex::build(ValueTypeCategory::DateTime, type_id, AttributeID::DateTime(date_time_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_date_time_tz<Snapshot>(
        &self,
        type_id: TypeID,
        value: DateTimeTZBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let date_time_tz_attribute_id = self.create_attribute_id_date_time_tz(value);
        let vertex = AttributeVertex::build(
            ValueTypeCategory::DateTimeTZ,
            type_id,
            AttributeID::DateTimeTZ(date_time_tz_attribute_id),
        );
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_duration<Snapshot>(
        &self,
        type_id: TypeID,
        value: DurationBytes,
        snapshot: &mut Snapshot,
    ) -> AttributeVertex<'static>
    where
        Snapshot: WritableSnapshot,
    {
        let duration_attribute_id = self.create_attribute_id_duration(value);
        let vertex =
            AttributeVertex::build(ValueTypeCategory::Duration, type_id, AttributeID::Duration(duration_attribute_id));
        snapshot.put(vertex.as_storage_key().into_owned_array());
        vertex
    }

    pub fn create_attribute_id_boolean(&self, value: BooleanBytes) -> BooleanAttributeID {
        BooleanAttributeID::build(value)
    }

    pub fn create_attribute_id_long(&self, value: LongBytes) -> LongAttributeID {
        LongAttributeID::build(value)
    }

    pub fn create_attribute_id_double(&self, value: DoubleBytes) -> DoubleAttributeID {
        DoubleAttributeID::build(value)
    }

    pub fn create_attribute_id_decimal(&self, value: DecimalBytes) -> DecimalAttributeID {
        DecimalAttributeID::build(value)
    }

    pub fn create_attribute_id_date(&self, value: DateBytes) -> DateAttributeID {
        DateAttributeID::build(value)
    }

    pub fn create_attribute_id_date_time(&self, value: DateTimeBytes) -> DateTimeAttributeID {
        DateTimeAttributeID::build(value)
    }

    pub fn create_attribute_id_date_time_tz(&self, value: DateTimeTZBytes) -> DateTimeTZAttributeID {
        DateTimeTZAttributeID::build(value)
    }

    pub fn create_attribute_id_duration(&self, value: DurationBytes) -> DurationAttributeID {
        DurationAttributeID::build(value)
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
    pub fn create_attribute_string<const INLINE_LENGTH: usize, Snapshot>(
        &self,
        type_id: TypeID,
        value: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &mut Snapshot,
    ) -> Result<AttributeVertex<'static>, Arc<SnapshotIteratorError>>
    where
        Snapshot: WritableSnapshot,
    {
        let string_attribute_id = self.create_attribute_id_string(type_id, value.as_reference(), snapshot)?;
        let vertex =
            AttributeVertex::build(ValueTypeCategory::String, type_id, AttributeID::String(string_attribute_id));
        snapshot.put_val(vertex.as_storage_key().into_owned_array(), ByteArray::from(value.bytes()));
        Ok(vertex)
    }

    pub fn create_attribute_id_string<const INLINE_LENGTH: usize, Snapshot>(
        &self,
        type_id: TypeID,
        string: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &mut Snapshot,
    ) -> Result<StringAttributeID, Arc<SnapshotIteratorError>>
    where
        Snapshot: WritableSnapshot,
    {
        if StringAttributeID::is_inlineable(string.as_reference()) {
            Ok(StringAttributeID::build_inline_id(string))
        } else {
            let id = StringAttributeID::build_hashed_id(type_id, string, snapshot, &self.large_value_hasher)?;
            let hash = id.get_hash_prefix_hash();
            let lock =
                ByteArray::copy_concat([&Prefix::VertexAttributeString.prefix_id().bytes(), &type_id.bytes(), &hash]);
            snapshot.exclusive_lock_add(lock);
            Ok(id)
        }
    }

    pub fn find_attribute_id_string_noinline<const INLINE_LENGTH: usize, Snapshot>(
        &self,
        type_id: TypeID,
        string: StringBytes<'_, INLINE_LENGTH>,
        snapshot: &Snapshot,
    ) -> Result<Option<StringAttributeID>, Arc<SnapshotIteratorError>>
    where
        Snapshot: ReadableSnapshot,
    {
        assert!(!StringAttributeID::is_inlineable(string.as_reference()));
        StringAttributeID::find_hashed_id(type_id, string, snapshot, &self.large_value_hasher)
    }

    pub fn create_attribute_struct<const INLINE_LENGTH: usize, Snapshot>(
        &self,
        type_id: TypeID,
        value: StructBytes<'_, INLINE_LENGTH>,
        snapshot: &mut Snapshot,
    ) -> Result<AttributeVertex<'static>, Arc<SnapshotIteratorError>>
    where
        Snapshot: WritableSnapshot,
    {
        let struct_attribute_id = self.create_attribute_id_struct(type_id, value.as_reference(), snapshot)?;
        let vertex =
            AttributeVertex::build(ValueTypeCategory::Struct, type_id, AttributeID::Struct(struct_attribute_id));
        snapshot.put_val(vertex.as_storage_key().into_owned_array(), ByteArray::from(value.bytes()));
        Ok(vertex)
    }

    pub fn create_attribute_id_struct<const INLINE_LENGTH: usize, Snapshot>(
        &self,
        type_id: TypeID,
        struct_bytes: StructBytes<'_, INLINE_LENGTH>,
        snapshot: &mut Snapshot,
    ) -> Result<StructAttributeID, Arc<SnapshotIteratorError>>
    where
        Snapshot: WritableSnapshot,
    {
        // We don't inline structs
        let id = StructAttributeID::build_hashed_id(type_id, struct_bytes, snapshot, &self.large_value_hasher)?;
        let hash = id.get_hash_hash();
        let lock =
            ByteArray::copy_concat([&Prefix::VertexAttributeStruct.prefix_id().bytes(), &type_id.bytes(), &hash]);
        snapshot.exclusive_lock_add(lock);
        Ok(id)
    }

    pub fn find_attribute_id_struct<const INLINE_LENGTH: usize, Snapshot>(
        &self,
        type_id: TypeID,
        struct_bytes: StructBytes<'_, INLINE_LENGTH>,
        snapshot: &Snapshot,
    ) -> Result<Option<StructAttributeID>, Arc<SnapshotIteratorError>>
    where
        Snapshot: ReadableSnapshot,
    {
        StructAttributeID::find_hashed_id(type_id, struct_bytes, snapshot, &self.large_value_hasher)
    }
}
