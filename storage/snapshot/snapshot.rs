/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{error::Error, fmt, iter::empty, sync::Arc};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use lending_iterator::LendingIterator;
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};

use crate::{
    durability_client::DurabilityClient,
    isolation_manager::{CommitRecord, CommitType},
    iterator::MVCCReadError,
    key_range::KeyRange,
    key_value::{StorageKey, StorageKeyArray, StorageKeyReference},
    sequence_number::SequenceNumber,
    snapshot::{
        buffer::{BufferRangeIterator, OperationsBuffer},
        iterator::SnapshotRangeIterator,
        lock::LockType,
        write::Write,
    },
    MVCCStorage, StorageCommitError,
};

pub trait ReadableSnapshot {
    fn open_sequence_number(&self) -> SequenceNumber;

    fn get<const INLINE_BYTES: usize>(
        &self,
        key: StorageKeyReference<'_>,
    ) -> Result<Option<ByteArray<INLINE_BYTES>>, SnapshotGetError>;

    fn get_mapped<T>(
        &self,
        key: StorageKeyReference<'_>,
        mut mapper: impl FnMut(ByteReference<'_>) -> T,
    ) -> Result<Option<T>, SnapshotGetError> {
        let value = self.get::<BUFFER_VALUE_INLINE>(key)?;
        Ok(value.map(|bytes| mapper(bytes.as_ref())))
    }

    fn iterate_range<const PS: usize>(&self, range: KeyRange<StorageKey<'_, PS>>) -> SnapshotRangeIterator;

    fn any_in_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        buffered_only: bool,
    ) -> bool;

    // --- we are slightly breaking the abstraction and Rust model by mimicking polymorphism for the following methods ---
    fn get_buffered_write(&self, key: StorageKeyReference<'_>) -> Option<&Write>;

    fn iterate_buffered_writes(&self) -> impl Iterator<Item = (StorageKeyArray<BUFFER_KEY_INLINE>, Write)> + '_;

    fn iterate_buffered_writes_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> BufferRangeIterator;
}

pub trait WritableSnapshot: ReadableSnapshot {
    fn operations(&self) -> &OperationsBuffer;

    fn operations_mut(&mut self) -> &mut OperationsBuffer;

    /// Insert a key with a new version
    fn insert(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.insert_val(key, ByteArray::empty())
    }

    fn insert_val(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations_mut().writes_in_mut(keyspace_id).insert(byte_array, value);
    }

    /// Insert a key with a new version
    fn uninsert(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.uninsert_val(key, ByteArray::empty())
    }

    fn uninsert_val(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations_mut().writes_in_mut(keyspace_id).uninsert(byte_array, value);
    }

    /// Insert a key with a new version if it does not already exist.
    /// If the key exists, mark it as a preexisting insertion to escalate to Insert if there is a concurrent Delete.
    fn put(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.put_val(key, ByteArray::empty())
    }

    fn put_val(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations_mut().writes_in_mut(keyspace_id).put(byte_array, value);
    }

    fn unput(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.unput_val(key, ByteArray::empty())
    }

    fn unput_val(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations_mut().writes_in_mut(keyspace_id).unput(byte_array, value);
    }

    /// Insert a delete marker for the key with a new version
    fn delete(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations_mut().writes_in_mut(keyspace_id).delete(byte_array);
    }

    /// Get a Value, and mark it as a required key
    fn get_required(
        &mut self,
        key: StorageKey<'_, BUFFER_KEY_INLINE>,
    ) -> Result<ByteArray<BUFFER_VALUE_INLINE>, SnapshotGetError> {
        let keyspace_id = key.keyspace_id();
        let writes = self.operations().writes_in(keyspace_id);
        match writes.get(key.bytes()) {
            Some(Write::Insert { value, .. }) | Some(Write::Put { value, .. }) => Ok(ByteArray::copy(value.bytes())),
            Some(Write::Delete) => {
                Err(SnapshotGetError::ExpectedRequiredKeyToExist { key: StorageKey::Array(key.into_owned_array()) })
            }
            None => {
                let storage_value = self.get_mapped(key.as_reference(), |reference| ByteArray::from(reference))?;
                if let Some(value) = storage_value {
                    self.operations_mut().lock_add(ByteArray::copy(key.bytes()), LockType::Unmodifiable);
                    Ok(value)
                } else {
                    Err(SnapshotGetError::ExpectedRequiredKeyToExist { key: StorageKey::Array(key.into_owned_array()) })
                }
            }
        }
    }

    // TODO: technically we should never need this in a schema txn
    fn unmodifiable_lock_add(&mut self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.operations_mut().lock_add(key.into_byte_array(), LockType::Unmodifiable)
    }

    fn unmodifiable_lock_remove(&mut self, key: &StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.operations_mut().lock_remove(key.byte_array())
    }

    fn exclusive_lock_add(&mut self, key: ByteArray<BUFFER_KEY_INLINE>) {
        self.operations_mut().lock_add(key, LockType::Exclusive)
    }

    fn iterate_writes(&self) -> impl Iterator<Item = (StorageKeyArray<BUFFER_KEY_INLINE>, Write)> + '_ {
        self.operations().write_buffers().flat_map(|buffer| {
            // note: this currently copies all the buffers
            buffer
                .iterate_range(KeyRange::new_unbounded(Bytes::Array(ByteArray::<BUFFER_KEY_INLINE>::empty())))
                .into_iter()
        })
    }

    fn iterate_writes_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<Bytes<'this, PS>>,
    ) -> impl Iterator<Item = (StorageKeyArray<BUFFER_KEY_INLINE>, Write)> + '_ {
        self.operations().write_buffers().flat_map(move |buffer| buffer.iterate_range(range.clone()).into_iter())
    }

    fn close_resources(&self);
}

pub trait CommittableSnapshot<D>: WritableSnapshot
where
    D: DurabilityClient,
{
    fn commit(self) -> Result<Option<SequenceNumber>, SnapshotError>;

    fn into_commit_record(self) -> CommitRecord;
}

#[derive(Debug)]
pub struct ReadSnapshot<D> {
    storage: Arc<MVCCStorage<D>>,
    open_sequence_number: SequenceNumber,
}

impl<D> ReadSnapshot<D> {
    pub(crate) fn new(storage: Arc<MVCCStorage<D>>, open_sequence_number: SequenceNumber) -> Self {
        // Note: for serialisability, we would need to register the open transaction to the IsolationManager
        ReadSnapshot { storage, open_sequence_number }
    }

    pub fn close_resources(self) {}
}

impl<D> ReadableSnapshot for ReadSnapshot<D> {
    fn open_sequence_number(&self) -> SequenceNumber {
        self.open_sequence_number
    }

    fn get<const INLINE_BYTES: usize>(
        &self,
        key: StorageKeyReference<'_>,
    ) -> Result<Option<ByteArray<INLINE_BYTES>>, SnapshotGetError> {
        self.storage.get(key, self.open_sequence_number).map_err(|error| SnapshotGetError::MVCCRead { source: error })
    }

    fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator {
        let mvcc_iterator = self.storage.iterate_range(range, self.open_sequence_number);
        SnapshotRangeIterator::new(mvcc_iterator, BufferRangeIterator::empty())
    }

    fn any_in_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        buffered_only: bool,
    ) -> bool {
        !buffered_only && self.storage.iterate_range(range, self.open_sequence_number).next().is_some()
    }

    fn get_buffered_write(&self, _: StorageKeyReference<'_>) -> Option<&Write> {
        None
    }

    fn iterate_buffered_writes(&self) -> impl Iterator<Item = (StorageKeyArray<BUFFER_KEY_INLINE>, Write)> + '_ {
        empty()
    }

    fn iterate_buffered_writes_range<'this, const PS: usize>(
        &'this self,
        _: KeyRange<StorageKey<'this, PS>>,
    ) -> BufferRangeIterator {
        BufferRangeIterator::empty()
    }
}

#[derive(Debug)]
pub struct WriteSnapshot<D> {
    storage: Arc<MVCCStorage<D>>,
    operations: OperationsBuffer,
    open_sequence_number: SequenceNumber,
}

impl<D> WriteSnapshot<D> {
    pub(crate) fn new(storage: Arc<MVCCStorage<D>>, open_sequence_number: SequenceNumber) -> Self {
        storage.isolation_manager.opened_for_read(open_sequence_number);
        WriteSnapshot { storage, operations: OperationsBuffer::new(), open_sequence_number }
    }

    pub fn new_with_operations(
        storage: Arc<MVCCStorage<D>>,
        open_sequence_number: SequenceNumber,
        operations: OperationsBuffer,
    ) -> impl ReadableSnapshot {
        WriteSnapshot { storage, operations, open_sequence_number }
    }
}

impl<D> ReadableSnapshot for WriteSnapshot<D> {
    fn open_sequence_number(&self) -> SequenceNumber {
        self.open_sequence_number
    }

    /// Get the Value for the key, returning an empty Option if it does not exist
    fn get<const INLINE_BYTES: usize>(
        &self,
        key: StorageKeyReference<'_>,
    ) -> Result<Option<ByteArray<INLINE_BYTES>>, SnapshotGetError> {
        let writes = self.operations().writes_in(key.keyspace_id());
        match writes.get(key.bytes()) {
            Some(Write::Insert { value, .. }) | Some(Write::Put { value, .. }) => {
                Ok(Some(ByteArray::copy(value.bytes())))
            }
            Some(Write::Delete) => Ok(None),
            None => self
                .storage
                .get(key, self.open_sequence_number)
                .map_err(|error| SnapshotGetError::MVCCRead { source: error }),
        }
    }

    fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator {
        let buffered_iterator = self
            .operations
            .writes_in(range.start().keyspace_id())
            .iterate_range(range.clone().map(|k| k.into_bytes(), |fixed| fixed));
        let storage_iterator = self.storage.iterate_range(range, self.open_sequence_number);
        SnapshotRangeIterator::new(storage_iterator, buffered_iterator)
    }

    fn any_in_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        buffered_only: bool,
    ) -> bool {
        let buffered = self
            .operations
            .writes_in(range.start().keyspace_id())
            .any_in_range(range.clone().map(|k| k.into_bytes(), |fixed| fixed));
        buffered || (!buffered_only && self.storage.iterate_range(range, self.open_sequence_number).next().is_some())
    }

    fn get_buffered_write(&self, key: StorageKeyReference<'_>) -> Option<&Write> {
        self.operations().writes_in(key.keyspace_id()).get_write(key.byte_ref())
    }

    fn iterate_buffered_writes(&self) -> impl Iterator<Item = (StorageKeyArray<BUFFER_KEY_INLINE>, Write)> + '_ {
        self.operations().iterate_writes()
    }

    fn iterate_buffered_writes_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> BufferRangeIterator {
        debug_assert!(range
            .end()
            .get_value()
            .map(|end| end.keyspace_id() == range.start().keyspace_id())
            .unwrap_or(true));
        self.operations()
            .writes_in(range.start().keyspace_id())
            .iterate_range(range.map(|k| k.into_bytes(), |fixed| fixed))
    }
}

impl<D> WritableSnapshot for WriteSnapshot<D> {
    fn operations(&self) -> &OperationsBuffer {
        &self.operations
    }

    fn operations_mut(&mut self) -> &mut OperationsBuffer {
        &mut self.operations
    }

    fn close_resources(&self) {
        self.storage.closed_snapshot_write(self.open_sequence_number());
    }
}

impl<D: DurabilityClient> CommittableSnapshot<D> for WriteSnapshot<D> {
    fn commit(self) -> Result<Option<SequenceNumber>, SnapshotError> {
        if self.operations.is_writes_empty() && self.operations.locks_empty() {
            Ok(None)
        } else {
            match self.storage.clone().snapshot_commit(self) {
                Ok(sequence_number) => Ok(Some(sequence_number)),
                Err(error) => Err(SnapshotError::Commit { source: error }),
            }
        }
    }

    fn into_commit_record(self) -> CommitRecord {
        CommitRecord::new(self.operations, self.open_sequence_number, CommitType::Data)
    }
}

#[derive(Debug)]
pub struct SchemaSnapshot<D> {
    storage: Arc<MVCCStorage<D>>,
    operations: OperationsBuffer,
    open_sequence_number: SequenceNumber,
}

impl<D> SchemaSnapshot<D> {
    pub(crate) fn new(storage: Arc<MVCCStorage<D>>, open_sequence_number: SequenceNumber) -> Self {
        storage.isolation_manager.opened_for_read(open_sequence_number);
        SchemaSnapshot { storage, operations: OperationsBuffer::new(), open_sequence_number }
    }

    pub fn new_with_operations(
        storage: Arc<MVCCStorage<D>>,
        open_sequence_number: SequenceNumber,
        operations: OperationsBuffer,
    ) -> impl ReadableSnapshot {
        SchemaSnapshot { storage, operations, open_sequence_number }
    }
}

impl<D> ReadableSnapshot for SchemaSnapshot<D> {
    fn open_sequence_number(&self) -> SequenceNumber {
        self.open_sequence_number
    }

    /// Get the Value for the key, returning an empty Option if it does not exist
    fn get<const INLINE_BYTES: usize>(
        &self,
        key: StorageKeyReference<'_>,
    ) -> Result<Option<ByteArray<INLINE_BYTES>>, SnapshotGetError> {
        let writes = self.operations().writes_in(key.keyspace_id());
        match writes.get(key.bytes()) {
            Some(Write::Insert { value, .. }) | Some(Write::Put { value, .. }) => {
                Ok(Some(ByteArray::copy(value.bytes())))
            }
            Some(Write::Delete) => Ok(None),
            None => self
                .storage
                .get(key, self.open_sequence_number)
                .map_err(|error| SnapshotGetError::MVCCRead { source: error }),
        }
    }

    fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator {
        let buffered_iterator = self
            .operations
            .writes_in(range.start().keyspace_id())
            .iterate_range(range.clone().map(|k| k.into_bytes(), |fixed| fixed));
        let storage_iterator = self.storage.iterate_range(range, self.open_sequence_number);
        SnapshotRangeIterator::new(storage_iterator, buffered_iterator)
    }

    fn any_in_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        buffered_only: bool,
    ) -> bool {
        let buffered = self
            .operations
            .writes_in(range.start().keyspace_id())
            .any_in_range(range.clone().map(|k| k.into_bytes(), |fixed| fixed));
        buffered || (!buffered_only && self.storage.iterate_range(range, self.open_sequence_number).next().is_some())
    }

    fn get_buffered_write(&self, key: StorageKeyReference<'_>) -> Option<&Write> {
        self.operations().writes_in(key.keyspace_id()).get_write(key.byte_ref())
    }

    fn iterate_buffered_writes(&self) -> impl Iterator<Item = (StorageKeyArray<BUFFER_KEY_INLINE>, Write)> + '_ {
        self.operations().iterate_writes()
    }

    fn iterate_buffered_writes_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> BufferRangeIterator {
        debug_assert!(range
            .end()
            .get_value()
            .map(|end| end.keyspace_id() == range.start().keyspace_id())
            .unwrap_or(true));
        self.operations()
            .writes_in(range.start().keyspace_id())
            .iterate_range(range.map(|k| k.into_bytes(), |fixed| fixed))
    }
}

impl<D> WritableSnapshot for SchemaSnapshot<D> {
    fn operations(&self) -> &OperationsBuffer {
        &self.operations
    }

    fn operations_mut(&mut self) -> &mut OperationsBuffer {
        &mut self.operations
    }

    fn close_resources(&self) {
        self.storage.closed_snapshot_write(self.open_sequence_number());
    }
}

impl<D: DurabilityClient> CommittableSnapshot<D> for SchemaSnapshot<D> {
    // TODO: extract these two methods into separate trait
    fn commit(self) -> Result<Option<SequenceNumber>, SnapshotError> {
        if self.operations.is_writes_empty() && self.operations.locks_empty() {
            Ok(None)
        } else {
            match self.storage.clone().snapshot_commit(self) {
                Ok(sequence_number) => Ok(Some(sequence_number)),
                Err(error) => Err(SnapshotError::Commit { source: error }),
            }
        }
    }

    fn into_commit_record(self) -> CommitRecord {
        CommitRecord::new(self.operations, self.open_sequence_number, CommitType::Schema)
    }
}

#[derive(Debug)]
pub enum SnapshotError {
    Commit { source: StorageCommitError },
}

impl fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Commit { source, .. } => {
                write!(f, "SnapshotError::Commit caused by: {}", source)
            }
        }
    }
}

impl Error for SnapshotError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Commit { source, .. } => Some(source),
        }
    }
}

#[derive(Debug, Clone)]
pub enum SnapshotGetError {
    MVCCRead { source: MVCCReadError },
    ExpectedRequiredKeyToExist { key: StorageKey<'static, BUFFER_KEY_INLINE> },
}

impl fmt::Display for SnapshotGetError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for SnapshotGetError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::MVCCRead { source, .. } => Some(source),
            SnapshotGetError::ExpectedRequiredKeyToExist { .. } => None,
        }
    }
}
