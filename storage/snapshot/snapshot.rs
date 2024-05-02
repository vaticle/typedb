/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{error::Error, fmt, sync::Arc};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use durability::{DurabilityService, SequenceNumber};
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};

use super::{buffer::OperationsBuffer, iterator::SnapshotRangeIterator};
use crate::{
    isolation_manager::CommitRecord,
    iterator::MVCCReadError,
    key_range::KeyRange,
    key_value::{StorageKey, StorageKeyArray, StorageKeyReference},
    snapshot::{lock::LockType, write::Write},
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

    fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator<'this, PS>;

    fn any_in_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        buffered_only: bool,
    ) -> bool;

    // --- we are slightly breaking the abstraction and Rust model by mimicking polymorphism for the following methods ---
    fn get_buffered_write_mapped<T>(&self, key: StorageKeyReference<'_>, mapper: impl FnMut(&Write) -> T) -> Option<T>;
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
    ) -> SnapshotRangeIterator<'this, PS> {
        let mvcc_iterator = self.storage.iterate_range(range, self.open_sequence_number);
        SnapshotRangeIterator::new(mvcc_iterator, None)
    }

    fn any_in_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        buffered_only: bool,
    ) -> bool {
        !buffered_only && self.storage.iterate_range(range, self.open_sequence_number).next().is_some()
    }

    fn get_buffered_write_mapped<T>(
        &self,
        _key: StorageKeyReference<'_>,
        _mapper: impl FnMut(&Write) -> T,
    ) -> Option<T> {
        None
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

    pub(crate) fn operations(&self) -> &OperationsBuffer {
        &self.operations
    }

    /// Insert a key with a new version
    pub fn insert(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.insert_val(key, ByteArray::empty())
    }

    pub fn insert_val(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations().writes_in(keyspace_id).insert(byte_array, value);
    }

    /// Insert a key with a new version if it does not already exist.
    /// If the key exists, mark it as a preexisting insertion to escalate to Insert if there is a concurrent Delete.
    pub fn put(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.put_val(key, ByteArray::empty())
    }

    pub fn put_val(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations().writes_in(keyspace_id).put(byte_array, value);
    }

    /// Insert a delete marker for the key with a new version
    pub fn delete(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.operations().writes_in(keyspace_id).delete(byte_array);
    }

    /// Get a Value, and mark it as a required key
    pub fn get_required(
        &self,
        key: StorageKey<'_, BUFFER_KEY_INLINE>,
    ) -> Result<ByteArray<BUFFER_VALUE_INLINE>, SnapshotGetError> {
        let keyspace_id = key.keyspace_id();
        let writes = self.operations().writes_in(keyspace_id);
        let existing = writes.get(key.bytes());
        if let Some(existing) = existing {
            Ok(existing)
        } else {
            let storage_value = self.get_mapped(key.as_reference(), |reference| ByteArray::from(reference))?;
            if let Some(value) = storage_value {
                self.operations().lock_add(ByteArray::copy(key.bytes()), LockType::Unmodifiable);
                Ok(value)
            } else {
                // TODO: what if the user concurrent requires a concept while deleting it in another query
                unreachable!("Require key exists in snapshot or in storage.");
            }
        }
    }

    // TODO: technically we should never need this in a schema txn
    pub fn unmodifiable_lock_add(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.operations().lock_add(key.into_byte_array(), LockType::Unmodifiable)
    }

    pub fn unmodifiable_lock_remove(&self, key: &StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.operations().lock_remove(key.byte_array())
    }

    pub fn exclusive_lock_add(&self, key: ByteArray<BUFFER_KEY_INLINE>) {
        self.operations().lock_add(key, LockType::Exclusive)
    }

    pub fn iterate_writes(&self) -> impl Iterator<Item = (StorageKeyArray<64>, Write)> + '_ {
        self.operations().write_buffers().flat_map(|buffer| {
            // note: this currently copies all the buffers
            buffer
                .iterate_range(KeyRange::new_unbounded(Bytes::Array(ByteArray::<BUFFER_KEY_INLINE>::empty())))
                .into_range()
                .into_iter()
        })
    }

    pub fn iterate_writes_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<Bytes<'this, PS>>,
    ) -> impl Iterator<Item = (StorageKeyArray<64>, Write)> + '_ {
        self.operations()
            .write_buffers()
            .flat_map(move |buffer| buffer.iterate_range(range.clone()).into_range().into_iter())
    }

    pub fn close_resources(&self) {
        self.storage.closed_snapshot_write(self.open_sequence_number());
    }

    pub fn commit(self) -> Result<(), SnapshotError>
    where
        D: DurabilityService,
    {
        if self.operations.writes_empty() && self.operations.locks_empty() {
            Ok(())
        } else {
            self.storage.clone().snapshot_commit(self).map_err(|error| SnapshotError::Commit { source: error })
        }
    }

    pub(crate) fn into_commit_record(self) -> CommitRecord {
        CommitRecord::new(self.operations, self.open_sequence_number)
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
        match self.operations.writes_in(key.keyspace_id()).get(key.bytes()) {
            Some(bytes) => Ok(Some(bytes)),
            None => self
                .storage
                .get(key, self.open_sequence_number)
                .map_err(|error| SnapshotGetError::MVCCRead { source: error }),
        }
    }

    fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator<'this, PS> {
        let buffered_iterator = self
            .operations
            .writes_in(range.start().keyspace_id())
            .iterate_range(range.clone().map(|k| k.into_byte_array_or_ref(), |fixed| fixed));
        let storage_iterator = self.storage.iterate_range(range, self.open_sequence_number);
        SnapshotRangeIterator::new(storage_iterator, Some(buffered_iterator))
    }

    fn any_in_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        buffered_only: bool,
    ) -> bool {
        let buffered = self
            .operations
            .writes_in(range.start().keyspace_id())
            .any_in_range(range.clone().map(|k| k.into_byte_array_or_ref(), |fixed| fixed));
        buffered || (!buffered_only && self.storage.iterate_range(range, self.open_sequence_number).next().is_some())
    }

    fn get_buffered_write_mapped<T>(&self, key: StorageKeyReference<'_>, mapper: impl FnMut(&Write) -> T) -> Option<T> {
        self.operations().writes_in(key.keyspace_id()).get_write_mapped(key.byte_ref(), mapper)
    }
}

#[derive(Debug)]
pub enum SnapshotError {
    Commit { source: StorageCommitError },
}

impl fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Commit { source, .. } => write!(f, "SnapshotError::Commit caused by: {}", source),
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
        }
    }
}
