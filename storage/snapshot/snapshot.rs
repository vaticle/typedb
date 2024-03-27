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

use std::{collections::btree_map::Entry, error::Error, fmt, sync::Arc};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference};
use durability::{DurabilityService, SequenceNumber};
use primitive::prefix_range::PrefixRange;
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};

use super::{buffer::KeyspaceBuffers, iterator::SnapshotRangeIterator};
use crate::{
    error::MVCCStorageError,
    isolation_manager::CommitRecord,
    iterator::MVCCReadError,
    key_value::{StorageKey, StorageKeyArray, StorageKeyReference},
    snapshot::write::Write,
    MVCCStorage,
};

#[derive(Debug)]
pub enum Snapshot<'storage, D> {
    Read(ReadSnapshot<'storage, D>),
    Write(WriteSnapshot<'storage, D>),
}

impl<'storage, D> Snapshot<'storage, D> {
    pub fn get<const KS: usize>(
        &self,
        key: StorageKeyReference<'_>,
    ) -> Result<Option<ByteArray<KS>>, SnapshotGetError> {
        match self {
            Snapshot::Read(snapshot) => snapshot.get(key),
            Snapshot::Write(snapshot) => snapshot.get(key),
        }
    }

    pub fn get_mapped<T>(
        &self,
        key: StorageKeyReference<'_>,
        mapper: impl FnMut(ByteReference<'_>) -> T,
    ) -> Result<Option<T>, SnapshotGetError> {
        match self {
            Snapshot::Read(snapshot) => snapshot.get_mapped(key, mapper),
            Snapshot::Write(snapshot) => snapshot.get_mapped(key, mapper),
        }
    }

    pub fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: PrefixRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator<'this, PS> {
        match self {
            Snapshot::Read(snapshot) => snapshot.iterate_range(range),
            Snapshot::Write(snapshot) => snapshot.iterate_range(range),
        }
    }

    pub fn close(self) {
        match self {
            Snapshot::Read(snapshot) => snapshot.close_resources(),
            Snapshot::Write(snapshot) => snapshot.close_resources(),
        }
    }

    pub fn open_sequence_number(&self) -> SequenceNumber {
        match self {
            Snapshot::Read(snapshot) => snapshot.open_sequence_number,
            Snapshot::Write(snapshot) => snapshot.open_sequence_number,
        }
    }
}

#[derive(Debug)]
pub struct ReadSnapshot<'storage, D> {
    storage: &'storage MVCCStorage<D>,
    open_sequence_number: SequenceNumber,
}

impl<'storage, D> ReadSnapshot<'storage, D> {
    pub(crate) fn new(storage: &'storage MVCCStorage<D>, open_sequence_number: SequenceNumber) -> Self {
        // Note: for serialisability, we would need to register the open transaction to the IsolationManager
        ReadSnapshot { storage, open_sequence_number }
    }

    pub fn get<const KS: usize>(
        &self,
        key: StorageKeyReference<'_>,
    ) -> Result<Option<ByteArray<KS>>, SnapshotGetError> {
        // TODO: this clone may not be necessary - we could pass a reference up?
        self.storage
            .get(key, self.open_sequence_number, |reference| ByteArray::from(reference))
            .map_err(|error| SnapshotGetError::MVCCRead { source: error })
    }

    pub fn get_mapped<T>(
        &self,
        key: StorageKeyReference<'_>,
        mapper: impl FnMut(ByteReference<'_>) -> T,
    ) -> Result<Option<T>, SnapshotGetError> {
        self.storage
            .get(key, self.open_sequence_number, mapper)
            .map_err(|error| SnapshotGetError::MVCCRead { source: error })
    }

    pub fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: PrefixRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator<'this, PS> {
        let mvcc_iterator = self.storage.iterate_range(range, self.open_sequence_number);
        SnapshotRangeIterator::new(mvcc_iterator, None)
    }

    pub fn close_resources(self) {}
}

#[derive(Debug)]
pub struct WriteSnapshot<'storage, D> {
    storage: &'storage MVCCStorage<D>,
    buffers: KeyspaceBuffers,
    open_sequence_number: SequenceNumber,
}

impl<'storage, D> WriteSnapshot<'storage, D> {
    pub(crate) fn new(storage: &'storage MVCCStorage<D>, open_sequence_number: SequenceNumber) -> Self {
        storage.isolation_manager.opened(&open_sequence_number);
        WriteSnapshot { storage, buffers: KeyspaceBuffers::new(), open_sequence_number }
    }

    /// Insert a key with a new version
    pub fn insert(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        self.insert_val(key, ByteArray::empty())
    }

    pub fn insert_val(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>, value: ByteArray<BUFFER_VALUE_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.buffers.get(keyspace_id).insert(byte_array, value);
    }

    /// Insert a key with a new version if it does not already exist.
    /// If the key exists, mark it as a preexisting insertion to escalate to Insert if there is a concurrent Delete.
    pub fn put(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>) -> Result<(), SnapshotPutError> {
        self.put_val(key, ByteArray::empty())
    }

    pub fn put_val(
        &self,
        key: StorageKeyArray<BUFFER_KEY_INLINE>,
        value: ByteArray<BUFFER_VALUE_INLINE>,
    ) -> Result<(), SnapshotPutError> {
        let keyspace_id = key.keyspace_id();
        let buffer = self.buffers.get(keyspace_id);
        let mut writes = buffer.map().write().unwrap();
        match writes.entry(key.into_byte_array()) {
            Entry::Occupied(entry) => {
                let buffered = entry.into_mut();
                match buffered {
                    | Write::RequireExists { value: preexisting }
                    | Write::InsertPreexisting { value: preexisting, .. } => {
                        if &value != preexisting {
                            *buffered = Write::Insert { value }
                        }
                    }
                    Write::Insert { value: inserted } => *inserted = value, // TODO: should this read storage?
                    Write::Delete => *buffered = Write::Insert { value },
                }
            }
            Entry::Vacant(entry) => {
                let reference = ByteReference::new(entry.key().bytes());
                let wrapped = StorageKeyReference::new_raw(keyspace_id, reference);
                let existing_stored = self
                    .storage
                    .get(wrapped, self.open_sequence_number, |reference| {
                        // Only copy if the value is the same
                        (reference.bytes() == value.bytes()).then(|| ByteArray::from(reference))
                    })
                    .map_err(|error| SnapshotPutError::MVCCRead { source: error })?;
                if let Some(Some(existing_stored)) = existing_stored {
                    entry.insert(Write::InsertPreexisting { value: existing_stored, reinsert: Arc::default() });
                } else {
                    entry.insert(Write::Insert { value });
                }
            }
        }
        Ok(())
    }

    /// Insert a delete marker for the key with a new version
    pub fn delete(&self, key: StorageKeyArray<BUFFER_KEY_INLINE>) {
        let keyspace_id = key.keyspace_id();
        let byte_array = key.into_byte_array();
        self.buffers.get(keyspace_id).delete(byte_array);
    }

    /// Get a Value, and mark it as a required key
    pub fn get_required(
        &self,
        key: StorageKey<'_, BUFFER_KEY_INLINE>,
    ) -> Result<ByteArray<BUFFER_VALUE_INLINE>, SnapshotGetError> {
        let keyspace_id = key.keyspace_id();
        let buffer = self.buffers.get(keyspace_id);
        let existing = buffer.get(key.bytes());
        if let Some(existing) = existing {
            Ok(existing)
        } else {
            let storage_value = self
                .storage
                .get(key.as_reference(), self.open_sequence_number, |reference| ByteArray::from(reference))
                .map_err(|error| SnapshotGetError::MVCCRead { source: error })?;
            if let Some(value) = storage_value {
                buffer.require_exists(ByteArray::copy(key.bytes()), value.clone());
                Ok(value)
            } else {
                // TODO: what if the user concurrent requires a concept while deleting it in another query
                unreachable!("Require key exists in snapshot or in storage.");
            }
        }
    }

    /// Get the Value for the key, returning an empty Option if it does not exist
    pub fn get<const INLINE_BYTES: usize>(
        &self,
        key: StorageKeyReference<'_>,
    ) -> Result<Option<ByteArray<INLINE_BYTES>>, SnapshotGetError> {
        match self.buffers.get(key.keyspace_id()).get(key.bytes()) {
            None => self
                .storage
                .get(key, self.open_sequence_number, |reference| ByteArray::from(reference))
                .map_err(|error| SnapshotGetError::MVCCRead { source: error }),
            some => Ok(some),
        }
    }

    pub fn get_mapped<T>(
        &self,
        key: StorageKeyReference<'_>,
        mut mapper: impl FnMut(ByteReference<'_>) -> T,
    ) -> Result<Option<T>, SnapshotGetError> {
        match self.buffers.get(key.keyspace_id()).get::<BUFFER_VALUE_INLINE>(key.bytes()) {
            None => self
                .storage
                .get(key, self.open_sequence_number, mapper)
                .map_err(|error| SnapshotGetError::MVCCRead { source: error }),
            Some(value) => Ok(Some(mapper(ByteReference::from(&value)))),
        }
    }

    pub fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: PrefixRange<StorageKey<'this, PS>>,
    ) -> SnapshotRangeIterator<'this, PS> {
        let buffered_iterator = self
            .buffers
            .get(range.start().keyspace_id())
            .iterate_range(range.clone().map(|k| k.into_byte_array_or_ref()));
        let storage_iterator = self.storage.iterate_range(range, self.open_sequence_number);
        SnapshotRangeIterator::new(storage_iterator, Some(buffered_iterator))
    }

    pub fn commit(self) -> Result<(), SnapshotError>
    where
        D: DurabilityService,
    {
        if self.buffers.is_empty() {
            Ok(())
        } else {
            self.storage.snapshot_commit(self).map_err(|err| SnapshotError::Commit { source: err })
        }
    }

    pub(crate) fn into_commit_record(self) -> CommitRecord {
        CommitRecord::new(self.buffers, self.open_sequence_number)
    }

    pub(crate) fn open_sequence_number(&self) -> &SequenceNumber {
        &self.open_sequence_number
    }

    pub fn close_resources(&self) {
        self.storage.closed_snapshot_write(self.open_sequence_number());
    }
}

//  TODO: in the current version, we should need to close resouces on drop because we need to notify Isolation the txn is closed.
//        However in the next iteration of IsolationManager, we don't need to record readers at all.
//
// impl Drop for WriteSnapshot<'_> {
//     fn drop(&mut self) {
//         self.close_resources();
//     }
// }

#[derive(Debug)]
pub enum SnapshotError {
    Iterate { source: Arc<SnapshotError> },
    Get { source: MVCCStorageError },
    Put { source: MVCCStorageError },
    MVCC { source: MVCCReadError },
    Commit { source: MVCCStorageError },
}

impl fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Iterate { source, .. } => {
                write!(f, "SnapshotError::Iterate caused by: {}", source)
            }
            Self::Get { source, .. } => write!(f, "SnapshotError::Get caused by: {}", source),
            Self::Put { source, .. } => write!(f, "SnapshotError::Put caused by: {}", source),
            Self::MVCC { source, .. } => {
                write!(f, "SnapshotError::MVCC caused by: {}", source)
            }
            Self::Commit { source, .. } => {
                write!(f, "SnapshotError::Commit caused by: {}", source)
            }
        }
    }
}

impl Error for SnapshotError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Iterate { source, .. } => Some(source),
            Self::Get { source, .. } => Some(source),
            Self::Put { source, .. } => Some(source),
            Self::MVCC { source, .. } => Some(source),
            Self::Commit { source, .. } => Some(source),
        }
    }
}

#[derive(Debug)]
pub enum SnapshotPutError {
    MVCCRead { source: MVCCReadError },
}

impl fmt::Display for SnapshotPutError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for SnapshotPutError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::MVCCRead { source, .. } => Some(source),
        }
    }
}

#[derive(Debug)]
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
