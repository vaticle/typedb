/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]
#![deny(elided_lifetimes_in_paths)]
#![allow(dead_code)]
#![allow(clippy::module_inception)]

use std::{
    error::Error,
    fmt, fs, io,
    path::{Path, PathBuf},
    sync::{atomic::Ordering, Arc},
};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use checkpoint::{Checkpoint, CheckpointCreateError, CheckpointLoadError};
use durability::{DurabilityError, DurabilityService, SequenceNumber};
use isolation_manager::IsolationConflict;
use iterator::MVCCReadError;
use itertools::Itertools;
use keyspace::KeyspaceDeleteError;
use logger::{error, result::ResultExt};
use resource::constants::snapshot::BUFFER_VALUE_INLINE;

use crate::{
    error::{MVCCStorageError, MVCCStorageErrorKind},
    isolation_manager::{CommitRecord, IsolationManager, StatusRecord, ValidatedCommit},
    iterator::MVCCRangeIterator,
    key_range::KeyRange,
    key_value::{StorageKey, StorageKeyReference},
    keyspace::{iterator::KeyspaceRangeIterator, Keyspace, KeyspaceError, KeyspaceId, KeyspaceSet, Keyspaces},
    snapshot::{write::Write, ReadSnapshot, ReadableSnapshot, WriteSnapshot},
};

mod checkpoint;
pub mod error;
pub mod isolation_manager;
pub mod iterator;
pub mod key_range;
pub mod key_value;
pub mod keyspace;
pub mod snapshot;
mod write_batches;

#[derive(Debug)]
pub struct MVCCStorage<Durability> {
    name: String,
    path: PathBuf,
    keyspaces: Keyspaces,
    durability_service: Durability,
    isolation_manager: IsolationManager,
}

impl<Durability> MVCCStorage<Durability> {
    const WAL_DIR_NAME: &'static str = "wal";
    const STORAGE_DIR_NAME: &'static str = "storage";

    pub fn open<KS: KeyspaceSet>(name: impl AsRef<str>, path: &Path) -> Result<Self, StorageOpenError>
    where
        Durability: DurabilityService,
    {
        use StorageOpenError::{CheckpointCreate, CheckpointLoad, DurabilityServiceOpen, StorageDirectoryCreate};

        let name = name.as_ref();
        let storage_dir = path.join(Self::STORAGE_DIR_NAME);
        if storage_dir.exists() {
            fs::remove_dir_all(&storage_dir)
                .map_err(|error| StorageDirectoryCreate { name: name.to_owned(), source: error })?;
        }
        fs::create_dir_all(&storage_dir)
            .map_err(|error| StorageDirectoryCreate { name: name.to_owned(), source: error })?;

        let mut durability_service = Durability::open(path.join(Self::WAL_DIR_NAME))
            .map_err(|error| DurabilityServiceOpen { name: name.to_owned(), source: error })?;
        durability_service.register_record_type::<CommitRecord>();
        durability_service.register_record_type::<StatusRecord>();

        let checkpoint = Checkpoint::load::<KS, _>(path, &durability_service)
            .map_err(|error| CheckpointLoad { name: name.to_owned(), source: error })?;

        let keyspaces = checkpoint.keyspaces;
        let next_sequence_number = checkpoint.next_sequence_number;
        let isolation_manager = IsolationManager::new(next_sequence_number);

        // TODO only create new checkpoint if recovery happened
        Checkpoint::create(next_sequence_number - 1, path, &keyspaces)
            .map_err(|error| CheckpointCreate { name: name.to_owned(), source: error })?;

        Ok(Self { name: name.to_owned(), path: path.to_owned(), durability_service, keyspaces, isolation_manager })
    }

    fn name(&self) -> &str {
        &self.name
    }

    pub fn open_snapshot_read(self: Arc<Self>) -> ReadSnapshot<Durability> {
        let open_sequence_number = self.isolation_manager.watermark();
        ReadSnapshot::new(self, open_sequence_number)
    }

    pub fn open_snapshot_read_at(
        self: Arc<Self>,
        sequence_number: SequenceNumber,
    ) -> Result<ReadSnapshot<Durability>, ReadSnapshotOpenError> {
        // TODO: Support waiting for watermark to catch up to sequence number when we support causal reading.
        assert!(sequence_number <= self.read_watermark());
        Ok(ReadSnapshot::new(self, sequence_number))
    }

    pub fn open_snapshot_write(self: Arc<Self>) -> WriteSnapshot<Durability> {
        /*
        How to pick a sequence number:

        TXN 1 - open(0) ---> durably write = 10 PENDING ---> validate ---> write ---> committed. RETURN

        Question: does external consistency make sense for single-node machines?
        If user opens TXN 10 in thread 1, thread 2... work. User expects if open TXN after TXN 10 returns, we will see it. Otherwise, no expectations.
        Therefore - we can always use the last committed state safely for happens-before relations.

        For external consistency, we should use the the currently last pending sequence number and wait for it to finish.
         */

        let open_sequence_number = self.isolation_manager.watermark();
        WriteSnapshot::new(self, open_sequence_number)
    }

    pub fn open_snapshot_write_at(
        self: Arc<Self>,
        sequence_number: SequenceNumber,
    ) -> Result<WriteSnapshot<Durability>, WriteSnapshotOpenError> {
        // TODO: Support waiting for watermark to catch up to sequence number when we support causal reading.
        assert!(sequence_number <= self.read_watermark());
        Ok(WriteSnapshot::new(self, sequence_number))
    }

    fn snapshot_commit(&self, snapshot: WriteSnapshot<Durability>) -> Result<(), StorageCommitError>
    where
        Durability: DurabilityService,
    {
        use StorageCommitError::{Durability, Internal, Keyspace, MVCCRead};

        self.set_initial_put_status(&snapshot).map_err(|error| MVCCRead { source: error })?;
        let commit_record = snapshot.into_commit_record();

        let commit_sequence_number = self
            .durability_service
            .sequenced_write(&commit_record)
            .map_err(|error| Durability { name: self.name.to_string(), source: error })?;

        let validated_commit = self
            .isolation_manager
            .validate_commit(commit_sequence_number, commit_record, &self.durability_service)
            .map_err(|error| Durability { name: self.name.to_owned(), source: error })?;

        match validated_commit {
            ValidatedCommit::Write(write_batches) => {
                // Write to the k-v storage
                self.keyspaces
                    .write(write_batches)
                    .map_err(|error| Keyspace { name: self.name.to_owned(), source: Arc::new(error) })?;

                // Inform the isolation manager and increment the watermark
                self.isolation_manager
                    .applied(commit_sequence_number)
                    .map_err(|error| Internal { name: self.name.clone(), source: Box::new(error) })?;

                Self::persist_commit_status(true, commit_sequence_number, &self.durability_service)
                    .map_err(|error| Durability { name: self.name.clone(), source: error })?;

                Ok(())
            }
            ValidatedCommit::Conflict(conflict) => {
                Self::persist_commit_status(false, commit_sequence_number, &self.durability_service)
                    .map_err(|error| Durability { name: self.name.clone(), source: error })?;
                Err(StorageCommitError::Isolation { name: self.name.clone(), conflict })
            }
        }
    }

    fn set_initial_put_status(&self, snapshot: &WriteSnapshot<Durability>) -> Result<(), MVCCReadError>
    where
        Durability: DurabilityService,
    {
        for buffer in snapshot.operations() {
            let writes = buffer.writes().write().unwrap();
            let puts = writes.iter().filter_map(|(key, write)| match write {
                Write::Put { value, reinsert, known_to_exist } => Some((key, value, reinsert, *known_to_exist)),
                _ => None,
            });
            for (key, value, reinsert, known_to_exist) in puts {
                let wrapped = StorageKeyReference::new_raw(buffer.keyspace_id, key.as_ref());
                if known_to_exist {
                    debug_assert!(self
                        .get::<0>(wrapped, snapshot.open_sequence_number())
                        .is_ok_and(|opt| opt.is_some()));
                    reinsert.store(false, Ordering::Release);
                } else {
                    let existing_stored = self
                        .get::<BUFFER_VALUE_INLINE>(wrapped, snapshot.open_sequence_number())?
                        .is_some_and(|reference| reference.bytes() == value.bytes());
                    reinsert.store(!existing_stored, Ordering::Release);
                }
            }
        }
        Ok(())
    }

    fn persist_commit_status(
        did_apply: bool,
        commit_sequence_number: SequenceNumber,
        durability_service: &Durability,
    ) -> Result<(), DurabilityError>
    where
        Durability: DurabilityService,
    {
        durability_service.unsequenced_write(&StatusRecord::new(commit_sequence_number, did_apply))?;
        Ok(())
    }

    pub fn closed_snapshot_write(&self, open_sequence_number: SequenceNumber) {
        self.isolation_manager.closed_for_read(open_sequence_number)
    }

    fn get_keyspace(&self, keyspace_id: KeyspaceId) -> &Keyspace {
        self.keyspaces.get(keyspace_id)
    }

    pub fn checkpoint(&self) -> Result<PathBuf, CheckpointCreateError> {
        Checkpoint::create(self.read_watermark(), &self.path, &self.keyspaces)
    }

    pub fn delete_storage(self) -> Result<(), Vec<StorageDeleteError>> {
        use StorageDeleteError::{DirectoryDelete, KeyspaceDelete};

        self.keyspaces.delete().map_err(|errs| {
            errs.into_iter().map(|error| KeyspaceDelete { name: self.name.clone(), source: error }).collect_vec()
        })?;

        if self.path.exists() {
            std::fs::remove_dir_all(&self.path).map_err(|error| {
                error!("Failed to delete storage {}, received error: {}", self.name, error);
                vec![DirectoryDelete { name: self.name.clone(), source: error }]
            })?;
        }

        Ok(())
    }

    fn get<'a, const INLINE_BYTES: usize>(
        &self,
        key: impl Into<StorageKeyReference<'a>>,
        open_sequence_number: SequenceNumber,
    ) -> Result<Option<ByteArray<INLINE_BYTES>>, MVCCReadError> {
        let key = key.into();
        let mut iterator =
            self.iterate_range(KeyRange::new_within(StorageKey::<0>::Reference(key), false), open_sequence_number);
        loop {
            match iterator.next().transpose()? {
                None => return Ok(None),
                Some((k, v)) if k.bytes() == key.bytes() => return Ok(Some(ByteArray::copy(v.bytes()))),
                Some(_) => (),
            }
        }
    }

    pub(crate) fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PS>>,
        open_sequence_number: SequenceNumber,
    ) -> MVCCRangeIterator<'this, PS> {
        MVCCRangeIterator::new(self, range, open_sequence_number)
    }

    pub fn read_watermark(&self) -> SequenceNumber {
        self.isolation_manager.watermark()
    }

    // --- direct access to storage, bypassing MVCC and returning raw key/value pairs ---

    pub fn put_raw(&self, key: StorageKeyReference<'_>, value: &Bytes<'_, BUFFER_VALUE_INLINE>) {
        // TODO: writes should always have to go through a transaction? Otherwise we have to WAL right here in a different path
        self.keyspaces
            .get(key.keyspace_id())
            .put(key.bytes(), value.bytes())
            .map_err(|e| MVCCStorageError {
                storage_name: self.name().to_owned(),
                kind: MVCCStorageErrorKind::KeyspaceError {
                    source: Arc::new(e),
                    keyspace_name: self.keyspaces.get(key.keyspace_id()).name(),
                },
            })
            .unwrap_or_log()
    }

    pub fn get_raw_mapped<M, V>(&self, key: StorageKeyReference<'_>, mut mapper: M) -> Option<V>
    where
        M: FnMut(&[u8]) -> V,
    {
        self.keyspaces
            .get(key.keyspace_id())
            .get(key.bytes(), |value| mapper(value))
            .map_err(|e| MVCCStorageError {
                storage_name: self.name().to_owned(),
                kind: MVCCStorageErrorKind::KeyspaceError {
                    source: Arc::new(e),
                    keyspace_name: self.keyspaces.get(key.keyspace_id()).name(),
                },
            })
            .unwrap_or_log() // TODO: unwrap_or_log may be incorrect: this could trigger if the DB is deleted for example?
    }

    pub fn get_prev_raw<M, T>(&self, key: StorageKeyReference<'_>, mut key_value_mapper: M) -> Option<T>
    where
        M: FnMut(&MVCCKey<'_>, &[u8]) -> T,
    {
        self.keyspaces
            .get(key.keyspace_id())
            .get_prev(key.bytes(), |raw_key, v| key_value_mapper(&MVCCKey::wrap_slice(raw_key), v))
    }

    pub fn iterate_keyspace_range<'this, const PREFIX_INLINE: usize>(
        &'this self,
        range: KeyRange<StorageKey<'this, PREFIX_INLINE>>,
    ) -> KeyspaceRangeIterator<'this, PREFIX_INLINE> {
        debug_assert!(!range.start().bytes().is_empty());
        self.keyspaces
            .get(range.start().keyspace_id())
            .iterate_range(range.map(|k| k.into_byte_array_or_ref(), |fixed| fixed))
    }
}

#[derive(Debug)]
pub enum ReadSnapshotOpenError {}

impl fmt::Display for ReadSnapshotOpenError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

impl Error for ReadSnapshotOpenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match *self {}
    }
}

#[derive(Debug)]
pub enum WriteSnapshotOpenError {}

impl fmt::Display for WriteSnapshotOpenError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

impl Error for WriteSnapshotOpenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match *self {}
    }
}

#[derive(Debug)]
pub enum StorageOpenError {
    StorageDirectoryCreate { name: String, source: io::Error },

    DurabilityServiceOpen { name: String, source: io::Error },
    DurabilityServiceRead { name: String, source: DurabilityError },
    DurabilityServiceWrite { name: String, source: DurabilityError },

    CheckpointLoad { name: String, source: CheckpointLoadError },
    CheckpointCreate { name: String, source: CheckpointCreateError },

    Commit { source: StorageCommitError },
}

impl fmt::Display for StorageOpenError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for StorageOpenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::StorageDirectoryCreate { source, .. } => Some(source),
            Self::DurabilityServiceOpen { source, .. } => Some(source),
            Self::DurabilityServiceRead { source, .. } => Some(source),
            Self::DurabilityServiceWrite { source, .. } => Some(source),
            Self::Commit { source, .. } => Some(source),
            Self::CheckpointLoad { source, .. } => Some(source),
            Self::CheckpointCreate { source, .. } => Some(source),
        }
    }
}

#[derive(Debug)]
pub enum StorageCommitError {
    Internal { name: String, source: Box<dyn Error> },
    Isolation { name: String, conflict: IsolationConflict },
    IO { name: String, source: io::Error },
    MVCCRead { source: MVCCReadError },
    Keyspace { name: String, source: Arc<KeyspaceError> },
    Durability { name: String, source: DurabilityError },
}

impl fmt::Display for StorageCommitError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for StorageCommitError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Internal { source, .. } => Some(&**source),
            Self::Isolation { .. } => None,
            Self::IO { source, .. } => Some(source),
            Self::MVCCRead { source, .. } => Some(source),
            Self::Keyspace { source, .. } => Some(source),
            Self::Durability { source, .. } => Some(source),
        }
    }
}

#[derive(Debug)]
pub enum StorageDeleteError {
    KeyspaceDelete { name: String, source: KeyspaceDeleteError },
    DirectoryDelete { name: String, source: io::Error },
}

impl fmt::Display for StorageDeleteError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for StorageDeleteError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::KeyspaceDelete { source, .. } => Some(source),
            Self::DirectoryDelete { source, .. } => Some(source),
        }
    }
}

/// MVCC keys are made of three parts: the [KEY][SEQ][OP]
pub struct MVCCKey<'bytes> {
    bytes: Bytes<'bytes, MVCC_KEY_INLINE_SIZE>,
}

// byte array inline size can be adjusted to avoid allocation since these key are often short-lived
const MVCC_KEY_INLINE_SIZE: usize = 128;

impl<'bytes> MVCCKey<'bytes> {
    const OPERATION_START_NEGATIVE_OFFSET: usize = StorageOperation::serialised_len();
    const SEQUENCE_NUMBER_START_NEGATIVE_OFFSET: usize =
        Self::OPERATION_START_NEGATIVE_OFFSET + SequenceNumber::serialised_len();

    fn build(key: &[u8], sequence_number: SequenceNumber, storage_operation: StorageOperation) -> Self {
        let length = key.len() + SequenceNumber::serialised_len() + StorageOperation::serialised_len();
        let mut byte_array = ByteArray::zeros(length);
        let bytes = byte_array.bytes_mut();

        let key_end = key.len();
        let sequence_number_end = key_end + SequenceNumber::serialised_len();
        let operation_end = sequence_number_end + StorageOperation::serialised_len();

        bytes[0..key_end].copy_from_slice(key);
        sequence_number.invert().serialise_be_into(&mut bytes[key_end..sequence_number_end]);
        bytes[sequence_number_end..operation_end].copy_from_slice(storage_operation.bytes());

        Self { bytes: Bytes::Array(byte_array) }
    }

    fn wrap_slice(bytes: &'bytes [u8]) -> Self {
        Self { bytes: Bytes::Reference(ByteReference::new(bytes)) }
    }

    pub(crate) fn is_visible_to(&self, sequence_number: SequenceNumber) -> bool {
        self.sequence_number() <= sequence_number
    }

    fn bytes(&self) -> &[u8] {
        self.bytes.bytes()
    }

    fn length(&self) -> usize {
        self.bytes.length()
    }

    pub fn key(&self) -> &[u8] {
        &self.bytes()[0..(self.length() - Self::SEQUENCE_NUMBER_START_NEGATIVE_OFFSET)]
    }

    fn into_key(self) -> Bytes<'bytes, MVCC_KEY_INLINE_SIZE> {
        let end = self.length() - Self::SEQUENCE_NUMBER_START_NEGATIVE_OFFSET;
        let bytes = self.bytes;
        bytes.truncate(end)
    }

    fn sequence_number(&self) -> SequenceNumber {
        let sequence_number_start = self.length() - Self::SEQUENCE_NUMBER_START_NEGATIVE_OFFSET;
        let sequence_number_end = sequence_number_start + SequenceNumber::serialised_len();
        let inverse_sequence_number_bytes = &self.bytes()[sequence_number_start..sequence_number_end];
        debug_assert_eq!(SequenceNumber::serialised_len(), inverse_sequence_number_bytes.len());
        SequenceNumber::from_be_bytes(inverse_sequence_number_bytes).invert()
    }

    fn operation(&self) -> StorageOperation {
        let operation_byte_offset = self.length() - Self::OPERATION_START_NEGATIVE_OFFSET;
        let operation_byte_end = operation_byte_offset + StorageOperation::serialised_len();
        StorageOperation::from(&self.bytes()[operation_byte_offset..operation_byte_end])
    }
}

enum StorageOperation {
    Insert,
    Delete,
}

impl StorageOperation {
    const BYTES: usize = 1;

    const fn bytes(&self) -> &[u8; Self::BYTES] {
        match self {
            Self::Insert => &[0x0],
            Self::Delete => &[0x1],
        }
    }

    const fn from(bytes: &[u8]) -> Self {
        match bytes {
            [0x0] => Self::Insert,
            [0x1] => Self::Delete,
            _ => panic!("Unrecognised storage operation bytes."),
        }
    }

    const fn serialised_len() -> usize {
        Self::BYTES
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, sync::Arc};

    use bytes::byte_array::ByteArray;
    use durability::{wal::WAL, DurabilityService, SequenceNumber, Sequencer};
    use resource::constants::snapshot::BUFFER_KEY_INLINE;
    use test_utils::{create_tmp_dir, init_logging};

    use super::MVCCStorage;
    use crate::{
        isolation_manager::{CommitRecord, ValidatedCommit},
        key_value::{StorageKeyArray, StorageKeyReference},
        keyspace::{KeyspaceId, KeyspaceSet, Keyspaces},
        snapshot::buffer::OperationsBuffer,
        write_batches::WriteBatches,
    };

    macro_rules! test_keyspace_set {
        {$($variant:ident => $id:literal : $name: literal),* $(,)?} => {
            #[derive(Clone, Copy)]
            enum TestKeyspaceSet { $($variant),* }
            impl KeyspaceSet for TestKeyspaceSet {
                fn iter() -> impl Iterator<Item = Self> { [$(Self::$variant),*].into_iter() }
                fn id(&self) -> KeyspaceId {
                    match *self { $(Self::$variant => KeyspaceId($id)),* }
                }
                fn name(&self) -> &'static str {
                    match *self { $(Self::$variant => $name),* }
                }
            }
        };
    }

    #[test]
    fn recovery_path() {
        test_keyspace_set! {
            Keyspace => 0: "keyspace",
        }

        init_logging();
        let storage_path = create_tmp_dir();
        let watermark_after_one_commit = {
            let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
            let commit_record = CommitRecord::new(OperationsBuffer::new(), SequenceNumber::MIN);
            let seq = storage.durability_service.sequenced_write(&commit_record).unwrap();

            let validated_commit =
                storage.isolation_manager.validate_commit(seq, commit_record, &storage.durability_service).unwrap();
            assert!(matches!(validated_commit, ValidatedCommit::Write(_)));

            let ValidatedCommit::Write(write_batches) = validated_commit else { unreachable!() };

            storage.keyspaces.write(write_batches).unwrap();
            storage.isolation_manager.applied(seq).unwrap();

            MVCCStorage::persist_commit_status(true, seq, &storage.durability_service).unwrap();

            storage.read_watermark()
        };

        let pending_commit_sequence = {
            let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
            assert_eq!(watermark_after_one_commit, storage.read_watermark());
            storage
                .durability_service
                .sequenced_write::<CommitRecord>(&CommitRecord::new(OperationsBuffer::new(), storage.read_watermark()))
                .unwrap()
            // We don't commit it.
        };
        {
            let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
            assert_eq!(pending_commit_sequence, storage.read_watermark()); // Recovery will commit the pending one.
        };
    }

    #[test]
    fn reload_without_checkpoint_or_wal_is_empty() {
        test_keyspace_set! {
            Keyspace => 0: "keyspace",
        }

        init_logging();
        let storage_path = create_tmp_dir();
        let key = StorageKeyArray::<BUFFER_KEY_INLINE>::from((TestKeyspaceSet::Keyspace, b"hello"));

        let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        snapshot.put(key.clone());
        snapshot.commit().unwrap();
        drop(storage);

        fs::remove_dir_all(storage_path.join(MVCCStorage::<WAL>::WAL_DIR_NAME)).unwrap();

        let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
        assert_eq!(storage.get::<0>(StorageKeyReference::from(&key), SequenceNumber::MAX).unwrap(), None);
    }

    #[test]
    fn writes_after_checkpoint_are_reloaded_from_wal() {
        test_keyspace_set! {
            Keyspace => 0: "keyspace",
        }

        init_logging();
        let storage_path = create_tmp_dir();
        let key_hello = StorageKeyArray::<BUFFER_KEY_INLINE>::from((TestKeyspaceSet::Keyspace, b"hello"));
        let key_world = StorageKeyArray::<BUFFER_KEY_INLINE>::from((TestKeyspaceSet::Keyspace, b"world"));

        let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        snapshot.put(key_hello.clone());
        snapshot.commit().unwrap();
        storage.checkpoint().unwrap();
        drop(storage);

        let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        snapshot.put(key_world.clone());
        snapshot.commit().unwrap();
        drop(storage);

        // hide wal from storage
        fs::rename(storage_path.join(MVCCStorage::<WAL>::WAL_DIR_NAME), storage_path.join("_wal")).unwrap();

        let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
        assert_eq!(storage.get::<0>(&key_hello, SequenceNumber::MAX).unwrap().unwrap(), ByteArray::empty());
        assert_eq!(storage.get::<0>(&key_world, SequenceNumber::MAX).unwrap(), None);
        drop(storage);

        // restore wal
        fs::remove_dir_all(storage_path.join(MVCCStorage::<WAL>::WAL_DIR_NAME)).unwrap();
        fs::rename(storage_path.join("_wal"), storage_path.join(MVCCStorage::<WAL>::WAL_DIR_NAME)).unwrap();

        let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
        assert_eq!(storage.get::<0>(&key_hello, SequenceNumber::MAX).unwrap().unwrap(), ByteArray::empty());
        assert_eq!(storage.get::<0>(&key_world, SequenceNumber::MAX).unwrap().unwrap(), ByteArray::empty());
    }

    #[test]
    fn test_recovery_from_failed_write() {
        test_keyspace_set! {
            Keyspace => 0: "keyspace",
        }

        init_logging();
        let storage_path = create_tmp_dir();
        let key = StorageKeyArray::<BUFFER_KEY_INLINE>::from((TestKeyspaceSet::Keyspace, b"hello"));

        let seq = {
            let operations = OperationsBuffer::new();
            operations.writes_in(key.keyspace_id()).insert(key.byte_array().clone(), ByteArray::empty());
            let mut durability_service = WAL::open(storage_path.join(MVCCStorage::<WAL>::WAL_DIR_NAME)).unwrap();
            durability_service.register_record_type::<CommitRecord>();
            durability_service.sequenced_write(&CommitRecord::new(operations, durability_service.previous())).unwrap()
            /* CRASH */
        };

        let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
        assert_eq!(storage.get::<0>(&key, seq).unwrap().unwrap(), ByteArray::empty());
    }

    #[test]
    fn test_recovery_from_partial_write() {
        test_keyspace_set! {
            PersistedKeyspace => 0: "write",
            FailedKeyspace => 1: "failed",
        }

        init_logging();
        let storage_path = create_tmp_dir();
        let key_1 = StorageKeyArray::from((TestKeyspaceSet::PersistedKeyspace, b"hello"));
        let key_2 = StorageKeyArray::from((TestKeyspaceSet::FailedKeyspace, b"world"));

        let seq = {
            let full_operations = OperationsBuffer::new();
            full_operations.writes_in(key_1.keyspace_id()).insert(key_1.byte_array().clone(), ByteArray::empty());
            full_operations.writes_in(key_2.keyspace_id()).insert(key_2.byte_array().clone(), ByteArray::empty());

            let partial_operations = OperationsBuffer::new();
            partial_operations.writes_in(key_1.keyspace_id()).insert(key_1.byte_array().clone(), ByteArray::empty());

            let mut durability_service = WAL::open(storage_path.join(MVCCStorage::<WAL>::WAL_DIR_NAME)).unwrap();
            durability_service.register_record_type::<CommitRecord>();
            let seq = durability_service
                .sequenced_write(&CommitRecord::new(full_operations, durability_service.previous()))
                .unwrap();

            let partial_commit = WriteBatches::from_operations(seq, &partial_operations);
            let keyspaces =
                Keyspaces::open::<TestKeyspaceSet>(storage_path.join(MVCCStorage::<WAL>::STORAGE_DIR_NAME)).unwrap();
            keyspaces.write(partial_commit).unwrap();

            /* CRASH */

            seq
        };

        let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
        assert_eq!(storage.get::<0>(&key_2, seq).unwrap().unwrap(), ByteArray::empty());
    }
}
