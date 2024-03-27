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

#![deny(unused_must_use)]
#![deny(elided_lifetimes_in_paths)]
#![allow(dead_code)]
#![allow(clippy::module_inception)]

use std::{
    error::Error,
    fmt,
    fs::{self, File},
    io::{self, Write as _},
    path::{Path, PathBuf},
    sync::{atomic::Ordering, Arc},
};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference, Bytes};
use chrono::Utc;
use durability::{DurabilityError, DurabilityService, SequenceNumber};
use iterator::MVCCReadError;
use itertools::Itertools;
use keyspace::keyspace::KeyspaceOpenError;
use logger::{error, result::ResultExt};
use primitive::{prefix_range::PrefixRange, u80::U80};
use resource::constants::snapshot::BUFFER_VALUE_INLINE;
use speedb::{Options, WriteBatch};

use crate::{
    error::{MVCCStorageError, MVCCStorageErrorKind},
    isolation_manager::{CommitRecord, IsolationManager},
    iterator::MVCCRangeIterator,
    key_value::{StorageKey, StorageKeyReference},
    keyspace::{
        iterator::KeyspaceRangeIterator,
        keyspace::{
            Keyspace, KeyspaceCheckpointError, KeyspaceId, KEYSPACE_ID_MAX, KEYSPACE_ID_RESERVED_UNSET,
            KEYSPACE_MAXIMUM_COUNT,
        },
    },
    snapshot::{buffer::KeyspaceBuffers, write::Write, ReadSnapshot, WriteSnapshot},
};

pub mod error;
pub mod isolation_manager;
pub mod iterator;
pub mod key_value;
pub mod keyspace;
pub mod snapshot;

#[derive(Debug)]
pub struct MVCCStorage<D> {
    name: String,
    path: PathBuf,
    keyspaces: Vec<Keyspace>,
    keyspaces_index: [Option<KeyspaceId>; KEYSPACE_MAXIMUM_COUNT],
    durability_service: D,
    isolation_manager: IsolationManager,
}

fn new_db_options() -> Options {
    let mut options = Options::default();
    options.create_if_missing(true);
    options.create_missing_column_families(true);
    options.enable_statistics();
    // TODO optimise per-keyspace
    options
}

pub trait KeyspaceSet: Copy {
    fn iter() -> impl Iterator<Item = Self>;
    fn id(&self) -> u8;
    fn name(&self) -> &'static str;
}

fn validate_new_keyspace(
    keyspace_id: impl KeyspaceSet,
    keyspaces: &[Keyspace],
    keyspaces_index: &[Option<KeyspaceId>],
) -> Result<(), KeyspaceValidationError> {
    use KeyspaceValidationError::{IdExists, IdReserved, IdTooLarge, NameExists};

    let name = keyspace_id.name();
    let id = KeyspaceId(keyspace_id.id());

    if id == KEYSPACE_ID_RESERVED_UNSET {
        return Err(IdReserved { name, id: id.0 });
    }

    if id > KEYSPACE_ID_MAX {
        return Err(IdTooLarge { name, id: id.0, max_id: KEYSPACE_ID_MAX.0 });
    }

    for (existing_id, existing_keyspace_index) in keyspaces_index.iter().enumerate() {
        if let Some(existing_index) = existing_keyspace_index {
            let keyspace = &keyspaces[existing_index.0 as usize];
            if keyspace.name() == name {
                return Err(NameExists { name });
            }
            if existing_id == id.0 as usize {
                return Err(IdExists { new_name: name, id: id.0, existing_name: keyspace.name() });
            }
        }
    }
    Ok(())
}

#[derive(Debug)]
pub enum KeyspaceValidationError {
    IdReserved { name: &'static str, id: u8 },
    IdTooLarge { name: &'static str, id: u8, max_id: u8 },
    NameExists { name: &'static str },
    IdExists { new_name: &'static str, id: u8, existing_name: &'static str },
}

impl fmt::Display for KeyspaceValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NameExists { name, .. } => write!(f, "keyspace '{name}' is defined multiple times."),
            Self::IdReserved { name, id, .. } => write!(f, "reserved keyspace id '{id}' cannot be used for new keyspace '{name}'."),
            Self::IdTooLarge { name, id, max_id, .. } => write!(
                f, "keyspace id '{id}' cannot be used for new keyspace '{name}' since it is larger than maximum keyspace id '{max_id}'.",
            ),
            Self::IdExists { new_name, id, existing_name, .. } => write!(
                f,
                "keyspace id '{}' cannot be used for new keyspace '{}' since it is already used by keyspace '{}'.",
                id, new_name, existing_name
            ),
        }
    }
}

impl Error for KeyspaceValidationError {}

fn db_options() -> Options {
    let mut options = Options::default();
    options.create_if_missing(true);
    options.create_missing_column_families(true);
    options.enable_statistics();
    // TODO optimise per-keyspace
    options
}

fn recover_keyspaces<KS: KeyspaceSet>(
    storage_dir: impl AsRef<Path>,
) -> Result<(Vec<Keyspace>, [Option<KeyspaceId>; KEYSPACE_MAXIMUM_COUNT]), StorageRecoverError> {
    use StorageRecoverError::*;

    let path = storage_dir.as_ref();
    let mut keyspaces = Vec::new();
    let mut keyspaces_index = core::array::from_fn(|_| None);
    let options = db_options();
    for keyspace_id in KS::iter() {
        validate_new_keyspace(keyspace_id, &keyspaces, &keyspaces_index)
            .map_err(|error| KeyspaceValidation { source: error })?;
        keyspaces.push(Keyspace::open(path, keyspace_id, &options).map_err(|error| KeyspaceOpen { source: error })?);
        keyspaces_index[keyspace_id.id() as usize] = Some(KeyspaceId(keyspaces.len() as u8 - 1));
    }
    Ok((keyspaces, keyspaces_index))
}

impl<D> MVCCStorage<D> {
    const WAL_DIR_NAME: &'static str = "wal";
    const STORAGE_DIR_NAME: &'static str = "storage";
    const CHECKPOINT_DIR_NAME: &'static str = "checkpoint";
    const CHECKPOINT_METADATA_FILE_NAME: &'static str = "METADATA";

    pub fn recover<KS: KeyspaceSet>(name: impl AsRef<str>, path: &Path) -> Result<Self, StorageRecoverError>
    where
        D: DurabilityService,
    {
        let storage_dir = path.join(Self::STORAGE_DIR_NAME);
        if !storage_dir.exists() {
            fs::create_dir_all(&storage_dir).map_err(|_error| todo!())?;
        }

        let mut durability_service = D::recover(path.join(Self::WAL_DIR_NAME)).expect("Could not create WAL directory");
        // FIXME proper error
        durability_service.register_record_type::<CommitRecord>();

        let name = name.as_ref();
        let (keyspaces, keyspaces_index) = recover_keyspaces::<KS>(&storage_dir)?;
        let isolation_manager = IsolationManager::new(SequenceNumber::from(1));

        let name = name.to_owned();
        let path = path.to_owned();
        let storage = Self { name, path, keyspaces, keyspaces_index, isolation_manager, durability_service };

        storage.reload()?;

        Ok(storage)
    }

    fn reload(&self) -> Result<(), StorageRecoverError>
    where
        D: DurabilityService,
    {
        use StorageRecoverError::DurabilityServiceRead;
        let records = self
            .durability_service
            .iter_type_from_start::<CommitRecord>()
            .map_err(|error| DurabilityServiceRead { source: error })?;
        for record in records {
            match record {
                Ok((commit_sequence_number, commit_record)) => {
                    self.write_commit_record(commit_sequence_number, commit_record).unwrap();
                }
                Err(error) => return Err(DurabilityServiceRead { source: error }),
            }
        }
        Ok(())
    }

    fn name(&self) -> &str {
        &self.name
    }

    pub fn open_snapshot_write(&self) -> WriteSnapshot<'_, D> {
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

    pub fn open_snapshot_read(&self) -> ReadSnapshot<'_, D> {
        let open_sequence_number = self.isolation_manager.watermark();
        ReadSnapshot::new(self, open_sequence_number)
    }

    pub fn open_snapshot_read_at(&self, sequence_number: SequenceNumber) -> ReadSnapshot<'_, D> {
        // TODO: validate sequence number is before or equal to watermark
        ReadSnapshot::new(self, sequence_number)
    }

    fn snapshot_commit(&self, snapshot: WriteSnapshot<'_, D>) -> Result<(), MVCCStorageError>
    where
        D: DurabilityService,
    {
        let commit_record = snapshot.into_commit_record();

        //  1. make durable and get sequence number
        let commit_sequence_number =
            self.durability_service.sequenced_write(&commit_record).map_err(|err| MVCCStorageError {
                storage_name: self.name.to_string(),
                kind: MVCCStorageErrorKind::DurabilityError { source: err },
            })?;

        self.write_commit_record(commit_sequence_number, commit_record)
    }

    fn write_commit_record(
        &self,
        commit_sequence_number: SequenceNumber,
        commit_record: CommitRecord,
    ) -> Result<(), MVCCStorageError> {
        // 2. validate commit isolation
        self.isolation_manager.try_commit(commit_sequence_number, commit_record).map_err(|err| MVCCStorageError {
            storage_name: self.name.clone(),
            kind: MVCCStorageErrorKind::IsolationError { source: err },
        })?;

        //  3. write to kv-storage
        let write_batches = self.isolation_manager.apply_to_commit_record(&commit_sequence_number, |record| {
            self.to_write_batches(commit_sequence_number, record.buffers())
        });

        for (index, write_batch) in write_batches.into_iter().enumerate() {
            debug_assert!(index < KEYSPACE_MAXIMUM_COUNT);
            if write_batch.is_some() {
                self.get_keyspace(KeyspaceId(index as _)).write(write_batch.unwrap()).map_err(|error| {
                    MVCCStorageError {
                        storage_name: self.name.clone(),
                        kind: MVCCStorageErrorKind::KeyspaceError {
                            source: Arc::new(error),
                            keyspace_name: self.get_keyspace(KeyspaceId(index as _)).name(),
                        },
                    }
                })?;
            }
        }
        Ok(())
    }

    fn to_write_batches(
        &self,
        seq: SequenceNumber,
        buffers: &KeyspaceBuffers,
    ) -> [Option<WriteBatch>; KEYSPACE_MAXIMUM_COUNT] {
        let mut write_batches: [Option<WriteBatch>; KEYSPACE_MAXIMUM_COUNT] = core::array::from_fn(|_| None);

        for (index, buffer) in buffers.iter().enumerate() {
            let map = buffer.map().read().unwrap();
            if !map.is_empty() {
                let mut write_batch = WriteBatch::default();
                for (key, write) in &*map {
                    match write {
                        Write::Insert { value } => write_batch
                            .put(MVCCKey::build(key.bytes(), seq, StorageOperation::Insert).bytes(), value.bytes()),
                        Write::InsertPreexisting { value, reinsert } => {
                            if reinsert.load(Ordering::SeqCst) {
                                write_batch.put(
                                    MVCCKey::build(key.bytes(), seq, StorageOperation::Insert).bytes(),
                                    value.bytes(),
                                )
                            }
                        }
                        Write::RequireExists { .. } => (),
                        Write::Delete => {
                            write_batch.put(MVCCKey::build(key.bytes(), seq, StorageOperation::Delete).bytes(), [])
                        }
                    }
                }
                write_batches[index] = Some(write_batch);
            }
        }
        write_batches
    }

    pub fn closed_snapshot_write(&self, open_sequence_number: &SequenceNumber) {
        self.isolation_manager.closed(open_sequence_number)
    }

    fn get_keyspace(&self, keyspace_id: KeyspaceId) -> &Keyspace {
        let keyspace_index = self.keyspaces_index[keyspace_id.0 as usize].unwrap();
        &self.keyspaces[keyspace_index.0 as usize]
    }

    pub fn checkpoint(&self) -> Result<(), StorageCheckpointError> {
        use StorageCheckpointError::{
            CreateCheckpointDir, CreateMetadataFile, KeyspaceCheckpoint, ReadCheckpointDir, RemoveOldCheckpoint,
            WriteMetadata,
        };

        let watermark = self.isolation_manager.watermark();

        let checkpoint_dir = self.path.join(Self::CHECKPOINT_DIR_NAME);
        if !checkpoint_dir.exists() {
            fs::create_dir_all(&checkpoint_dir)
                .map_err(|error| CreateCheckpointDir { dir: checkpoint_dir.clone(), source: error })?
        }

        let previous_checkpoints: Vec<_> = fs::read_dir(&checkpoint_dir)
            .map_err(|error| ReadCheckpointDir { dir: checkpoint_dir.clone(), source: error })?
            .map_ok(|entry| entry.path())
            .try_collect()
            .map_err(|error| ReadCheckpointDir { dir: checkpoint_dir.clone(), source: error })?;

        let current_checkpoint_dir = checkpoint_dir.join(format!("{}", Utc::now().timestamp_micros()));
        fs::create_dir_all(&current_checkpoint_dir)
            .map_err(|error| CreateCheckpointDir { dir: checkpoint_dir.clone(), source: error })?;

        for keyspace in &self.keyspaces {
            keyspace.checkpoint(&current_checkpoint_dir).map_err(|error| KeyspaceCheckpoint {
                keyspace_name: keyspace.name().to_owned(),
                dir: current_checkpoint_dir.clone(),
                source: error,
            })?;
        }

        let metadata_file_path = current_checkpoint_dir.join(Self::CHECKPOINT_METADATA_FILE_NAME);
        let mut metadata_file = File::create(&metadata_file_path)
            .map_err(|error| CreateMetadataFile { file_path: metadata_file_path.clone(), source: error })?;
        metadata_file
            .write_all(watermark.number().to_string().as_bytes())
            .map_err(|error| WriteMetadata { file_path: metadata_file_path.clone(), source: error })?;
        metadata_file
            .sync_all()
            .map_err(|error| WriteMetadata { file_path: metadata_file_path.clone(), source: error })?;

        for previous_checkpoint in previous_checkpoints {
            fs::remove_dir_all(&previous_checkpoint)
                .map_err(|error| RemoveOldCheckpoint { dir: previous_checkpoint, source: error })?
        }

        Ok(())
    }

    pub fn delete_storage(self) -> Result<(), Vec<MVCCStorageError>> {
        let errors: Vec<MVCCStorageError> = self
            .keyspaces
            .into_iter()
            .map(|keyspace| keyspace.delete())
            .filter(|result| result.is_err())
            .map(|result| MVCCStorageError {
                storage_name: self.name.clone(),
                kind: MVCCStorageErrorKind::KeyspaceDeleteError { source: result.unwrap_err() },
            })
            .collect();

        if !errors.is_empty() {
            return Err(errors);
        }

        if self.path.exists() {
            std::fs::remove_dir_all(&self.path).map_err(|err| {
                error!("Failed to delete storage {}, received error: {}", self.name, err);
                vec![MVCCStorageError {
                    storage_name: self.name.clone(),
                    kind: MVCCStorageErrorKind::FailedToDeleteStorage { source: err },
                }]
            })?;
        }

        Ok(())
    }

    pub fn get<V>(
        &self,
        key: StorageKeyReference<'_>,
        open_sequence_number: SequenceNumber,
        mut mapper: impl FnMut(ByteReference<'_>) -> V,
    ) -> Result<Option<V>, MVCCReadError> {
        let mut iterator =
            self.iterate_range(PrefixRange::new_within(StorageKey::<0>::Reference(key)), open_sequence_number);
        // TODO: we don't want to panic on unwrap here
        loop {
            match iterator.next().transpose()? {
                None => return Ok(None),
                Some((k, v)) if k.bytes() == key.bytes() => return Ok(Some(mapper(v))),
                Some(_) => (),
            }
        }
    }

    pub(crate) fn iterate_range<'this, const PS: usize>(
        &'this self,
        range: PrefixRange<StorageKey<'this, PS>>,
        open_sequence_number: SequenceNumber,
    ) -> MVCCRangeIterator<'this, PS> {
        MVCCRangeIterator::new(self, range, open_sequence_number)
    }

    // --- direct access to storage, bypassing MVCC and returning raw key/value pairs ---

    pub fn put_raw(&self, key: StorageKeyReference<'_>, value: &Bytes<'_, BUFFER_VALUE_INLINE>) {
        // TODO: writes should always have to go through a transaction? Otherwise we have to WAL right here in a different path
        self.get_keyspace(key.keyspace_id())
            .put(key.bytes(), value.bytes())
            .map_err(|e| MVCCStorageError {
                storage_name: self.name().to_owned(),
                kind: MVCCStorageErrorKind::KeyspaceError {
                    source: Arc::new(e),
                    keyspace_name: self.get_keyspace(key.keyspace_id()).name(),
                },
            })
            .unwrap_or_log()
    }

    pub fn get_raw<M, V>(&self, key: StorageKeyReference<'_>, mut mapper: M) -> Option<V>
    where
        M: FnMut(&[u8]) -> V,
    {
        self.get_keyspace(key.keyspace_id())
            .get(key.bytes(), |value| mapper(value))
            .map_err(|e| MVCCStorageError {
                storage_name: self.name().to_owned(),
                kind: MVCCStorageErrorKind::KeyspaceError {
                    source: Arc::new(e),
                    keyspace_name: self.get_keyspace(key.keyspace_id()).name(),
                },
                // TODO: unwrap_or_log may be incorrect: this could trigger if the DB is deleted for example?
            })
            .unwrap_or_log()
    }

    pub fn get_prev_raw<M, T>(&self, key: StorageKeyReference<'_>, mut key_value_mapper: M) -> Option<T>
    where
        M: FnMut(&[u8], &[u8]) -> T,
    {
        self.get_keyspace(key.keyspace_id()).get_prev(key.bytes(), |k, v| key_value_mapper(k, v))
    }

    pub fn iterate_keyspace_range<'this, const PREFIX_INLINE: usize>(
        &'this self,
        range: PrefixRange<StorageKey<'this, PREFIX_INLINE>>,
    ) -> KeyspaceRangeIterator<'this, PREFIX_INLINE> {
        debug_assert!(!range.start().bytes().is_empty());
        self.get_keyspace(range.start().keyspace_id()).iterate_range(range.map(|k| k.into_byte_array_or_ref()))
    }
}

#[derive(Debug)]
pub enum StorageRecoverError {
    KeyspaceValidation { source: KeyspaceValidationError },
    KeyspaceOpen { source: KeyspaceOpenError },
    DurabilityServiceRead { source: DurabilityError },
}

impl fmt::Display for StorageRecoverError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for StorageRecoverError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::KeyspaceValidation { source, .. } => Some(source),
            Self::KeyspaceOpen { source, .. } => Some(source),
            Self::DurabilityServiceRead { source, .. } => Some(source),
        }
    }
}

#[derive(Debug)]
pub enum StorageCheckpointError {
    CreateCheckpointDir { dir: PathBuf, source: io::Error },
    ReadCheckpointDir { dir: PathBuf, source: io::Error },

    KeyspaceCheckpoint { keyspace_name: String, dir: PathBuf, source: KeyspaceCheckpointError },

    CreateMetadataFile { file_path: PathBuf, source: io::Error },
    WriteMetadata { file_path: PathBuf, source: io::Error },

    RemoveOldCheckpoint { dir: PathBuf, source: io::Error },
}

impl fmt::Display for StorageCheckpointError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for StorageCheckpointError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::CreateCheckpointDir { source, .. } => Some(source),
            Self::ReadCheckpointDir { source, .. } => Some(source),
            Self::KeyspaceCheckpoint { source, .. } => Some(source),
            Self::CreateMetadataFile { source, .. } => Some(source),
            Self::WriteMetadata { source, .. } => Some(source),
            Self::RemoveOldCheckpoint { source, .. } => Some(source),
        }
    }
}

///
/// MVCC keys are made of three parts: the [KEY][SEQ][OP]
///
struct MVCCKey<'bytes> {
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

    fn key(&self) -> &[u8] {
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
        SequenceNumber::new(U80::from_be_bytes(inverse_sequence_number_bytes)).invert()
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

    const fn bytes(&self) -> &[u8; StorageOperation::BYTES] {
        match self {
            StorageOperation::Insert => &[0x0],
            StorageOperation::Delete => &[0x1],
        }
    }

    const fn from(bytes: &[u8]) -> StorageOperation {
        match bytes {
            [0x0] => StorageOperation::Insert,
            [0x1] => StorageOperation::Delete,
            _ => panic!("Unrecognised storage operation bytes."),
        }
    }

    const fn serialised_len() -> usize {
        StorageOperation::BYTES
    }
}
