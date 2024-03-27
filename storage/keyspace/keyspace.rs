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
    error::Error,
    fmt,
    path::{Path, PathBuf},
};

use bytes::Bytes;
use primitive::prefix_range::PrefixRange;
use serde::{Deserialize, Serialize};
use speedb::{checkpoint::Checkpoint, Options, ReadOptions, WriteBatch, WriteOptions, DB};

use super::iterator;
use crate::KeyspaceSet;

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct KeyspaceId(pub(crate) u8);

impl fmt::Display for KeyspaceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// WARNING: adjusting these constants affects many things, including serialised WAL records and in-memory data structures.  //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub(crate) const KEYSPACE_MAXIMUM_COUNT: usize = 10;
pub(crate) const KEYSPACE_ID_MAX: KeyspaceId = KeyspaceId(KEYSPACE_MAXIMUM_COUNT as u8 - 1);
pub(crate) const KEYSPACE_ID_RESERVED_UNSET: KeyspaceId = KeyspaceId(KEYSPACE_ID_MAX.0 + 1);

///
/// A non-durable key-value store that supports put, get, delete, iterate
/// and checkpointing.
///
pub(crate) struct Keyspace {
    path: PathBuf,
    name: &'static str,
    id: KeyspaceId,
    pub(super) kv_storage: DB,
    read_options: ReadOptions,
    write_options: WriteOptions,
}

impl Keyspace {
    pub(crate) fn open(
        storage_path: &Path,
        keyspace: impl KeyspaceSet,
        options: &Options,
    ) -> Result<Keyspace, KeyspaceOpenError> {
        use KeyspaceOpenError::SpeeDB;
        let name = keyspace.name();
        let path = storage_path.join(name);
        let kv_storage = DB::open(options, &path).map_err(|error| SpeeDB { name, source: error })?;
        Ok(Self::new(path, keyspace, kv_storage))
    }

    fn new(path: PathBuf, keyspace: impl KeyspaceSet, kv_storage: DB) -> Self {
        // initial read options, should be customised to this storage's properties
        let read_options = ReadOptions::default();
        let mut write_options = WriteOptions::default();
        write_options.disable_wal(true);
        Self { path, name: keyspace.name(), id: KeyspaceId(keyspace.id()), kv_storage, read_options, write_options }
    }

    // TODO: we want to be able to pass new options, since Rocks can handle rebooting with new options
    pub(crate) fn load_from_checkpoint(_path: PathBuf) {
        todo!()
        // Steps:
        //  WARNING: this is intended to be DESTRUCTIVE since we may wipe anything partially written in the active directory
        //  Locate the directory with the latest number - say 'checkpoint_n'
        //  Delete 'active' directory.
        //  Rename directory called 'active' to 'checkpoint_x' -- TODO: do we need to delete 'active' or will re-checkpointing to it be clever enough to delete corrupt files?
        //  Rename 'checkpoint_x' to 'active'
        //  open storage at 'active'
    }

    pub(super) fn new_read_options(&self) -> ReadOptions {
        ReadOptions::default()
    }

    fn new_write_options(&self) -> WriteOptions {
        let mut options = WriteOptions::default();
        options.disable_wal(true);
        options
    }

    pub(crate) fn id(&self) -> KeyspaceId {
        self.id
    }

    pub(crate) fn name(&self) -> &'static str {
        self.name
    }

    pub(crate) fn put(&self, key: &[u8], value: &[u8]) -> Result<(), KeyspaceError> {
        self.kv_storage.put_opt(key, value, &self.write_options).map_err(|e| KeyspaceError::Put { source: e })
    }

    pub(crate) fn get<M, V>(&self, key: &[u8], mut mapper: M) -> Result<Option<V>, KeyspaceError>
    where
        M: FnMut(&[u8]) -> V,
    {
        self.kv_storage
            .get_pinned_opt(key, &self.read_options)
            .map(|option| option.map(|value| mapper(value.as_ref())))
            .map_err(|err| KeyspaceError::Get { source: err })
    }

    pub(crate) fn get_prev<M, T>(&self, key: &[u8], mut mapper: M) -> Option<T>
    where
        M: FnMut(&[u8], &[u8]) -> T,
    {
        let mut iterator = self.kv_storage.raw_iterator_opt(self.new_read_options());
        iterator.seek_for_prev(key);
        iterator.item().map(|(k, v)| mapper(k, v))
    }

    // TODO: we should benchmark using iterator pools, which would require changing prefix/range on read options
    pub(crate) fn iterate_range<'s, const PREFIX_INLINE_SIZE: usize>(
        &'s self,
        range: PrefixRange<Bytes<'s, { PREFIX_INLINE_SIZE }>>,
    ) -> iterator::KeyspaceRangeIterator<'s, PREFIX_INLINE_SIZE> {
        iterator::KeyspaceRangeIterator::new(self, range)
    }

    pub(crate) fn write(&self, write_batch: WriteBatch) -> Result<(), KeyspaceError> {
        self.kv_storage
            .write_opt(write_batch, &self.write_options)
            .map_err(|error| KeyspaceError::BatchWrite { source: error })
    }

    pub(crate) fn checkpoint(&self, checkpoint_dir: &Path) -> Result<(), KeyspaceCheckpointError> {
        use KeyspaceCheckpointError::{CheckpointExists, CreateSpeeDBCheckpoint};
        let checkpoint_dir = checkpoint_dir.join(self.name);
        if checkpoint_dir.exists() {
            return Err(CheckpointExists { dir: checkpoint_dir });
        }

        let checkpoint = Checkpoint::new(&self.kv_storage).map_err(|error| CreateSpeeDBCheckpoint { source: error })?;
        checkpoint.create_checkpoint(&checkpoint_dir).map_err(|error| CreateSpeeDBCheckpoint { source: error })?;

        Ok(())
    }

    pub(crate) fn delete(self) -> Result<(), KeyspaceError> {
        match std::fs::remove_dir_all(self.path.clone()) {
            Ok(_) => Ok(()),
            Err(e) => Err(KeyspaceError::KeyspaceDelete { source: e }),
        }
    }
}

impl fmt::Debug for Keyspace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Keyspace[name={}, path={}, id={}]", self.name(), self.path.to_str().unwrap(), self.id,)
    }
}

#[derive(Debug)]
pub enum KeyspaceOpenError {
    SpeeDB { name: &'static str, source: speedb::Error },
}

impl fmt::Display for KeyspaceOpenError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for KeyspaceOpenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::SpeeDB { source, .. } => Some(source),
        }
    }
}

#[derive(Debug)]
pub enum KeyspaceCheckpointError {
    CheckpointExists { dir: PathBuf },
    CreateSpeeDBCheckpoint { source: speedb::Error },
}

impl fmt::Display for KeyspaceCheckpointError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for KeyspaceCheckpointError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::CheckpointExists { .. } => None,
            Self::CreateSpeeDBCheckpoint { source } => Some(source),
        }
    }
}

#[derive(Debug)]
pub enum KeyspaceError {
    KeyspaceDelete { source: std::io::Error },
    Get { source: speedb::Error },
    Put { source: speedb::Error },
    BatchWrite { source: speedb::Error },
    Iterate { source: speedb::Error },
}

impl fmt::Display for KeyspaceError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for KeyspaceError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self {
            Self::KeyspaceDelete { source, .. } => Some(source),
            Self::Get { source, .. } => Some(source),
            Self::Put { source, .. } => Some(source),
            Self::BatchWrite { source, .. } => Some(source),
            Self::Iterate { source, .. } => Some(source),
        }
    }
}
