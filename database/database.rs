/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    error::Error,
    ffi::OsString,
    fmt, fs, io,
    path::{Path, PathBuf},
    sync::Arc,
};

use concept::{
    error::ConceptWriteError,
    thing::statistics::{Statistics, StatisticsInitialiseError},
    type_::type_manager::TypeManager,
};
use durability::wal::{WALError, WAL};
use encoding::{
    error::EncodingError,
    graph::{
        definition::definition_key_generator::DefinitionKeyGenerator, thing::vertex_generator::ThingVertexGenerator,
        type_::vertex_generator::TypeVertexGenerator,
    },
    EncodingKeyspace,
};
use storage::{
    durability_client::{DurabilityClient, DurabilityClientError, WALClient},
    recovery::checkpoint::{Checkpoint, CheckpointCreateError, CheckpointLoadError},
    sequence_number::SequenceNumber,
    snapshot::WriteSnapshot,
    MVCCStorage, StorageOpenError,
};

pub struct Database<D> {
    name: String,
    path: PathBuf,
    pub(super) storage: Arc<MVCCStorage<D>>,
    pub(super) definition_key_generator: Arc<DefinitionKeyGenerator>,
    pub(super) type_vertex_generator: Arc<TypeVertexGenerator>,
    pub(super) thing_vertex_generator: Arc<ThingVertexGenerator>,
    thing_statistics: Arc<Statistics>,
}

impl<D> fmt::Debug for Database<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Database").field("name", &self.name).field("path", &self.path).finish_non_exhaustive()
    }
}

impl Database<WALClient> {
    pub fn open(path: &Path) -> Result<Database<WALClient>, DatabaseOpenError> {
        let file_name = path.file_name().unwrap();
        let name =
            file_name.to_str().ok_or_else(|| DatabaseOpenError::InvalidUnicodeName { name: file_name.to_owned() })?;

        if !path.exists() {
            Self::create(path, name)
        } else {
            Self::load(path, name)
        }
    }

    fn create(path: &Path, name: impl AsRef<str>) -> Result<Database<WALClient>, DatabaseOpenError> {
        use DatabaseOpenError::{DirectoryCreate, Encoding, SchemaInitialise, StorageOpen, WALOpen};
        fs::create_dir(path).map_err(|error| DirectoryCreate { path: path.to_owned(), source: error })?;
        let wal = WAL::create(path).map_err(|err| WALOpen { source: err })?;
        let storage = Arc::new(
            MVCCStorage::create::<EncodingKeyspace>(&name, path, WALClient::new(wal))
                .map_err(|error| StorageOpen { source: error })?,
        );
        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        let thing_vertex_generator =
            Arc::new(ThingVertexGenerator::load(storage.clone()).map_err(|err| Encoding { source: err })?);
        TypeManager::<WriteSnapshot<WALClient>>::initialise_types(
            storage.clone(),
            definition_key_generator.clone(),
            type_vertex_generator.clone(),
        )
        .map_err(|err| SchemaInitialise { source: err })?;
        let statistics = Arc::new(Statistics::new(storage.read_watermark()));

        Ok(Database::<WALClient> {
            name: name.as_ref().to_owned(),
            path: path.to_owned(),
            storage,
            definition_key_generator,
            type_vertex_generator,
            thing_vertex_generator,
            thing_statistics: statistics,
        })
    }

    fn load(path: &Path, name: impl AsRef<str>) -> Result<Database<WALClient>, DatabaseOpenError> {
        use DatabaseOpenError::{
            CheckpointCreate, CheckpointLoad, DurabilityRead, Encoding, SchemaInitialise, StatisticsInitialise,
            StorageOpen, WALOpen,
        };

        let wal = WAL::load(path).map_err(|err| WALOpen { source: err })?;
        let wal_last_sequence_number = wal.previous();
        let checkpoint = Checkpoint::open_latest(path).map_err(|err| CheckpointLoad { source: err })?;
        let storage = Arc::new(
            MVCCStorage::load::<EncodingKeyspace>(&name, path, WALClient::new(wal), &checkpoint)
                .map_err(|error| StorageOpen { source: error })?,
        );
        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        let thing_vertex_generator =
            Arc::new(ThingVertexGenerator::load(storage.clone()).map_err(|err| Encoding { source: err })?);
        TypeManager::<WriteSnapshot<WALClient>>::initialise_types(
            storage.clone(),
            definition_key_generator.clone(),
            type_vertex_generator.clone(),
        )
        .map_err(|err| SchemaInitialise { source: err })?;

        let statistics = storage
            .durability()
            .find_last_unsequenced_type::<Statistics>()
            .map_err(|err| DurabilityRead { source: err })?
            .unwrap_or_else(|| Statistics::new(SequenceNumber::MIN));
        let statistics =
            statistics.may_synchronise(storage.clone()).map_err(|err| StatisticsInitialise { source: err })?;

        let database = Database::<WALClient> {
            name: name.as_ref().to_owned(),
            path: path.to_owned(),
            storage,
            definition_key_generator,
            type_vertex_generator,
            thing_vertex_generator,
            thing_statistics: Arc::new(statistics),
        };

        let checkpoint_sequence_number =
            checkpoint.as_ref().unwrap().read_sequence_number().map_err(|err| CheckpointLoad { source: err })?;
        if checkpoint_sequence_number < wal_last_sequence_number {
            database.checkpoint().map_err(|err| CheckpointCreate { source: err })?;
        }

        Ok(database)
    }

    fn checkpoint(&self) -> Result<(), DatabaseCheckpointError> {
        let checkpoint =
            Checkpoint::new(&self.path).map_err(|err| DatabaseCheckpointError::CheckpointCreate { source: err })?;

        self.storage
            .checkpoint(&checkpoint)
            .map_err(|err| DatabaseCheckpointError::CheckpointCreate { source: err })?;

        checkpoint.finish().map_err(|err| DatabaseCheckpointError::CheckpointCreate { source: err })?;
        Ok(())
    }
}

impl<D> Database<D> {
    pub fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug)]
pub enum DatabaseOpenError {
    InvalidUnicodeName { name: OsString },
    DirectoryCreate { path: PathBuf, source: io::Error },
    StorageOpen { source: StorageOpenError },
    WALOpen { source: WALError },
    DurabilityOpen { source: DurabilityClientError },
    DurabilityRead { source: DurabilityClientError },
    CheckpointLoad { source: CheckpointLoadError },
    CheckpointCreate { source: DatabaseCheckpointError },
    Encoding { source: EncodingError },
    SchemaInitialise { source: ConceptWriteError },
    StatisticsInitialise { source: StatisticsInitialiseError },
}

impl fmt::Display for DatabaseOpenError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for DatabaseOpenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidUnicodeName { .. } => None,
            Self::DirectoryCreate { source, .. } => Some(source),
            Self::StorageOpen { source } => Some(source),
            Self::WALOpen { source } => Some(source),
            Self::DurabilityOpen { source } => Some(source),
            Self::DurabilityRead { source } => Some(source),
            Self::CheckpointLoad { source } => Some(source),
            Self::CheckpointCreate { source } => Some(source),
            Self::SchemaInitialise { source } => Some(source),
            Self::StatisticsInitialise { source } => Some(source),
            Self::Encoding { source } => Some(source),
        }
    }
}

#[derive(Debug)]
pub enum DatabaseCheckpointError {
    CheckpointCreate { source: CheckpointCreateError },
}

impl fmt::Display for DatabaseCheckpointError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for DatabaseCheckpointError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::CheckpointCreate { source } => Some(source),
        }
    }
}
