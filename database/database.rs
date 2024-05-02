/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use core::fmt;
use std::{
    error::Error,
    fs, io,
    path::{Path, PathBuf},
    sync::Arc,
};

use concept::{error::ConceptWriteError, type_::type_manager::TypeManager};
use durability::DurabilityService;
use encoding::{
    error::EncodingError,
    graph::{thing::vertex_generator::ThingVertexGenerator, type_::vertex_generator::TypeVertexGenerator},
    EncodingKeyspace,
};
use storage::{snapshot::WriteSnapshot, MVCCStorage, StorageOpenError};

pub struct Database<D> {
    name: String,
    path: PathBuf,
    pub(super) storage: Arc<MVCCStorage<D>>,
    pub(super) type_vertex_generator: Arc<TypeVertexGenerator>,
    pub(super) thing_vertex_generator: Arc<ThingVertexGenerator>,
}

impl<D> fmt::Debug for Database<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Database").field("name", &self.name).field("path", &self.path).finish_non_exhaustive()
    }
}

impl<D> Database<D> {
    pub fn open(path: &Path, database_name: impl AsRef<str>) -> Result<Self, DatabaseOpenError>
    where
        D: DurabilityService,
    {
        use DatabaseOpenError::{DirectoryCreate, Encoding, SchemaInitialise, StorageOpen};

        let name = database_name.as_ref();
        if !path.exists() {
            fs::create_dir(path).map_err(|error| DirectoryCreate { path: path.to_owned(), source: error })?;
        }
        let storage =
            Arc::new(MVCCStorage::open::<EncodingKeyspace>(name, path).map_err(|error| StorageOpen { source: error })?);
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        let thing_vertex_generator =
            Arc::new(ThingVertexGenerator::load(storage.clone()).map_err(|err| Encoding { source: err })?);
        TypeManager::<WriteSnapshot<D>>::initialise_types(storage.clone(), type_vertex_generator.clone())
            .map_err(|err| SchemaInitialise { source: err })?;

        Ok(Self {
            name: name.to_owned(),
            path: path.to_owned(),
            storage,
            type_vertex_generator,
            thing_vertex_generator,
        })
    }
}

#[derive(Debug)]
pub enum DatabaseOpenError {
    DirectoryCreate { path: PathBuf, source: io::Error },
    StorageOpen { source: StorageOpenError },
    Encoding { source: EncodingError },
    SchemaInitialise { source: ConceptWriteError },
}

impl fmt::Display for DatabaseOpenError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for DatabaseOpenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::DirectoryCreate { source, .. } => Some(source),
            Self::StorageOpen { source } => Some(source),
            Self::SchemaInitialise { source } => Some(source),
            Self::Encoding { source } => Some(source),
        }
    }
}
