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
    collections::HashMap,
    error::Error,
    ffi::OsString,
    fmt, fs, io,
    path::{Path, PathBuf},
};

use database::{Database, DatabaseRecoverError};
use durability::wal::WAL;
use itertools::Itertools;

pub struct Server {
    data_directory: PathBuf,
    databases: HashMap<String, Database<WAL>>,
}

impl Server {
    pub fn recover(data_directory: impl AsRef<Path>) -> Result<Self, ServerRecoverError> {
        use ServerRecoverError::*;
        let data_directory = data_directory.as_ref();

        if !data_directory.exists() {
            fs::create_dir_all(data_directory)
                .map_err(|error| CouldNotCreateDataDirectory { path: data_directory.to_owned(), source: error })?;
        } else if !data_directory.is_dir() {
            return Err(NotADirectory { path: data_directory.to_owned() });
        }

        let databases = fs::read_dir(data_directory)
            .map_err(|error| CouldNotReadDataDirectory { path: data_directory.to_owned(), source: error })?
            .map(|entry| {
                let entry = entry
                    .map_err(|error| CouldNotReadDataDirectory { path: data_directory.to_owned(), source: error })?;
                let database_name = entry.file_name().into_string().map_err(|name| InvalidUnicodeName { name })?;
                let database = Database::recover(&entry.path(), &database_name)
                    .map_err(|error| DatabaseRecover { source: error })?;
                Ok((database_name, database))
            })
            .try_collect()?;
        let data_directory = data_directory.to_owned();
        Ok(Self { data_directory, databases })
    }

    pub fn serve(mut self) {
        self.databases
            .entry("test".to_owned())
            .or_insert_with(|| Database::recover(&self.data_directory.join("test"), "test").unwrap());
        dbg!(self.databases);
    }
}

#[derive(Debug)]
pub enum ServerRecoverError {
    NotADirectory { path: PathBuf },
    CouldNotCreateDataDirectory { path: PathBuf, source: io::Error },
    CouldNotReadDataDirectory { path: PathBuf, source: io::Error },
    InvalidUnicodeName { name: OsString },
    DatabaseRecover { source: DatabaseRecoverError },
}

impl Error for ServerRecoverError {}

impl fmt::Display for ServerRecoverError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
