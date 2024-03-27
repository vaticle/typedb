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

use std::{error::Error, fmt, sync::Arc};

use durability::DurabilityError;

use crate::{isolation_manager::IsolationError, keyspace::KeyspaceError};

#[derive(Debug)]
pub struct MVCCStorageError {
    pub storage_name: String,
    pub kind: MVCCStorageErrorKind,
}

#[derive(Debug)]
pub enum MVCCStorageErrorKind {
    FailedToDeleteStorage { source: std::io::Error },
    KeyspaceError { source: Arc<dyn Error + Sync + Send>, keyspace_name: &'static str },
    KeyspaceDeleteError { source: KeyspaceError },
    IsolationError { source: IsolationError },
    DurabilityError { source: DurabilityError },
}

impl fmt::Display for MVCCStorageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            MVCCStorageErrorKind::FailedToDeleteStorage { source, .. } => {
                write!(f, "MVCCStorageError.FailedToDeleteStorage caused by: '{}'", source)
            }
            MVCCStorageErrorKind::KeyspaceError { source, keyspace_name, .. } => {
                write!(f, "MVCCStorageError.KeyspaceError in keyspace '{}' caused by: '{}'", keyspace_name, source)
            }
            MVCCStorageErrorKind::KeyspaceDeleteError { source, .. } => {
                write!(f, "MVCCStorageError.KeyspaceDeleteError caused by: '{}'", source)
            }
            MVCCStorageErrorKind::IsolationError { source, .. } => {
                write!(f, "MVCCStorageError.IsolationError caused by: '{}'", source)
            }
            MVCCStorageErrorKind::DurabilityError { source, .. } => {
                write!(f, "MVCCStorageError.DurabilityError caused by: '{}'", source)
            }
        }
    }
}

impl Error for MVCCStorageError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            MVCCStorageErrorKind::FailedToDeleteStorage { source, .. } => Some(source),
            MVCCStorageErrorKind::KeyspaceError { source, .. } => Some(source),
            MVCCStorageErrorKind::IsolationError { source, .. } => Some(source),
            MVCCStorageErrorKind::DurabilityError { source, .. } => Some(source),
            MVCCStorageErrorKind::KeyspaceDeleteError { source } => Some(source),
        }
    }
}
