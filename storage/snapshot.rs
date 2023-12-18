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

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::sync::RwLock;

use itertools::Itertools;
use wal::SequenceNumber;

use crate::error::StorageError;
use crate::key::Key;
use crate::Storage;

pub enum Snapshot<'storage> {
    Read(ReadSnapshot<'storage>),
    Write(WriteSnapshot<'storage>),
}

impl<'storage> Snapshot<'storage> {

    pub fn iterate_prefix<'snapshot>(&'snapshot self, prefix: &[u8]) -> Box<dyn Iterator<Item=(Box<[u8]>, Box<[u8]>)> + 'snapshot> {
        match self {
            Snapshot::Read(snapshot) => Box::new(snapshot.iterate_prefix(prefix)),
            Snapshot::Write(snapshot) => Box::new(snapshot.iterate_prefix(prefix)),
        }
    }
}

pub struct ReadSnapshot<'storage> {
    storage: &'storage Storage,
    open_sequence_number: SequenceNumber,
}

impl<'storage> ReadSnapshot<'storage> {
    pub(crate) fn new(storage: &'storage Storage, open_sequence_number: SequenceNumber) -> ReadSnapshot {
        ReadSnapshot {
            storage: storage,
            open_sequence_number: open_sequence_number,
        }
    }

    fn iterate_prefix<'snapshot>(&'snapshot self, prefix: &[u8]) -> impl Iterator<Item=(Box<[u8]>, Box<[u8]>)> + 'snapshot {
        self.storage.iterate_prefix(prefix)
    }
}

pub struct WriteSnapshot<'storage> {
    storage: &'storage Storage,
    // TODO: replace with BTree Left-Right structure to allow concurrent read/write
    inserts: RwLock<BTreeMap<Vec<u8>, Vec<u8>>>,
    open_sequence_number: SequenceNumber,
}

impl<'storage> WriteSnapshot<'storage> {
    pub(crate) fn new(storage: &'storage Storage, open_sequence_number: SequenceNumber) -> WriteSnapshot {
        WriteSnapshot {
            storage: storage,
            inserts: RwLock::new(BTreeMap::new()),
            open_sequence_number: open_sequence_number,
        }
    }

    pub fn put(&self, key: &[u8]) {
        let mut map = self.inserts.write().unwrap();
        map.insert(key.into(), Storage::BYTES_EMPTY_VEC);
    }

    pub fn put_val(&self, key: &[u8], val: &[u8]) {
        let mut map = self.inserts.write().unwrap();
        map.insert(key.into(), val.into());
    }

    fn get(&self, key: &Key) -> Option<Vec<u8>> {
        // TODO merge with inserts & deletes
        self.storage.get(key)
    }

    fn iterate_prefix<'snapshot>(&'snapshot self, prefix: &[u8]) -> impl Iterator<Item=(Box<[u8]>, Box<[u8]>)> + 'snapshot {
        self.storage.iterate_prefix(prefix).merge(self.iterate_prefix_buffered(prefix))
    }

    fn iterate_prefix_buffered<'s>(&'s self, prefix: &[u8]) -> impl Iterator<Item=(Box<[u8]>, Box<[u8]>)> + 's {
        // TODO: avoid copy
        let p: Vec<u8> = prefix.into();
        let map = self.inserts.read().unwrap();
        // TODO: hold read lock while iterating so avoid collecting into array
        map.range::<Vec<u8>, _>(&p..).map(|(key, val)| {
            // TODO: we can avoid allocation here once we settle on a Key/Value struct
            (key.clone().into_boxed_slice(), val.clone().into_boxed_slice())
        }).collect::<Vec<_>>().into_iter()
    }
}

#[derive(Debug)]
pub struct WriteSnapshotError {
    pub kind: WriteSnapshotErrorKind,
}

#[derive(Debug)]
pub enum WriteSnapshotErrorKind {
    FailedGet { source: StorageError },
    FailedPut { source: StorageError },
}

impl Display for WriteSnapshotError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Error for WriteSnapshotError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            WriteSnapshotErrorKind::FailedGet { source, .. } => Some(source),
            WriteSnapshotErrorKind::FailedPut { source, .. } => Some(source),
        }
    }
}