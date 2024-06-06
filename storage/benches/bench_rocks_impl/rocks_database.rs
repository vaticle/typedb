/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use non_transactional_rocks::NonTransactionalRocks;
use rocksdb::{Options, WriteOptions};
use storage::StorageOpenError;

use crate::{bench_rocks_impl::rocks_database::typedb_database::TypeDBDatabase, CLIArgs};

fn database_options(args: &CLIArgs) -> Options {
    let mut opts = Options::default();
    opts.create_if_missing(true);
    if let Some(write_buffer_size_mb) = args.rocks_write_buffer_mb {
        opts.set_write_buffer_size(write_buffer_size_mb * 1024 * 1024);
    }
    opts
}

fn write_options(args: &CLIArgs) -> WriteOptions {
    let mut write_options = WriteOptions::default();
    if let Some(disable_wal) = args.rocks_disable_wal {
        write_options.disable_wal(disable_wal);
    }
    if let Some(set_sync) = args.rocks_set_sync {
        write_options.set_sync(set_sync);
    }
    write_options
}

pub fn rocks<const N_DATABASES: usize>(args: &CLIArgs) -> Result<NonTransactionalRocks<N_DATABASES>, rocksdb::Error> {
    NonTransactionalRocks::<N_DATABASES>::setup(database_options(args), write_options(args))
}

pub fn create_typedb<const N_DATABASES: usize>() -> Result<TypeDBDatabase<N_DATABASES>, StorageOpenError> {
    TypeDBDatabase::<N_DATABASES>::setup()
}

mod non_transactional_rocks {
    use std::iter::zip;

    use rocksdb::{Options, WriteBatch, WriteOptions, DB};
    use test_utils::{create_tmp_dir, TempDir};

    use crate::{RocksDatabase, RocksWriteBatch};

    pub struct NonTransactionalRocks<const N_DATABASES: usize> {
        databases: [DB; crate::N_DATABASES],
        write_options: WriteOptions,
        path: TempDir,
    }

    impl<const N_DATABASES: usize> NonTransactionalRocks<N_DATABASES> {
        pub(super) fn setup(options: Options, write_options: WriteOptions) -> Result<Self, rocksdb::Error> {
            let path = create_tmp_dir();
            let databases = core::array::from_fn(|i| DB::open(&options, path.join(format!("db_{i}"))).unwrap());

            Ok(Self { path, databases, write_options })
        }
    }

    impl<const N_DATABASES: usize> RocksDatabase for NonTransactionalRocks<N_DATABASES> {
        fn open_batch(&self) -> impl RocksWriteBatch {
            let write_batches = core::array::from_fn(|_| WriteBatch::default());
            NonTransactionalWriteBatch { database: self, write_batches }
        }
    }

    pub struct NonTransactionalWriteBatch<'this, const N_DATABASES: usize> {
        database: &'this NonTransactionalRocks<N_DATABASES>,
        write_batches: [WriteBatch; N_DATABASES],
    }

    impl<'this, const N_DATABASES: usize> RocksWriteBatch for NonTransactionalWriteBatch<'this, N_DATABASES> {
        type CommitError = rocksdb::Error;
        fn put(&mut self, database_index: usize, key: [u8; crate::KEY_SIZE]) {
            self.write_batches[database_index].put(key, [])
        }

        fn commit(self) -> Result<(), rocksdb::Error> {
            let write_options = &self.database.write_options;
            for (db, write_batch) in zip(&self.database.databases, self.write_batches) {
                db.write_opt(write_batch, write_options)?
            }
            Ok(())
        }
    }
}

mod typedb_database {
    use std::sync::Arc;

    use bytes::byte_array::ByteArray;
    use durability::wal::WAL;
    use storage::{
        durability_client::WALClient,
        key_value::StorageKeyArray,
        keyspace::{KeyspaceId, KeyspaceSet},
        snapshot::{CommittableSnapshot, SnapshotError, WritableSnapshot, WriteSnapshot},
        MVCCStorage, StorageOpenError,
    };
    use test_utils::{create_tmp_dir, TempDir};

    use crate::{RocksDatabase, RocksWriteBatch, KEY_SIZE};

    pub struct TypeDBDatabase<const N_DATABASES: usize> {
        storage: Arc<MVCCStorage<WALClient>>,
        pub path: TempDir,
    }

    impl<const N_DATABASES: usize> TypeDBDatabase<N_DATABASES> {
        pub(super) fn setup() -> Result<Self, StorageOpenError> {
            let name = "bench_rocks__typedb";
            let path = create_tmp_dir();
            let wal = WAL::create(&path).unwrap();
            let storage =
                Arc::new(MVCCStorage::<WALClient>::create::<BenchKeySpace>(name, &path, WALClient::new(wal))?);
            Ok(Self { path, storage })
        }
    }

    impl<const N_DATABASES: usize> RocksDatabase for TypeDBDatabase<N_DATABASES> {
        fn open_batch(&self) -> impl RocksWriteBatch {
            TypeDBSnapshot { snapshot: self.storage.clone().open_snapshot_write() }
        }
    }

    pub struct TypeDBSnapshot {
        snapshot: WriteSnapshot<WALClient>,
    }

    impl TypeDBSnapshot {
        const KEYSPACES: [BenchKeySpace; 1] = [BenchKeySpace { id: 0 }];
        const KEYSPACE_NAMES: [&'static str; 1] = ["BenchKeySpace[1]"];
    }
    impl RocksWriteBatch for TypeDBSnapshot {
        type CommitError = SnapshotError;
        fn put(&mut self, database_index: usize, key: [u8; KEY_SIZE]) {
            debug_assert_eq!(0, database_index, "Not implemented for multiple databases");
            self.snapshot.put(StorageKeyArray::new(Self::KEYSPACES[0], ByteArray::inline(key, KEY_SIZE)))
        }

        fn commit(self) -> Result<(), Self::CommitError> {
            self.snapshot.commit()?;
            Ok(())
        }
    }

    #[derive(Copy, Clone)]
    pub struct BenchKeySpace {
        id: u8,
    }

    impl KeyspaceSet for BenchKeySpace {
        fn iter() -> impl Iterator<Item = Self> {
            TypeDBSnapshot::KEYSPACES.into_iter()
        }

        fn id(&self) -> KeyspaceId {
            KeyspaceId(self.id)
        }

        fn name(&self) -> &'static str {
            &TypeDBSnapshot::KEYSPACE_NAMES[self.id as usize]
        }
    }
}
