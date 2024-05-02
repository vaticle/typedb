/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

/*
This file should comprise a set of low-level tests relating to MVCC.

1. We should be able to open a new snapshot (check open sequence number) and commit it. The next sequence number should have advanced by one (ie. watermark).

2. We should be able to open a previous snapshot, and doing reads on this version should ignore all newer versions

3. We should be able to open a previous snapshot in write, and the commit should fail if a subsequent commit has a conflicting operation
   Note: edge case is when the commit records have been purged from memory. Isolation manager should be able to retrieve them again from the Durability service on demand.
   Note: let's write this test first, and leave it red. This will induce a refactor of the Timeline - which is the next task.

4. We should be able to configure that a cleanup of old versionsn of key is run after T has elapsed that deletes old versions of data we no longer want to retain
   We want the time keeping component to be received from the durability service, which should be able to tell us the last sequence number
   before a specific time (it should be able to binary search its WAL log files and check the dates on them to find this information).
   After cleanup is run, we should get a good error if a version that is too-old is opened.
   After cleanup is run, if we iterate directly on the storage layer, we should be able to confirm the keys are actually not present anymore (Rocks may defer the disk delete till compaction, but to us they are "gone").

 */
mod test_common;

use std::{path::Path, sync::Arc};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference};
use durability::wal::WAL;
use storage::{
    key_value::{StorageKey, StorageKeyArray, StorageKeyReference},
    keyspace::{KeyspaceId, KeyspaceSet},
    snapshot::ReadableSnapshot,
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging};

test_keyspace_set! {
    Keyspace => 0: "keyspace",
}

use self::TestKeyspaceSet::Keyspace;

const KEY_1: [u8; 4] = [0x0, 0x0, 0x0, 0x1];
const KEY_2: [u8; 4] = [0x0, 0x0, 0x0, 0x2];
const VALUE_0: [u8; 1] = [0x0];
const VALUE_1: [u8; 1] = [0x1];
const VALUE_2: [u8; 1] = [0x2];

fn setup_storage(storage_path: &Path) -> Arc<MVCCStorage<WAL>> {
    Arc::new(MVCCStorage::open::<TestKeyspaceSet>("storage", storage_path).unwrap())
}

#[test]
fn test_commit_increments_watermark() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);
    let wm_initial = storage.read_watermark();
    let snapshot_0 = storage.clone().open_snapshot_write();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    snapshot_0.put_val(key_1.clone(), ByteArray::copy(&VALUE_1));
    snapshot_0.commit().unwrap();

    assert_eq!(wm_initial.number() + 1, storage.read_watermark().number());
}

#[test]
fn test_reading_snapshots() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let key_1: &StorageKey<'_, 48> =
        &StorageKey::Reference(StorageKeyReference::new(Keyspace, ByteReference::new(&KEY_1)));

    let snapshot_write_0 = storage.clone().open_snapshot_write();
    snapshot_write_0.put_val(StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1)), ByteArray::copy(&VALUE_0));
    snapshot_write_0.commit().unwrap();

    let watermark_0 = storage.read_watermark();

    let snapshot_read_0 = storage.clone().open_snapshot_read();
    assert_eq!(snapshot_read_0.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0);

    let snapshot_write_1 = storage.clone().open_snapshot_write();
    snapshot_write_1.put_val(StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1)), ByteArray::copy(&VALUE_1));
    let snapshot_read_01 = storage.clone().open_snapshot_read();
    assert_eq!(snapshot_read_0.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0);
    assert_eq!(snapshot_read_01.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0);

    let result_write_1 = snapshot_write_1.commit();
    assert!(result_write_1.is_ok());

    let snapshot_read_1 = storage.clone().open_snapshot_read();
    assert_eq!(snapshot_read_0.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0);
    assert_eq!(snapshot_read_01.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0);
    assert_eq!(snapshot_read_1.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_1);
    snapshot_read_1.close_resources();
    snapshot_read_01.close_resources();
    snapshot_read_0.close_resources();

    // Read from further in the past.
    let snapshot_read_02 = storage.open_snapshot_read_at(watermark_0).unwrap();
    assert_eq!(snapshot_read_02.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0);
    snapshot_read_02.close_resources();
}

#[test]
fn test_conflicting_update_fails() {
    // TODO: Why does this exist if we have separate isolation tests?
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let key_1 = StorageKey::new_owned(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKey::new_owned(Keyspace, ByteArray::copy(&KEY_2));

    let snapshot_write_0 = storage.clone().open_snapshot_write();
    snapshot_write_0.put_val(key_1.clone().into_owned_array(), ByteArray::copy(&VALUE_0));
    snapshot_write_0.commit().unwrap();

    let watermark_after_initial_write = storage.read_watermark();

    {
        let snapshot_write_11 = storage.clone().open_snapshot_write();
        let snapshot_write_21 = storage.clone().open_snapshot_write();
        snapshot_write_11.delete(key_1.clone().into_owned_array());
        snapshot_write_21.get_required(key_1.clone()).unwrap();
        snapshot_write_21.put_val(key_2.clone().into_owned_array(), ByteArray::copy(&VALUE_2));
        let result_write_11 = snapshot_write_11.commit();
        assert!(result_write_11.is_ok());
        let result_write_21 = snapshot_write_21.commit();
        assert!(result_write_21.is_err());
    }

    {
        // Try the same, with the snapshot opened in the past
        let snapshot_write_at_0 = storage.open_snapshot_write_at(watermark_after_initial_write).unwrap();
        snapshot_write_at_0.get_required(key_1.clone()).unwrap();
        snapshot_write_at_0.put_val(key_2.clone().into_owned_array(), ByteArray::copy(&VALUE_2));
        let result_write_at_0 = snapshot_write_at_0.commit();
        assert!(result_write_at_0.is_err());
    }
}

#[test]
fn test_open_snapshot_write_at() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let key_1: &StorageKey<'_, 48> =
        &StorageKey::Reference(StorageKeyReference::new(Keyspace, ByteReference::new(&KEY_1)));

    let watermark_init = storage.read_watermark();

    let snapshot_write_0 = storage.clone().open_snapshot_write();
    snapshot_write_0.put_val(StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1)), ByteArray::copy(&VALUE_0));
    snapshot_write_0.commit().unwrap();

    let watermark_0 = storage.read_watermark();

    let snapshot_read_0 = storage.clone().open_snapshot_read();
    assert_eq!(snapshot_read_0.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0);
    snapshot_read_0.close_resources();

    let snapshot_write_1 = storage.clone().open_snapshot_write_at(watermark_init).unwrap();
    snapshot_write_1.put_val(StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1)), ByteArray::copy(&VALUE_1));
    snapshot_write_1.commit().unwrap();

    let snapshot_read_1 = storage.open_snapshot_read();
    assert_eq!(snapshot_read_1.get::<128>(key_1.as_reference()).unwrap().unwrap().bytes(), VALUE_0); // FIXME: value overwrite currently unsupported
    snapshot_read_1.close_resources();
}
