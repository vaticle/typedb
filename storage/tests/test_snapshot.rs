/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

mod test_common;

use std::sync::Arc;

use bytes::byte_array::ByteArray;
use durability::wal::WAL;
use logger::result::ResultExt;
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use storage::{
    key_range::KeyRange,
    key_value::{StorageKey, StorageKeyArray},
    keyspace::{KeyspaceId, KeyspaceSet},
    snapshot::ReadableSnapshot,
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging};

test_keyspace_set! {
    Keyspace => 0: "keyspace",
}
use self::TestKeyspaceSet::Keyspace;

#[test]
fn snapshot_buffered_put_get() {
    init_logging();

    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());

    let snapshot = storage.open_snapshot_write();

    let key_1 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x0, 0x0, 0x1]));
    let key_2 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0x10]));
    let key_3 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0xff]));
    let key_4 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x2, 0x0, 0xff]));
    let value_1 = ByteArray::copy(&[0, 0, 0, 0]);
    snapshot.put_val(key_1.clone(), value_1.clone());
    snapshot.put(key_2.clone());
    snapshot.put(key_3);
    snapshot.put(key_4);

    assert_eq!(snapshot.get(StorageKey::Array(key_1).as_reference()).unwrap(), Some(value_1));
    assert_eq!(snapshot.get::<48>(StorageKey::Array(key_2).as_reference()).unwrap(), Some(ByteArray::empty()));

    let key_5 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0xff, 0xff, 0xff]));
    assert_eq!(snapshot.get::<48>(StorageKey::Array(key_5).as_reference()).unwrap(), None);
    snapshot.close_resources();
}

#[test]
fn snapshot_buffered_put_iterate() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());

    let snapshot = storage.open_snapshot_write();

    let key_1 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x0, 0x0, 0x1]));
    let key_2 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0x10]));
    let key_3 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0xff]));
    let key_4 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x2, 0x0, 0xff]));
    snapshot.put(key_1);
    snapshot.put(key_2.clone());
    snapshot.put(key_3.clone());
    snapshot.put(key_4.clone());

    let key_prefix = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1]));
    let items: Result<Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, ByteArray<BUFFER_VALUE_INLINE>)>, _> = snapshot
        .iterate_range(KeyRange::new_within(StorageKey::Array(key_prefix), false))
        .collect_cloned_vec(|k, v| (StorageKeyArray::from(k), ByteArray::from(v)));
    assert_eq!(items.unwrap(), vec![(key_2, ByteArray::empty()), (key_3, ByteArray::empty())]);
    snapshot.close_resources();
}

#[test]
fn snapshot_buffered_delete() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());

    let snapshot = storage.open_snapshot_write();

    let key_1 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x0, 0x0, 0x1]));
    let key_2 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0x10]));
    let key_3 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0xff]));
    let key_4 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x2, 0x0, 0xff]));
    snapshot.put(key_1);
    snapshot.put(key_2.clone());
    snapshot.put(key_3.clone());
    snapshot.put(key_4.clone());

    snapshot.delete(key_3.clone());

    assert_eq!(snapshot.get::<48>(StorageKey::Array(key_3).as_reference()).unwrap(), None);

    let key_prefix = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1]));
    let items: Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, ByteArray<BUFFER_VALUE_INLINE>)> = snapshot
        .iterate_range(KeyRange::new_within(StorageKey::Array(key_prefix), false))
        .collect_cloned_vec(|k, v| (StorageKeyArray::from(k), ByteArray::from(v)))
        .unwrap();
    assert_eq!(items, vec![(key_2, ByteArray::empty())]);
    snapshot.close_resources();
}

#[test]
fn snapshot_read_through() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());

    let key_1 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x0, 0x0, 0x1]));
    let key_2 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0x10]));
    let key_3 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x0, 0xff]));
    let key_4 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x2, 0x0, 0xff]));

    let snapshot = storage.clone().open_snapshot_write();
    snapshot.put(key_1.clone());
    snapshot.put(key_2.clone());
    snapshot.put(key_3.clone());
    snapshot.put(key_4.clone());
    snapshot.commit().unwrap_or_log();

    let key_5 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1, 0x2, 0x0]));

    // test put - iterate read-through
    let snapshot = storage.open_snapshot_write();
    snapshot.put(key_5.clone());

    let key_prefix = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x1]));
    let key_values: Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, ByteArray<BUFFER_VALUE_INLINE>)> = snapshot
        .iterate_range(KeyRange::new_within(StorageKey::Array(key_prefix.clone()), false))
        .collect_cloned_vec(|k, v| (StorageKeyArray::from(k), ByteArray::from(v)))
        .unwrap();
    assert_eq!(
        key_values,
        vec![
            (key_2.clone(), ByteArray::empty()),
            (key_3.clone(), ByteArray::empty()),
            (key_5.clone(), ByteArray::empty()),
        ]
    );

    // test delete-iterate read-through
    snapshot.delete(key_2.clone());
    let key_values: Vec<(StorageKeyArray<BUFFER_KEY_INLINE>, ByteArray<BUFFER_VALUE_INLINE>)> = snapshot
        .iterate_range(KeyRange::new_within(StorageKey::Array(key_prefix), false))
        .collect_cloned_vec(|k, v| (StorageKeyArray::from(k), ByteArray::from(v)))
        .unwrap();
    assert_eq!(key_values, vec![(key_3, ByteArray::empty()), (key_5, ByteArray::empty())]);
    snapshot.close_resources();
}

#[test]
fn snapshot_delete_reinserted() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());

    let key_1 = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x0, 0x0, 0x1]));
    let value_0 = ByteArray::copy(&[0, 0, 0, 0]);
    let value_1 = ByteArray::copy(&[0, 0, 0, 1]);

    let snapshot_0 = storage.clone().open_snapshot_write();
    snapshot_0.put_val(key_1.clone(), value_0);
    snapshot_0.commit().unwrap();

    let snapshot_1 = storage.clone().open_snapshot_write();
    snapshot_1.put_val(key_1.clone(), value_1);
    snapshot_1.delete(key_1.clone());
    snapshot_1.commit().unwrap();

    let snapshot_2 = storage.open_snapshot_read();
    assert_eq!(snapshot_2.get::<BUFFER_KEY_INLINE>(StorageKey::Array(key_1).as_reference()).unwrap(), None);
    snapshot_2.close_resources();
}
