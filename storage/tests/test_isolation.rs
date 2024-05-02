/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

mod test_common;

use std::{path::Path, sync::Arc};

use bytes::{byte_array::ByteArray, byte_reference::ByteReference};
use durability::{wal::WAL, DurabilityService};
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use storage::{
    isolation_manager::IsolationConflict,
    key_range::KeyRange,
    key_value::{StorageKey, StorageKeyArray, StorageKeyReference},
    keyspace::{KeyspaceId, KeyspaceSet},
    snapshot::{ReadableSnapshot, SnapshotError, WriteSnapshot},
    MVCCStorage, StorageCommitError,
};
use test_utils::{create_tmp_dir, init_logging};

test_keyspace_set! {
    Keyspace => 0: "keyspace",
}
use self::TestKeyspaceSet::Keyspace;

macro_rules! fails_without_serializability {
    ($x:expr) => {
        assert!(!$x);
    };
}

const KEY_1: [u8; 4] = [0x0, 0x0, 0x0, 0x1];
const KEY_2: [u8; 4] = [0x0, 0x0, 0x0, 0x2];
const KEY_3: [u8; 4] = [0x0, 0x0, 0x0, 0x3];
const VALUE_1: [u8; 1] = [0x0];
const VALUE_2: [u8; 1] = [0x1];
const VALUE_3: [u8; 1] = [0x88];

fn setup_storage(storage_path: &Path) -> Arc<MVCCStorage<WAL>> {
    let storage = Arc::new(MVCCStorage::open::<TestKeyspaceSet>("storage", storage_path).unwrap());

    let snapshot = storage.clone().open_snapshot_write();
    snapshot.put_val(StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1)), ByteArray::copy(&VALUE_1));
    snapshot.put_val(StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2)), ByteArray::copy(&VALUE_2));
    snapshot.commit().unwrap();

    storage
}

#[test]
fn commits_isolated() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_read();

    let key_3 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_3));
    let value_3 = ByteArray::copy(&VALUE_3);
    snapshot_1.put_val(key_3.clone(), value_3.clone());
    snapshot_1.commit().unwrap();

    let get: Option<ByteArray<BUFFER_KEY_INLINE>> = snapshot_2.get(StorageKeyReference::from(&key_3)).unwrap();
    assert!(get.is_none());
    let prefix: StorageKey<'_, BUFFER_KEY_INLINE> =
        StorageKey::Array(StorageKeyArray::new(Keyspace, ByteArray::copy(&[0x0_u8])));
    let range = KeyRange::new_within(prefix, false);
    let retrieved_count = snapshot_2.iterate_range(range.clone()).count();
    assert_eq!(retrieved_count, 2);

    let snapshot_3 = storage.open_snapshot_read();
    let get: Option<ByteArray<BUFFER_KEY_INLINE>> = snapshot_3.get(StorageKeyReference::from(&key_3)).unwrap();
    assert!(matches!(get, Some(_value_3)));
    let retrieved_count = snapshot_3.iterate_range(range.clone()).count();
    assert_eq!(retrieved_count, 3);
}

///
/// 1. Open two snapshots on the same version
/// 2. S1 - get_required(K1)
/// 3. S2 - delete(K1)
///
#[test]
fn g0_update_conflicts_fail() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_write();

    let key_1 = StorageKey::Reference(StorageKeyReference::new(Keyspace, ByteReference::new(&KEY_1)));

    snapshot_1.get_required(key_1.clone()).unwrap();

    snapshot_2.delete(key_1.clone().into_owned_array());

    let result_1 = snapshot_1.commit();
    assert!(result_1.is_ok());

    let result_2 = snapshot_2.commit();
    assert!(
        matches!(result_2, Err(SnapshotError::Commit { source: StorageCommitError::Isolation { .. }, .. }, ..)),
        "{:?}",
        result_2
    );
}

#[ignore] // TODO: This currently fails because of the behaviour flagged in typedb#7033
#[test]
fn g0_dirty_writes() {
    // With snapshots, all writes happen together at commit time.
    // Hence, all writes of t_i happen before t_j or vice-versa, and no ww-ww cycles are possible
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_write();

    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));

    let value_11 = ByteArray::inline([11], 1);
    let value_12 = ByteArray::inline([12], 1);
    let value_21 = ByteArray::inline([21], 1);
    let value_22 = ByteArray::inline([22], 1);

    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_11.bytes()));
    snapshot_2.put_val(key_1.to_owned(), ByteArray::copy(value_12.bytes()));
    snapshot_2.put_val(key_2.to_owned(), ByteArray::copy(value_22.bytes()));
    let result_2 = snapshot_2.commit();

    // Check state
    match result_2 {
        Ok(_) => {
            let reader_after_2 = storage.clone().open_snapshot_read();
            assert_eq!(
                reader_after_2.get::<128>(StorageKeyReference::from(&key_1)).unwrap().unwrap().bytes(),
                value_12.bytes()
            );
            assert_eq!(
                reader_after_2.get::<128>(StorageKeyReference::from(&key_2)).unwrap().unwrap().bytes(),
                value_22.bytes()
            );
            reader_after_2.close_resources();
        }
        Err(_) => panic!(),
    }

    // Continue
    snapshot_1.put_val(key_2.to_owned(), ByteArray::copy(value_21.bytes()));
    let result_1 = snapshot_1.commit();

    if let Ok(()) = result_1 {
        let reader_after_1 = storage.clone().open_snapshot_read();
        assert_eq!(
            reader_after_1.get::<128>(StorageKeyReference::from(&key_1)).unwrap().unwrap().bytes(),
            value_11.bytes()
        );
        assert_eq!(
            reader_after_1.get::<128>(StorageKeyReference::from(&key_2)).unwrap().unwrap().bytes(),
            value_21.bytes()
        );
        // reader_after_1.close();
    }
}

#[test]
fn g1a_aborted_writes() {
    // This requires a wr edge which do not exist under snapshots
    // With snapshots, concurrent transactions cannot see each others writes.
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let value_1_0 = ByteArray::inline([10], 1);
    let value_1_1 = ByteArray::inline([11], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_1_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_write();
    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_1_1.bytes()));
    let read_2 = snapshot_2.get::<128>(StorageKeyReference::from(&key_1));
    snapshot_1.close_resources();
    assert_eq!(value_1_0.bytes(), read_2.unwrap().unwrap().bytes());
}

#[test]
fn g1b_intermediate_read() {
    // This requires a wr edge which do not exist under snapshots
    // Since all writes happen together at commit time, either the initial or the final value is read.
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let value_1_0 = ByteArray::inline([10], 1);
    let value_1_1i = ByteArray::inline([111], 1);
    let value_1_1f = ByteArray::inline([112], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_1_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.open_snapshot_write();
    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_1_1i.bytes()));
    let read_2 = snapshot_2.get::<128>(StorageKeyReference::from(&key_1));
    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_1_1f.bytes()));
    let result_1 = snapshot_1.commit();
    assert!(result_1.is_ok());
    assert_eq!(value_1_0.bytes(), read_2.unwrap().unwrap().bytes()); // No direct problem - We read the initial value.
}

#[test]
fn g1c_circular_info_flow() {
    // These are ww-ww or wr-ww cycles, which cannot exist.
    // Intuitively, since concurrent transactions cannot read each others' writes, circular info flow is impossible.
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));
    let value_1_0 = ByteArray::inline([10], 1);
    let value_1_1 = ByteArray::inline([11], 1);
    let value_2_0 = ByteArray::inline([20], 1);
    let value_2_2 = ByteArray::inline([22], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_1_0.bytes()));
    snapshot_setup.put_val(key_2.to_owned(), ByteArray::copy(value_2_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.open_snapshot_write();
    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_1_1.bytes()));
    let read_1_2 = snapshot_2.get::<128>(StorageKeyReference::from(&key_1));
    snapshot_2.put_val(key_2.to_owned(), ByteArray::copy(value_2_2.bytes()));
    let read_2_1 = snapshot_1.get::<128>(StorageKeyReference::from(&key_2));

    assert_eq!(value_1_0.bytes(), read_1_2.unwrap().unwrap().bytes());
    assert_eq!(value_2_0.bytes(), read_2_1.unwrap().unwrap().bytes());
}

#[test]
fn p4_g_cursor_lost_update() {
    // This requires a rw-ww cycle, which can and does happen here.
    // Other Snapshot Isolation systems would disallow the conflict on KEY_1
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let value_0 = ByteArray::inline([0], 1);

    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_write();
    let read_1 = snapshot_1.get::<128>(StorageKeyReference::from(&key_1)).unwrap().unwrap();
    let read_2 = snapshot_2.get::<128>(StorageKeyReference::from(&key_1)).unwrap().unwrap();
    let to_write_1 = ByteArray::inline([read_1.bytes()[0] + 1], 1);
    let to_write_2 = ByteArray::inline([read_2.bytes()[0] + 1], 1);

    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(to_write_1.bytes()));
    snapshot_2.put_val(key_1.to_owned(), ByteArray::copy(to_write_2.bytes()));
    let result_1 = snapshot_1.commit();
    let result_2 = snapshot_2.commit();

    if result_1.is_ok() && result_2.is_ok() {
        let snapshot_verify = storage.open_snapshot_read();
        let read_verify = snapshot_verify.get::<128>(StorageKeyReference::from(&key_1)).unwrap().unwrap();
        fails_without_serializability!(2 == read_verify.bytes()[0]); // This does fail
    }
}

#[test]
fn g_single_read_skew() {
    // This requires an rw-wr cycle. But wr edges are impossible
    // Intuitively, read_21 reads the initial one for both keys, hence there is no skewed read.
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));
    let value_1_0 = ByteArray::inline([10], 1);
    let value_1_2 = ByteArray::inline([12], 1);
    let value_2_0 = ByteArray::inline([20], 1);
    let value_2_2 = ByteArray::inline([22], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_1_0.bytes()));
    snapshot_setup.put_val(key_2.to_owned(), ByteArray::copy(value_2_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.open_snapshot_write();

    let read_1_1 = snapshot_1.get::<128>(StorageKeyReference::from(&key_1));
    snapshot_2.put_val(key_1.to_owned(), ByteArray::copy(value_1_2.bytes()));
    snapshot_2.put_val(key_2.to_owned(), ByteArray::copy(value_2_2.bytes()));
    let read_2_1 = snapshot_1.get::<128>(StorageKeyReference::from(&key_2));

    assert_eq!(value_1_0.bytes(), read_1_1.unwrap().unwrap().bytes());
    assert_eq!(value_2_0.bytes(), read_2_1.unwrap().unwrap().bytes());

    let result_1 = snapshot_1.commit();
    let result_2 = snapshot_2.commit();
    assert!(result_1.is_ok() && result_2.is_ok()); // No reason it shouldn't succeed
}

#[test]
fn g2_item_write_skew_disjoint_read() {
    // This requires an rw-rw cycle, which is possible and does happen.
    // The example shows a violation of an invariant x+y <= 1.
    //   t1 checks x==0, sets y=1; t2 checks y==0, sets x=1
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));
    let value_0 = ByteArray::inline([10], 1);
    let value_1 = ByteArray::inline([11], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_0.bytes()));
    snapshot_setup.put_val(key_2.to_owned(), ByteArray::copy(value_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_write();

    let read_2_1 = snapshot_1.get::<128>(StorageKeyReference::from(&key_2));
    if read_2_1.unwrap().unwrap().bytes()[0] == 0 {
        snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_1.bytes()));
    }
    let read_1_2 = snapshot_2.get::<128>(StorageKeyReference::from(&key_1));
    if read_1_2.unwrap().unwrap().bytes()[0] == 0 {
        snapshot_2.put_val(key_2.to_owned(), ByteArray::copy(value_1.bytes()));
    }

    let result_1 = snapshot_1.commit();
    let result_2 = snapshot_2.commit();

    assert!(result_1.is_ok() && result_2.is_ok());
    let reader_after = storage.open_snapshot_read();
    let sum = reader_after.get::<128>(StorageKeyReference::from(&key_1)).unwrap().unwrap().bytes()[0]
        + reader_after.get::<128>(StorageKeyReference::from(&key_2)).unwrap().unwrap().bytes()[0];
    fails_without_serializability!(sum <= 1);
}

#[test]
fn g2_predicate_anti_dependency_cycles() {
    // This also shows a rw-rw cycle, but with a predicate (realised as an iterate_prefix)
    // t1 sums up a range, and adds an element to it. t2 sums up the same range and adds an element to it.
    //      (Strictly, we only need to insert elements into the intersection of the ranges)
    // One of their reads would not be repeatable under any serialisation.
    init_logging();
    let key_4_bytes = [0x0, 0x0, 0x0, 0x4];
    let key_3 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_3));
    let key_4 = StorageKeyArray::new(Keyspace, ByteArray::copy(&key_4_bytes));

    let key_prefix = StorageKeyArray::<BUFFER_KEY_INLINE>::from((Keyspace, [0x0]));
    let prefix = KeyRange::new_within(StorageKey::Array(key_prefix), false);
    let value_31 = ByteArray::inline([30], 1);
    let value_42 = ByteArray::inline([42], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.open_snapshot_write();

    let it_1 = snapshot_1.iterate_range(prefix.clone());
    let mut sum_1 = 0;
    for v in it_1.collect_cloned_vec(|_, v| ByteArray::<BUFFER_VALUE_INLINE>::from(v)).unwrap().iter() {
        sum_1 += v.bytes()[0] as i64;
    }
    assert!(sum_1 == 1);

    let it_2 = snapshot_2.iterate_range(prefix.clone());
    let mut sum_2 = 0;
    for v in it_2.collect_cloned_vec(|_, v| ByteArray::<BUFFER_VALUE_INLINE>::from(v)).unwrap().iter() {
        sum_2 += v.bytes()[0] as i64;
    }
    assert!(sum_2 == 1);

    snapshot_1.put_val(key_3.to_owned(), ByteArray::copy(value_31.bytes()));
    snapshot_2.put_val(key_4.to_owned(), ByteArray::copy(value_42.bytes()));
    let result_1 = snapshot_1.commit();
    let result_2 = snapshot_2.commit();

    // These two rw anti-dependency edges are enough for the transactions not be serialisable.
    // Both the assert sum_x == 1 cannot be true in any serialisation.
    fails_without_serializability!(result_1.is_err() || result_2.is_err());
}

#[test]
fn g2_antidependency_cycles_fekete() {
    // From "A Read-Only Transaction Anomaly Under Snapshot Isolation" (Fekete et al.)
    //  Without the read-only t3,  the history is: [ r_1(1), r_1(2), r_2(2), w_2(2, ?) ]
    //      There is only one rw edge: r_1(2) -> w_2(2,?)
    // The third transaction extends the history, [..., r_3(1), r_3(2), w_1(1, ?) ]
    // opened after t2 commits introduces :
    //  * a wr edge w_2(2,?) -> r_3(2)      (This is possible since t1 & t3 are not 'concurrent')
    //  * a rw edge r_3(1) -> w_1(1,?)
    // These form a cycle between t1, t2, t3.
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));
    let value_1_0 = ByteArray::inline([10], 1);
    let value_2_0 = ByteArray::inline([20], 1);
    let value_1_3 = ByteArray::inline([13], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_1_0.bytes()));
    snapshot_setup.put_val(key_2.to_owned(), ByteArray::copy(value_2_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_write();

    let read_1_1 = snapshot_1.get::<128>(StorageKeyReference::from(&key_1));
    let read_2_1 = snapshot_1.get::<128>(StorageKeyReference::from(&key_2));
    assert_eq!(value_1_0.bytes(), read_1_1.unwrap().unwrap().bytes());
    assert_eq!(value_2_0.bytes(), read_2_1.unwrap().unwrap().bytes());

    let read_2_2 = snapshot_2.get::<128>(StorageKeyReference::from(&key_2));
    let to_write_22 = ByteArray::inline([read_2_2.unwrap().unwrap().bytes()[0] + 5], 1);
    snapshot_2.put_val(key_2.to_owned(), ByteArray::copy(to_write_22.bytes()));
    let result_2 = snapshot_2.commit();
    assert!(result_2.is_ok());

    let snapshot_3 = storage.open_snapshot_write();

    let read_1_3 = snapshot_3.get::<128>(StorageKeyReference::from(&key_1));
    let read_2_3 = snapshot_3.get::<128>(StorageKeyReference::from(&key_2));
    assert_eq!(value_1_0.bytes(), read_1_3.unwrap().unwrap().bytes());
    assert_eq!(to_write_22.bytes(), read_2_3.unwrap().unwrap().bytes());

    let result_3 = snapshot_3.commit();
    assert!(result_3.is_ok());

    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_1_3.bytes()));
    let result_1 = snapshot_1.commit();
    fails_without_serializability!(result_1.is_err()); // Error if it's allowed to commit
}

#[test]
fn otv() {
    // This requires a rw-wr cycle.
    // In the example, t3 partially observes writes from t1 before they are overwritten by t2.
    // In our case, we can't see t3's writes, the wr edge is absent and the anomaly does not occur.

    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));
    let value_1_0 = ByteArray::inline([10], 1);
    let value_1_1 = ByteArray::inline([11], 1);
    let value_1_2 = ByteArray::inline([12], 1);
    let value_2_0 = ByteArray::inline([20], 1);
    let value_2_1 = ByteArray::inline([21], 1);
    let value_2_2 = ByteArray::inline([22], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_1_0.bytes()));
    snapshot_setup.put_val(key_2.to_owned(), ByteArray::copy(value_2_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());

    let snapshot_1 = storage.clone().open_snapshot_write();
    let snapshot_2 = storage.clone().open_snapshot_write();
    let snapshot_3 = storage.open_snapshot_read();

    snapshot_1.put_val(key_1.to_owned(), ByteArray::copy(value_1_1.bytes()));
    snapshot_2.put_val(key_1.to_owned(), ByteArray::copy(value_1_2.bytes()));
    snapshot_1.put_val(key_2.to_owned(), ByteArray::copy(value_2_1.bytes()));
    let read_1_3 = snapshot_3.get::<128>(StorageKeyReference::from(&key_1));
    let result_1 = snapshot_1.commit();
    snapshot_2.put_val(key_2.to_owned(), ByteArray::copy(value_2_2.bytes()));
    let read_2_3 = snapshot_3.get::<128>(StorageKeyReference::from(&key_2));
    let result_2 = snapshot_2.commit();
    assert!(result_1.is_ok() && result_2.is_ok());
    assert_eq!(value_1_0.bytes(), read_1_3.unwrap().unwrap().bytes());
    assert_eq!(value_2_0.bytes(), read_2_3.unwrap().unwrap().bytes());
}

fn imp_setup() -> Arc<MVCCStorage<WAL>> {
    init_logging();
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));
    let value_1_0 = ByteArray::inline([10], 1);
    let value_2_0 = ByteArray::inline([20], 1);
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);

    let snapshot_setup = storage.clone().open_snapshot_write();
    snapshot_setup.put_val(key_1.to_owned(), ByteArray::copy(value_1_0.bytes()));
    snapshot_setup.put_val(key_2.to_owned(), ByteArray::copy(value_2_0.bytes()));
    let result_snapshot = snapshot_setup.commit();
    assert!(result_snapshot.is_ok());
    storage
}

fn imp_ops<D>(snapshot_update: &WriteSnapshot<D>, snapshot_delete: &WriteSnapshot<D>)
where
    D: DurabilityService,
{
    let key_1 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));

    let read_1_1 = snapshot_update.get::<128>(StorageKeyReference::from(&key_1));
    let to_write_11 = ByteArray::inline([read_1_1.unwrap().unwrap().bytes()[0] + 10], 1);
    snapshot_update.put_val(key_1.to_owned(), ByteArray::copy(to_write_11.bytes()));

    let read_2_1 = snapshot_update.get::<128>(StorageKeyReference::from(&key_2));
    let to_write_21 = ByteArray::inline([read_2_1.unwrap().unwrap().bytes()[0] + 10], 1);
    snapshot_update.put_val(key_2.to_owned(), ByteArray::copy(to_write_21.bytes()));

    let read_1_2 = snapshot_delete.get::<128>(StorageKeyReference::from(&key_1));
    if read_1_2.unwrap().unwrap().bytes()[0] == 20 {
        snapshot_delete.delete(key_1.to_owned());
    }
    let read_2_2 = snapshot_delete.get::<128>(StorageKeyReference::from(&key_2));
    if read_2_2.unwrap().unwrap().bytes()[0] == 20 {
        snapshot_delete.delete(key_2.to_owned());
    }
}

fn imp_validate_serializable<D>(storage: Arc<MVCCStorage<D>>) -> bool
where
    D: DurabilityService,
{
    let key_1: StorageKeyArray<BUFFER_KEY_INLINE> = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_1));
    let key_2: StorageKeyArray<BUFFER_KEY_INLINE> = StorageKeyArray::new(Keyspace, ByteArray::copy(&KEY_2));
    let value_20 = ByteArray::inline([20], 1);
    let value_30 = ByteArray::inline([30], 1);

    let reader_after = storage.open_snapshot_read();
    let read_1_after = reader_after.get::<128>(StorageKeyReference::from(&key_1)).unwrap();
    let read_2_after = reader_after.get::<128>(StorageKeyReference::from(&key_2)).unwrap();

    let delete_went_first_1 = match read_1_after {
        Some(x) => {
            assert_eq!(value_20.bytes()[0], x.bytes()[0]);
            true
        }
        None => false,
    };
    let delete_went_first_2 = match read_2_after {
        Some(x) => {
            assert_eq!(value_30.bytes()[0], x.bytes()[0]);
            false
        }
        None => true,
    };
    delete_went_first_1 == delete_went_first_2
}

#[test]
fn imp_commit_delete_first() {
    // Initially, (k1, 10), (k2, 20)
    //  t_update performs "update v = v + 10 for all (k,v)"
    //  t_delete performs "delete (k,v) where v == 20"
    // By our implementation, committing the update first and delete second looks correct.
    // But committing the delete first and update second leaves both keys present.
    let storage = imp_setup();
    let snapshot_update = storage.clone().open_snapshot_write();
    let snapshot_delete = storage.clone().open_snapshot_write();
    imp_ops(&snapshot_update, &snapshot_delete);
    let result_delete = snapshot_delete.commit();
    let result_update = snapshot_update.commit();

    if !(result_update.is_ok() && result_delete.is_ok()) {
        panic!("The execution has changed. If we failed the second commit, this would be a success condition!")
    }
    fails_without_serializability!(imp_validate_serializable(storage));
}

#[test]
fn imp_commit_update_first() {
    let storage = imp_setup();
    let snapshot_update = storage.clone().open_snapshot_write();
    let snapshot_delete = storage.clone().open_snapshot_write();
    imp_ops(&snapshot_update, &snapshot_delete);
    let result_update = snapshot_update.commit();
    let result_delete = snapshot_delete.commit();

    if !(result_update.is_ok() && result_delete.is_ok()) {
        panic!("The execution has changed. If we failed the second commit, this would be a success condition!")
    }
    assert!(imp_validate_serializable(storage));
}

#[test]
fn isolation_manager_reads_evicted_from_disk() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = setup_storage(&storage_path);
    let key_1 = StorageKey::new_owned(Keyspace, ByteArray::copy(&KEY_1));
    let key_2 = StorageKey::new_owned(Keyspace, ByteArray::copy(&KEY_2));
    let value_1 = ByteArray::copy(&VALUE_1);

    let snapshot0 = storage.clone().open_snapshot_write();
    snapshot0.put_val(key_1.clone().into_owned_array(), value_1.clone());
    snapshot0.commit().unwrap();
    let watermark_after_0 = storage.read_watermark();

    let snapshot1 = storage.clone().open_snapshot_write();
    snapshot1.delete(key_1.clone().into_owned_array());
    snapshot1.commit().unwrap();

    for _i in 0..resource::constants::storage::TIMELINE_WINDOW_SIZE {
        let snapshot_i = storage.clone().open_snapshot_write();
        snapshot_i.put_val(key_2.clone().into_owned_array(), value_1.clone());
        snapshot_i.commit().unwrap();
    }

    {
        let snapshot_passes = storage.clone().open_snapshot_write_at(watermark_after_0).unwrap();
        snapshot_passes.put_val(key_2.clone().into_owned_array(), value_1.clone());
        let snapshot_passes_result = snapshot_passes.commit();

        assert!(snapshot_passes_result.is_ok());
    }
    {
        let snapshot_conflicts = storage.open_snapshot_write_at(watermark_after_0).unwrap();
        snapshot_conflicts.get_required(key_1.clone()).unwrap();
        snapshot_conflicts.put_val(key_2.clone().into_owned_array(), value_1.clone());
        let snapshot_conflicts_result = snapshot_conflicts.commit();

        assert!(
            matches!(
                snapshot_conflicts_result,
                Err(SnapshotError::Commit {
                    source: StorageCommitError::Isolation { conflict: IsolationConflict::RequireDeletedKey, .. },
                    ..
                })
            ),
            "{}",
            snapshot_conflicts_result.unwrap_err()
        );
    }
}

#[test]
fn isolation_manager_correctly_recovers_from_disk() {
    init_logging();
    let storage_path = create_tmp_dir();

    let key_1 = StorageKey::new_owned(Keyspace, ByteArray::copy(&KEY_1));
    let value_1 = ByteArray::copy(&VALUE_1);

    let watermark_after_one_commit = {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap());

        let snapshot = storage.clone().open_snapshot_write();
        snapshot.put_val(key_1.clone().into_owned_array(), value_1.clone());
        snapshot.commit().unwrap();
        storage.clone().read_watermark()
    };

    {
        // TODO: Find a way to make commits crash before they're committed
        let storage = MVCCStorage::<WAL>::open::<TestKeyspaceSet>("storage", &storage_path).unwrap();
        assert_eq!(watermark_after_one_commit, storage.read_watermark());
    };
}
