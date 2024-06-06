/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::sync::Arc;

use concept::{
    thing::{statistics::Statistics, thing_manager::ThingManager, ThingAPI},
    type_::type_manager::TypeManager,
};
use durability::wal::WAL;
use encoding::{
    graph::{thing::vertex_generator::ThingVertexGenerator, type_::vertex_generator::TypeVertexGenerator},
    value::label::Label,
    EncodingKeyspace,
};
use storage::{
    durability_client::WALClient,
    sequence_number::SequenceNumber,
    snapshot::{CommittableSnapshot, WriteSnapshot},
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging, TempDir};

macro_rules! assert_statistics_eq {
    ($lhs:expr, $rhs:expr) => {
        let Statistics {
            sequence_number: lhs_sequence_number,
            total_thing_count: lhs_total_thing_count,
            total_entity_count: lhs_total_entity_count,
            total_relation_count: lhs_total_relation_count,
            total_attribute_count: lhs_total_attribute_count,
            total_role_count: lhs_total_role_count,
            total_has_count: lhs_total_has_count,
            entity_counts: lhs_entity_counts,
            relation_counts: lhs_relation_counts,
            attribute_counts: lhs_attribute_counts,
            role_counts: lhs_role_counts,
            has_attribute_counts: lhs_has_attribute_counts,
            attribute_owner_counts: lhs_attribute_owner_counts,
            role_player_counts: lhs_role_player_counts,
            relation_role_counts: lhs_relation_role_counts,
            player_index_counts: lhs_player_index_counts,
            ..
        } = $lhs;
        let Statistics {
            sequence_number: rhs_sequence_number,
            total_thing_count: rhs_total_thing_count,
            total_entity_count: rhs_total_entity_count,
            total_relation_count: rhs_total_relation_count,
            total_attribute_count: rhs_total_attribute_count,
            total_role_count: rhs_total_role_count,
            total_has_count: rhs_total_has_count,
            entity_counts: rhs_entity_counts,
            relation_counts: rhs_relation_counts,
            attribute_counts: rhs_attribute_counts,
            role_counts: rhs_role_counts,
            has_attribute_counts: rhs_has_attribute_counts,
            attribute_owner_counts: rhs_attribute_owner_counts,
            role_player_counts: rhs_role_player_counts,
            relation_role_counts: rhs_relation_role_counts,
            player_index_counts: rhs_player_index_counts,
            ..
        } = $rhs;
        assert_eq!(
            (
                lhs_sequence_number,
                (lhs_total_thing_count, lhs_total_entity_count, lhs_total_relation_count, lhs_total_attribute_count),
                (lhs_total_role_count, lhs_total_has_count),
                (lhs_entity_counts, lhs_relation_counts, lhs_attribute_counts, lhs_role_counts),
                (lhs_has_attribute_counts, lhs_attribute_owner_counts),
                (lhs_role_player_counts, lhs_relation_role_counts, lhs_player_index_counts),
            ),
            (
                rhs_sequence_number,
                (rhs_total_thing_count, rhs_total_entity_count, rhs_total_relation_count, rhs_total_attribute_count),
                (rhs_total_role_count, rhs_total_has_count),
                (rhs_entity_counts, rhs_relation_counts, rhs_attribute_counts, rhs_role_counts),
                (rhs_has_attribute_counts, rhs_attribute_owner_counts),
                (rhs_role_player_counts, rhs_relation_role_counts, rhs_player_index_counts),
            )
        );
    };
}

fn setup() -> (Arc<MVCCStorage<WALClient>>, Arc<TypeVertexGenerator>, TempDir) {
    init_logging();
    let storage_path = create_tmp_dir(); // NOTE: dir is deleted when TempDir goes out of scope
    let wal = WAL::create(&storage_path).unwrap();
    let storage =
        Arc::new(MVCCStorage::create::<EncodingKeyspace>("storage", &storage_path, WALClient::new(wal)).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WALClient>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();
    (storage, type_vertex_generator, storage_path)
}

#[test]
fn create_entity() {
    let (storage, type_vertex_generator, _guard) = setup();

    let person_label = Label::build("person");

    let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
    let type_manager = Arc::new(TypeManager::new(type_vertex_generator.clone(), None));

    let mut snapshot = storage.clone().open_snapshot_write();
    let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());
    let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();
    thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
    thing_manager.finalise(&mut snapshot).unwrap();
    let commit_sequence_number = snapshot.commit().unwrap().unwrap();

    let mut manually_tracked = Statistics::new(commit_sequence_number);
    manually_tracked.total_thing_count += 1;
    manually_tracked.total_entity_count += 1;
    *manually_tracked.entity_counts.entry(person_type).or_default() += 1;

    let synchronised = Statistics::new(SequenceNumber::MIN).may_synchronise(storage).unwrap();

    assert_statistics_eq!(synchronised, manually_tracked);
}

#[test]
fn create_then_delete_twice_concurrently() {
    let (storage, type_vertex_generator, _guard) = setup();

    let person_label = Label::build("person");

    let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
    let type_manager = Arc::new(TypeManager::new(type_vertex_generator.clone(), None));

    let mut snapshot = storage.clone().open_snapshot_write();
    let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());
    let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();
    let person = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
    thing_manager.finalise(&mut snapshot).unwrap();
    let create_commit_seq = snapshot.commit().unwrap().unwrap();

    let mut snapshot = storage.clone().open_snapshot_write_at(create_commit_seq).unwrap();
    let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());
    person.clone().delete(&mut snapshot, &thing_manager).unwrap();
    thing_manager.finalise(&mut snapshot).unwrap();
    snapshot.commit().unwrap().unwrap();

    let mut snapshot = storage.clone().open_snapshot_write_at(create_commit_seq).unwrap();
    let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());
    person.clone().delete(&mut snapshot, &thing_manager).unwrap();
    thing_manager.finalise(&mut snapshot).unwrap();
    let commit_sequence_number = snapshot.commit().unwrap().unwrap();

    let mut manually_tracked = Statistics::new(commit_sequence_number);
    manually_tracked.entity_counts.insert(person_type, 0);

    let synchronised = Statistics::new(SequenceNumber::MIN).may_synchronise(storage).unwrap();

    assert_statistics_eq!(synchronised, manually_tracked);
}
