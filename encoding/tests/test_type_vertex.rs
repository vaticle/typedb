/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;

use durability::wal::WAL;
use encoding::{
    error::EncodingError,
    graph::{
        type_::{
            vertex::{build_vertex_entity_type, TypeID},
            vertex_generator::TypeVertexGenerator,
        },
        Typed,
    },
    AsBytes, EncodingKeyspace, Keyable,
};
use storage::{key_value::StorageKeyReference, MVCCStorage};
use test_utils::{create_tmp_dir, init_logging};

// TODO: Update all tests with higher level APIs
#[test]
fn entity_type_vertexes_are_reused() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    // If we don't commit, it doesn't move.
    {
        for _ in 0..5 {
            let snapshot = storage.clone().open_snapshot_write();
            let generator = TypeVertexGenerator::new();
            let vertex = generator.create_entity_type(&snapshot).unwrap();
            assert_eq!(0, vertex.type_id_().as_u16());
        }
    }

    // create a bunch of types, delete, and assert that the IDs are re-used
    let create_till = 32;
    {
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();
        for i in 0..=create_till {
            let vertex = generator.create_entity_type(&snapshot).unwrap();
            assert_eq!(i, vertex.type_id_().as_u16());
        }
        snapshot.commit().unwrap();
    }

    {
        let snapshot = storage.clone().open_snapshot_write();
        for i in 0..=create_till {
            if i % 2 == 0 {
                let vertex = build_vertex_entity_type(TypeID::build(i));
                snapshot.delete(StorageKeyReference::new(vertex.keyspace(), vertex.bytes()).into());
                // TODO: replace with type api call.
            }
        }
        snapshot.commit().unwrap();
    }

    {
        let generator = TypeVertexGenerator::new();
        let snapshot = storage.clone().open_snapshot_write();
        for i in 0..=create_till {
            if i % 2 == 0 {
                let vertex = generator.create_entity_type(&snapshot).unwrap();
                assert_eq!(i, vertex.type_id_().as_u16());
            }
        }
    }
}

#[test]
fn max_entity_type_vertexes() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    let create_till = u16::MAX;
    {
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();
        for i in 0..=create_till {
            let vertex = generator.create_entity_type(&snapshot).unwrap();
            assert_eq!(i, vertex.type_id_().as_u16());
        }
        snapshot.commit().unwrap();
    }

    {
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();

        let res = generator.create_entity_type(&snapshot); // Crashes
        assert!(matches!(res, Err(EncodingError::TypeIDsExhausted { kind: encoding::graph::type_::Kind::Entity })));
    }
}

#[test]
fn loading_storage_assigns_next_vertex() {
    init_logging();
    let storage_path = create_tmp_dir();
    let create_till = 5;

    for i in 0..create_till {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();

        let vertex = generator.create_entity_type(&snapshot).unwrap();
        assert_eq!(i, vertex.type_id_().as_u16());
        snapshot.commit().unwrap();
    }

    for i in 0..create_till {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();

        let vertex = generator.create_attribute_type(&snapshot).unwrap();
        assert_eq!(i, vertex.type_id_().as_u16());
        snapshot.commit().unwrap();
    }

    for i in 0..create_till {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();

        let vertex = generator.create_relation_type(&snapshot).unwrap();
        assert_eq!(i, vertex.type_id_().as_u16());
        snapshot.commit().unwrap();
    }

    for i in 0..create_till {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();

        let vertex = generator.create_role_type(&snapshot).unwrap();
        assert_eq!(i, vertex.type_id_().as_u16());
        snapshot.commit().unwrap();
    }
}
