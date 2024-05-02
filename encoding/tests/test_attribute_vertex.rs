/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::{rc::Rc, sync::Arc};

use durability::wal::WAL;
use encoding::{
    graph::{
        thing::{vertex_attribute::StringAttributeID, vertex_generator::ThingVertexGenerator},
        type_::{vertex::TypeID, vertex_generator::TypeVertexGenerator},
        Typed,
    },
    value::string_bytes::StringBytes,
    AsBytes, EncodingKeyspace,
};
use resource::constants::snapshot::BUFFER_KEY_INLINE;
use storage::MVCCStorage;
use test_utils::{create_tmp_dir, init_logging};

#[test]
fn generate_string_attribute_vertex() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>(Rc::from("storage"), &storage_path).unwrap());

    let snapshot = storage.clone().open_snapshot_write();
    let type_id = TypeID::build(0);

    let thing_vertex_generator = ThingVertexGenerator::new();

    // 1: vertex for short string that is stored inline
    {
        let short_string = "Hello";
        let short_string_bytes: StringBytes<'_, BUFFER_KEY_INLINE> = StringBytes::build_ref(short_string);
        let vertex = thing_vertex_generator
            .create_attribute_string(type_id, short_string_bytes.as_reference(), &snapshot)
            .unwrap();
        let vertex_id = vertex.attribute_id().unwrap_string();
        assert!(vertex_id.is_inline());
        assert_eq!(vertex_id.get_inline_length() as usize, short_string_bytes.length());
        assert_eq!(vertex_id.get_inline_string_bytes().bytes(), short_string_bytes.bytes());
    }

    // 2: vertex for long string that does not exist beforehand with default hasher
    {
        let string = "Hello world, this is a long attribute string to be encoded.";
        let string_bytes: StringBytes<'_, BUFFER_KEY_INLINE> = StringBytes::build_ref(string);
        let vertex =
            thing_vertex_generator.create_attribute_string(type_id, string_bytes.as_reference(), &snapshot).unwrap();
        let vertex_id = vertex.attribute_id().unwrap_string();
        assert!(!vertex_id.is_inline());
        assert_eq!(
            vertex_id.get_hash_prefix(),
            string_bytes.bytes().bytes()[StringAttributeID::ENCODING_STRING_PREFIX_RANGE]
        );
        assert_eq!(
            vertex_id.get_hash_hash(),
            seahash::hash(string_bytes.bytes().bytes()).to_be_bytes()
                [0..StringAttributeID::ENCODING_STRING_HASH_LENGTH]
        );
        assert_eq!(vertex_id.get_hash_disambiguator(), 0u8);
    }

    // 3. use a constant hasher to force collisions
    const CONSTANT_HASH: u64 = 0;
    let thing_vertex_generator = ThingVertexGenerator::new_with_hasher(|_bytes| CONSTANT_HASH);

    {
        let string = "Hello world, this is a long attribute string to be encoded with a constant hash.";
        let string_bytes: StringBytes<'_, BUFFER_KEY_INLINE> = StringBytes::build_ref(string);
        let vertex =
            thing_vertex_generator.create_attribute_string(type_id, string_bytes.as_reference(), &snapshot).unwrap();

        let vertex_id = vertex.attribute_id().unwrap_string();
        assert!(!vertex_id.is_inline());
        assert_eq!(
            vertex_id.get_hash_prefix(),
            string_bytes.bytes().bytes()[StringAttributeID::ENCODING_STRING_PREFIX_RANGE]
        );
        assert_eq!(
            vertex_id.get_hash_hash(),
            CONSTANT_HASH.to_be_bytes()[0..StringAttributeID::ENCODING_STRING_HASH_LENGTH]
        );
        assert_eq!(vertex_id.get_hash_disambiguator(), 0u8);

        let string_collide = "Hello world, this is using the same prefix and will collide.";
        let string_collide_bytes: StringBytes<'_, BUFFER_KEY_INLINE> = StringBytes::build_ref(string_collide);
        let collide_vertex = thing_vertex_generator
            .create_attribute_string(type_id, string_collide_bytes.as_reference(), &snapshot)
            .unwrap();

        let collide_id = collide_vertex.attribute_id().unwrap_string();
        assert!(!collide_id.is_inline());
        assert_eq!(
            collide_id.get_hash_prefix(),
            string_collide_bytes.bytes().bytes()[StringAttributeID::ENCODING_STRING_PREFIX_RANGE]
        );
        assert_eq!(
            collide_id.get_hash_hash(),
            CONSTANT_HASH.to_be_bytes()[0..StringAttributeID::ENCODING_STRING_HASH_LENGTH]
        );
        assert_eq!(collide_id.get_hash_disambiguator(), 1u8);
    }
}

#[test]
fn next_entity_and_relation_ids_are_determined_from_storage() {
    init_logging();
    let storage_path = create_tmp_dir();
    let type_id = TypeID::build(0);
    {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        let generator = TypeVertexGenerator::new();

        let entity_type_vertex = generator.create_entity_type(&snapshot).unwrap();
        debug_assert_eq!(type_id, entity_type_vertex.type_id_());

        let relation_type_vertex = generator.create_relation_type(&snapshot).unwrap();
        debug_assert_eq!(type_id, relation_type_vertex.type_id_());

        snapshot.commit().unwrap();
    }

    for i in 0..5 {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        let generator = ThingVertexGenerator::load(storage.clone()).unwrap();
        let vertex = generator.create_entity(type_id, &snapshot);
        assert_eq!(type_id, vertex.type_id_());
        assert_eq!(i as u64, vertex.object_id().as_u64());
        snapshot.commit().unwrap();
    }

    for i in 0..5 {
        let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
        let snapshot = storage.clone().open_snapshot_write();
        let generator = ThingVertexGenerator::load(storage.clone()).unwrap();
        let vertex = generator.create_relation(type_id, &snapshot);
        assert_eq!(type_id, vertex.type_id_());
        assert_eq!(i as u64, vertex.object_id().as_u64());
        snapshot.commit().unwrap();
    }
}
