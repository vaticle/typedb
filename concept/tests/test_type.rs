/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::{borrow::Borrow, collections::HashMap, rc::Rc, sync::Arc};

use concept::type_::{
    annotation::AnnotationAbstract,
    entity_type::EntityTypeAnnotation,
    object_type::ObjectType,
    owns::Owns,
    relation_type::RelationTypeAnnotation,
    role_type::RoleTypeAnnotation,
    type_manager::{type_cache::TypeCache, TypeManager},
    Ordering, OwnerAPI, PlayerAPI, TypeAPI,
};
use durability::wal::WAL;
use encoding::{
    graph::{
        definition::{
            definition_key::DefinitionKey, definition_key_generator::DefinitionKeyGenerator, r#struct::StructDefinition,
        },
        type_::{vertex_generator::TypeVertexGenerator, Kind},
    },
    value::{label::Label, value_type::ValueType},
    EncodingKeyspace,
};
use storage::{
    durability_client::WALClient,
    snapshot::{CommittableSnapshot, ReadSnapshot, ReadableSnapshot, WritableSnapshot, WriteSnapshot},
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging};

/*
This test is used to help develop the API of Types.
We don't aim for complete coverage of all APIs, and will rely on the BDD scenarios for coverage.
 */

fn setup_storage() -> Arc<MVCCStorage<WALClient>> {
    init_logging();
    let storage_path = create_tmp_dir();
    let wal = WAL::create(&storage_path).unwrap();
    let storage = Arc::new(
        MVCCStorage::<WALClient>::create::<EncodingKeyspace>("storage", &storage_path, WALClient::new(wal)).unwrap(),
    );

    let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WALClient>>::initialise_types(
        storage.clone(),
        definition_key_generator.clone(),
        type_vertex_generator.clone(),
    )
    .unwrap();
    storage
}

fn type_manager<Snapshot: ReadableSnapshot>(
    storage: Arc<MVCCStorage<WALClient>>,
    cache_at_snapshot: Option<&Snapshot>,
) -> Arc<TypeManager<Snapshot>> {
    let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    let cache = cache_at_snapshot
        .map(|snapshot| Arc::new(TypeCache::new(storage.clone(), snapshot.open_sequence_number()).unwrap()));
    let type_manager =
        Arc::new(TypeManager::new(definition_key_generator.clone(), type_vertex_generator.clone(), cache));

    type_manager
}

#[test]
fn entity_usage() {
    let storage = setup_storage();

    let mut snapshot: WriteSnapshot<_> = storage.clone().open_snapshot_write();
    {
        // Without cache, uncommitted
        let type_manager = type_manager(storage.clone(), None);

        let root_entity = type_manager.get_entity_type(&snapshot, &Kind::Entity.root_label()).unwrap().unwrap();
        assert_eq!(*root_entity.get_label(&snapshot, &type_manager).unwrap(), Kind::Entity.root_label());
        assert!(root_entity.is_root(&snapshot, &type_manager).unwrap());

        // --- age sub attribute ---
        let age_label = Label::build("age");
        let age_type = type_manager.create_attribute_type(&mut snapshot, &age_label, false).unwrap();
        age_type.set_value_type(&mut snapshot, &type_manager, ValueType::Long).unwrap();

        assert!(!age_type.is_root(&snapshot, &type_manager).unwrap());
        assert!(age_type.get_annotations(&snapshot, &type_manager).unwrap().is_empty());
        assert_eq!(*age_type.get_label(&snapshot, &type_manager).unwrap(), age_label);
        assert_eq!(age_type.get_value_type(&snapshot, &type_manager).unwrap(), Some(ValueType::Long));

        // --- person sub entity @abstract ---
        let person_label = Label::build("person");
        let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();
        person_type
            .set_annotation(&mut snapshot, &type_manager, EntityTypeAnnotation::Abstract(AnnotationAbstract))
            .unwrap();

        assert!(!person_type.is_root(&snapshot, &type_manager).unwrap());
        assert!(person_type
            .get_annotations(&snapshot, &type_manager)
            .unwrap()
            .contains(&EntityTypeAnnotation::Abstract(AnnotationAbstract)));
        assert_eq!(*person_type.get_label(&snapshot, &type_manager).unwrap(), person_label);

        let supertype = person_type.get_supertype(&snapshot, &type_manager).unwrap().unwrap();
        assert_eq!(supertype, root_entity);

        // --- child sub person ---
        let child_label = Label::build("child");
        let child_type = type_manager.create_entity_type(&mut snapshot, &child_label, false).unwrap();
        child_type.set_supertype(&mut snapshot, &type_manager, person_type.clone()).unwrap();

        assert!(!child_type.is_root(&snapshot, &type_manager).unwrap());
        assert_eq!(*child_type.get_label(&snapshot, &type_manager).unwrap(), child_label);

        let supertype = child_type.get_supertype(&snapshot, &type_manager).unwrap().unwrap();
        assert_eq!(supertype, person_type);
        let supertypes = child_type.get_supertypes(&snapshot, &type_manager).unwrap();
        assert_eq!(supertypes.len(), 2);

        // --- child owns age ---
        child_type.set_owns(&mut snapshot, &type_manager, age_type.clone().into_owned(), Ordering::Unordered).unwrap();
        let owns =
            child_type.get_owns_attribute(&snapshot, &type_manager, age_type.clone().into_owned()).unwrap().unwrap();
        // TODO: test 'owns' structure directly

        let all_owns = child_type.get_owns(&snapshot, &type_manager).unwrap();
        assert_eq!(all_owns.len(), 1);
        assert!(all_owns.contains(&owns));
        assert_eq!(child_type.get_owns_attribute(&snapshot, &type_manager, age_type.clone()).unwrap(), Some(owns));
        assert!(child_type.has_owns_attribute(&snapshot, &type_manager, age_type.clone()).unwrap());

        // --- adult sub person ---
        let adult_type = type_manager.create_entity_type(&mut snapshot, &Label::build("adult"), false).unwrap();
        adult_type.set_supertype(&mut snapshot, &type_manager, person_type.clone()).unwrap();
        assert_eq!(root_entity.get_subtypes(&snapshot, &type_manager).unwrap().len(), 1);
        assert_eq!(root_entity.get_subtypes_transitive(&snapshot, &type_manager).unwrap().len(), 3);
        assert_eq!(person_type.get_subtypes(&snapshot, &type_manager).unwrap().len(), 2);
        assert_eq!(person_type.get_subtypes_transitive(&snapshot, &type_manager).unwrap().len(), 2);

        // --- owns inheritance ---
        let height_label = Label::new_static("height");
        let height_type = type_manager.create_attribute_type(&mut snapshot, &height_label, false).unwrap();
        person_type.set_owns(&mut snapshot, &type_manager, height_type.clone(), Ordering::Unordered).unwrap();

        match child_type.get_owns_attribute_transitive(&snapshot, &type_manager, height_type.clone()).unwrap() {
            None => panic!("child should inherit ownership of height"),
            Some(child_owns_height) => {
                assert_eq!(height_type, child_owns_height.attribute());
                assert_eq!(ObjectType::Entity(person_type.clone()), child_owns_height.owner());
            }
        }
    }
    snapshot.commit().unwrap();

    {
        // With cache, committed
        let snapshot: ReadSnapshot<_> = storage.clone().open_snapshot_read();
        let type_cache = Arc::new(TypeCache::new(storage.clone(), snapshot.open_sequence_number()).unwrap());
        let type_manager = type_manager(storage.clone(), Some(&snapshot));

        let root_entity = type_manager.get_entity_type(&snapshot, &Kind::Entity.root_label()).unwrap().unwrap();
        assert_eq!(*root_entity.get_label(&snapshot, &type_manager).unwrap(), Kind::Entity.root_label());
        assert!(root_entity.is_root(&snapshot, &type_manager).unwrap());

        // --- age sub attribute ---
        let age_label = Label::build("age");
        let age_type = type_manager.get_attribute_type(&snapshot, &age_label).unwrap().unwrap();

        assert!(!age_type.is_root(&snapshot, &type_manager).unwrap());
        assert!(age_type.get_annotations(&snapshot, &type_manager).unwrap().is_empty());
        assert_eq!(*age_type.get_label(&snapshot, &type_manager).unwrap(), age_label);
        assert_eq!(age_type.get_value_type(&snapshot, &type_manager).unwrap(), Some(ValueType::Long));

        // --- person sub entity ---
        let person_label = Label::build("person");
        let person_type = type_manager.get_entity_type(&snapshot, &person_label).unwrap().unwrap();
        assert!(!person_type.is_root(&snapshot, &type_manager).unwrap());
        assert!(person_type
            .get_annotations(&snapshot, &type_manager)
            .unwrap()
            .contains(&EntityTypeAnnotation::Abstract(AnnotationAbstract)));
        assert_eq!(*person_type.get_label(&snapshot, &type_manager).unwrap(), person_label);

        let supertype = person_type.get_supertype(&snapshot, &type_manager).unwrap().unwrap();
        assert_eq!(supertype, root_entity);

        // --- child sub person ---
        let child_label = Label::build("child");
        let child_type = type_manager.get_entity_type(&snapshot, &child_label).unwrap().unwrap();

        assert!(!child_type.is_root(&snapshot, &type_manager).unwrap());
        assert_eq!(*child_type.get_label(&snapshot, &type_manager).unwrap(), child_label);

        let supertype = child_type.get_supertype(&snapshot, &type_manager).unwrap().unwrap();
        assert_eq!(supertype, person_type);
        let supertypes = child_type.get_supertypes(&snapshot, &type_manager).unwrap();
        assert_eq!(supertypes.len(), 2);

        // --- child owns age ---
        let all_owns = child_type.get_owns(&snapshot, &type_manager).unwrap();
        assert_eq!(all_owns.len(), 1);
        let expected_owns = Owns::new(ObjectType::Entity(child_type.clone()), age_type.clone());
        assert!(all_owns.contains(&expected_owns));
        assert_eq!(
            child_type.get_owns_attribute(&snapshot, &type_manager, age_type.clone()).unwrap(),
            Some(expected_owns)
        );
        assert!(child_type.has_owns_attribute(&snapshot, &type_manager, age_type.clone()).unwrap());

        // --- adult sub person ---
        assert_eq!(root_entity.get_subtypes(&snapshot, &type_manager).unwrap().len(), 1);
        assert_eq!(root_entity.get_subtypes_transitive(&snapshot, &type_manager).unwrap().len(), 3);
        assert_eq!(person_type.get_subtypes(&snapshot, &type_manager).unwrap().len(), 2);
        assert_eq!(person_type.get_subtypes_transitive(&snapshot, &type_manager).unwrap().len(), 2);

        // --- owns inheritance ---
        let height_type = type_manager.get_attribute_type(&snapshot, &Label::new_static("height")).unwrap().unwrap();
        match child_type.get_owns_attribute_transitive(&snapshot, &type_manager, height_type.clone()).unwrap() {
            None => panic!("child should inherit ownership of height"),
            Some(child_owns_height) => {
                assert_eq!(height_type, child_owns_height.attribute());
                assert_eq!(ObjectType::Entity(person_type.clone()), child_owns_height.owner());
            }
        }
    }
}

#[test]
fn role_usage() {
    let storage = setup_storage();

    let friendship_label = Label::build("friendship");
    let friend_name = "friend";
    let person_label = Label::build("person");

    let mut snapshot: WriteSnapshot<_> = storage.clone().open_snapshot_write();
    {
        // Without cache, uncommitted
        let type_manager = type_manager(storage.clone(), None);
        let root_relation = type_manager.get_relation_type(&snapshot, &Kind::Relation.root_label()).unwrap().unwrap();
        assert_eq!(*root_relation.get_label(&snapshot, &type_manager).unwrap(), Kind::Relation.root_label());
        assert!(root_relation.is_root(&snapshot, &type_manager).unwrap());
        assert!(root_relation.get_supertype(&snapshot, &type_manager).unwrap().is_none());
        assert_eq!(root_relation.get_supertypes(&snapshot, &type_manager).unwrap().len(), 0);
        assert!(root_relation
            .get_annotations(&snapshot, &type_manager)
            .unwrap()
            .contains(&RelationTypeAnnotation::Abstract(AnnotationAbstract)));

        let root_role = type_manager.get_role_type(&snapshot, &Kind::Role.root_label()).unwrap().unwrap();
        assert_eq!(*root_role.get_label(&snapshot, &type_manager).unwrap(), Kind::Role.root_label());
        assert!(root_role.is_root(&snapshot, &type_manager).unwrap());
        assert!(root_role.get_supertype(&snapshot, &type_manager).unwrap().is_none());
        assert_eq!(root_role.get_supertypes(&snapshot, &type_manager).unwrap().len(), 0);
        assert!(root_role
            .get_annotations(&snapshot, &type_manager)
            .unwrap()
            .contains(&RoleTypeAnnotation::Abstract(AnnotationAbstract)));

        // --- friendship sub relation, relates friend ---
        let friendship_type = type_manager.create_relation_type(&mut snapshot, &friendship_label, false).unwrap();
        friendship_type.create_relates(&mut snapshot, &type_manager, friend_name, Ordering::Unordered).unwrap();
        let relates = friendship_type.get_relates_role(&snapshot, &type_manager, friend_name).unwrap().unwrap();
        let role_type =
            type_manager.resolve_relates(&snapshot, friendship_type.clone(), friend_name).unwrap().unwrap().role();
        debug_assert_eq!(relates.relation(), friendship_type.clone());
        debug_assert_eq!(relates.role(), role_type);

        // --- person plays friendship:friend ---
        let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();
        person_type.set_plays(&mut snapshot, &type_manager, role_type.clone().into_owned()).unwrap();
        let plays =
            person_type.get_plays_role(&snapshot, &type_manager, role_type.clone().into_owned()).unwrap().unwrap();
        debug_assert_eq!(plays.player(), ObjectType::Entity(person_type.clone()));
        debug_assert_eq!(plays.role(), role_type);
    }
    snapshot.commit().unwrap();

    {
        // With cache, committed
        let snapshot: ReadSnapshot<_> = storage.clone().open_snapshot_read();
        let type_cache = Arc::new(TypeCache::new(storage.clone(), snapshot.open_sequence_number()).unwrap());
        let type_manager = type_manager(storage.clone(), Some(&snapshot));

        // --- friendship sub relation, relates friend ---
        let friendship_type = type_manager.get_relation_type(&snapshot, &friendship_label).unwrap().unwrap();
        let relates = friendship_type.get_relates_role(&snapshot, &type_manager, friend_name).unwrap();
        debug_assert!(relates.is_some());
        let relates = relates.unwrap();
        let role_type =
            type_manager.resolve_relates(&snapshot, friendship_type.clone(), friend_name).unwrap().unwrap().role();
        debug_assert_eq!(relates.relation(), friendship_type.clone());
        debug_assert_eq!(relates.role(), role_type);

        // --- person plays friendship:friend ---
        let person_type = type_manager.get_entity_type(&snapshot, &person_label).unwrap().unwrap();
        let plays =
            person_type.get_plays_role(&snapshot, &type_manager, role_type.clone().into_owned()).unwrap().unwrap();
        debug_assert_eq!(plays.player(), ObjectType::Entity(person_type.clone()));
        debug_assert_eq!(plays.role(), role_type);
    }
}

#[test]
fn test_struct_definition() {
    let storage = setup_storage();

    // Without cache, uncommitted
    let mut snapshot = storage.clone().open_snapshot_write();
    let type_manager = type_manager(storage.clone(), None);

    let nested_struct_name = "nested_struct".to_owned();
    let nested_struct_fields =
        HashMap::from([("f0_bool".into(), (ValueType::Boolean, false)), ("f1_long".into(), (ValueType::Long, false))]);
    let nested_struct_key =
        define_struct(&mut snapshot, &type_manager, nested_struct_name.clone(), nested_struct_fields.clone());

    let outer_struct_name = "outer_struct".to_owned();
    let outer_struct_fields =
        HashMap::from([("f0_nested".into(), (ValueType::Struct(nested_struct_key.clone()), false))]);

    let outer_struct_key =
        define_struct(&mut snapshot, &type_manager, outer_struct_name.clone(), outer_struct_fields.clone());
    // Read buffered
    {
        assert_eq!(0, nested_struct_key.definition_id().as_uint());
        let read_nested_key =
            type_manager.get_struct_definition_key(&snapshot, &nested_struct_name.clone()).unwrap().unwrap();
        assert_eq!(nested_struct_key.definition_id().as_uint(), read_nested_key.definition_id().as_uint());
        let read_nested_definition = type_manager.get_struct_definition(&snapshot, read_nested_key).unwrap();
        assert_eq!(&nested_struct_name, &read_nested_definition.name);
        assert_eq!(&nested_struct_fields, &remap_struct_fields(read_nested_definition.borrow()));

        assert_eq!(1, outer_struct_key.definition_id().as_uint());
        let read_outer_key =
            type_manager.get_struct_definition_key(&snapshot, &outer_struct_name.clone()).unwrap().unwrap();
        assert_eq!(outer_struct_key.definition_id().as_uint(), read_outer_key.definition_id().as_uint());
        let read_outer_definition = type_manager.get_struct_definition(&snapshot, read_outer_key).unwrap();
        assert_eq!(&outer_struct_name, &read_outer_definition.name);
        assert_eq!(&outer_struct_fields, &remap_struct_fields(read_outer_definition.borrow()));
    }
    snapshot.commit().unwrap();

    // Persisted, without cache
    {
        let snapshot = storage.clone().open_snapshot_read();
        let type_manager = crate::type_manager(storage.clone(), None);

        assert_eq!(0, nested_struct_key.definition_id().as_uint());
        // Read back:
        let read_nested_key = type_manager.get_struct_definition_key(&snapshot, &nested_struct_name).unwrap().unwrap();
        assert_eq!(nested_struct_key.definition_id().as_uint(), read_nested_key.definition_id().as_uint());
        let read_nested_definition = type_manager.get_struct_definition(&snapshot, read_nested_key).unwrap();
        assert_eq!(&nested_struct_name, &read_nested_definition.name);
        assert_eq!(&nested_struct_fields, &remap_struct_fields(read_nested_definition.borrow()));

        let read_outer_key = type_manager.get_struct_definition_key(&snapshot, &outer_struct_name).unwrap().unwrap();
        assert_eq!(outer_struct_key.definition_id().as_uint(), read_outer_key.definition_id().as_uint());
        let read_outer_definition = type_manager.get_struct_definition(&snapshot, read_outer_key).unwrap();
        assert_eq!(&outer_struct_name, &read_outer_definition.name);
        assert_eq!(&outer_struct_fields, &remap_struct_fields(read_outer_definition.borrow()));

        snapshot.close_resources()
    }

    // Persisted, with cache
    {
        let snapshot = storage.clone().open_snapshot_read();
        let type_cache = Arc::new(TypeCache::new(storage.clone(), snapshot.open_sequence_number()).unwrap());
        let type_manager = crate::type_manager(storage.clone(), Some(&snapshot));

        assert_eq!(0, nested_struct_key.definition_id().as_uint());
        // Read back:
        let read_nested_key = type_manager.get_struct_definition_key(&snapshot, &nested_struct_name).unwrap().unwrap();
        assert_eq!(nested_struct_key.definition_id().as_uint(), read_nested_key.definition_id().as_uint());
        let read_nested_definition = type_manager.get_struct_definition(&snapshot, read_nested_key).unwrap();
        assert_eq!(&nested_struct_name, &read_nested_definition.name);
        assert_eq!(&nested_struct_fields, &remap_struct_fields(read_nested_definition.borrow()));

        let read_outer_key = type_manager.get_struct_definition_key(&snapshot, &outer_struct_name).unwrap().unwrap();
        assert_eq!(outer_struct_key.definition_id().as_uint(), read_outer_key.definition_id().as_uint());
        let read_outer_definition = type_manager.get_struct_definition(&snapshot, read_outer_key).unwrap();
        assert_eq!(&outer_struct_name, &read_outer_definition.name);
        assert_eq!(&outer_struct_fields, &remap_struct_fields(read_outer_definition.borrow()));

        snapshot.close_resources()
    }
}

fn remap_struct_fields(struct_definition: &StructDefinition) -> HashMap<String, (ValueType, bool)> {
    struct_definition
        .field_names
        .iter()
        .map(|(name, idx)| {
            let field_def = struct_definition.fields.get(&idx).unwrap();
            (name.to_owned(), (field_def.value_type.clone(), field_def.optional))
        })
        .collect()
}

fn define_struct<Snapshot: WritableSnapshot>(
    snapshot: &mut Snapshot,
    type_manager: &TypeManager<Snapshot>,
    name: String,
    definitions: HashMap<String, (ValueType, bool)>,
) -> DefinitionKey<'static> {
    let struct_key = type_manager.create_struct(snapshot, name).unwrap();
    for (name, (value_type, optional)) in definitions {
        type_manager.create_struct_field(snapshot, struct_key.clone(), name, value_type, optional).unwrap();
    }
    struct_key
}

#[test]
fn test_struct_definition_updates() {
    let storage = setup_storage();
    let type_manager = type_manager(storage.clone(), None);

    // types to add
    let f_long = ("f_long".to_owned(), (ValueType::Long, false));
    let f_string = ("f_string".to_owned(), (ValueType::String, false));

    let struct_name = "structs_can_be_modified".to_owned();

    let struct_key = {
        let mut snapshot = storage.clone().open_snapshot_write();
        let struct_key = type_manager.create_struct(&mut snapshot, struct_name.clone()).unwrap();

        let (field, (value_type, is_optional)) = f_long.clone();
        type_manager.create_struct_field(&mut snapshot, struct_key.clone(), field, value_type, is_optional).unwrap();
        assert_eq!(
            HashMap::from([f_long.clone()]),
            remap_struct_fields(&type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap())
        );

        snapshot.commit().unwrap();
        struct_key
    };

    {
        let mut snapshot = storage.clone().open_snapshot_write();
        let (field, (value_type, is_optional)) = f_string.clone();
        type_manager.create_struct_field(&mut snapshot, struct_key.clone(), field, value_type, is_optional).unwrap();
        assert_eq!(
            HashMap::from([f_long.clone(), f_string.clone()]),
            remap_struct_fields(&type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap())
        );

        type_manager.delete_struct_field(&mut snapshot, struct_key.clone(), f_long.clone().0.to_owned()).unwrap();
        assert_eq!(
            HashMap::from([f_string.clone()]),
            remap_struct_fields(&type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap())
        );

        snapshot.commit().unwrap();
    };

    {
        let mut snapshot = storage.clone().open_snapshot_write();
        assert_eq!(
            HashMap::from([f_string.clone()]),
            remap_struct_fields(&type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap())
        );
        snapshot.close_resources();
    }
}
