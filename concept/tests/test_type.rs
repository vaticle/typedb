/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::{rc::Rc, sync::Arc};

use concept::type_::{
    annotation::AnnotationAbstract, entity_type::EntityTypeAnnotation, object_type::ObjectType, owns::Owns,
    relation_type::RelationTypeAnnotation, role_type::RoleTypeAnnotation, type_cache::TypeCache,
    type_manager::TypeManager, Ordering, OwnerAPI, PlayerAPI,
};
use durability::wal::WAL;
use encoding::{
    graph::type_::{vertex_generator::TypeVertexGenerator, Kind},
    value::{label::Label, value_type::ValueType},
    EncodingKeyspace,
};
use storage::{
    snapshot::{ReadSnapshot, ReadableSnapshot, WriteSnapshot},
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging};

/*
This test is used to help develop the API of Types.
We don't aim for complete coverage of all APIs, and will rely on the BDD scenarios for coverage.
 */

#[test]
fn entity_usage() {
    init_logging();
    let storage_path = create_tmp_dir();
    let mut storage =
        Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>(Rc::from("storage"), &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();

    let snapshot: Arc<WriteSnapshot<_>> = Arc::new(storage.clone().open_snapshot_write());
    {
        // Without cache, uncommitted
        let type_manager = TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None);

        let root_entity = type_manager.get_entity_type(&Kind::Entity.root_label()).unwrap().unwrap();
        assert_eq!(*root_entity.get_label(&type_manager).unwrap(), Kind::Entity.root_label());
        assert!(root_entity.is_root(&type_manager).unwrap());

        // --- age sub attribute ---
        let age_label = Label::build("age");
        let age_type = type_manager.create_attribute_type(&age_label, false).unwrap();
        age_type.set_value_type(&type_manager, ValueType::Long);

        assert!(!age_type.is_root(&type_manager).unwrap());
        assert!(age_type.get_annotations(&type_manager).unwrap().is_empty());
        assert_eq!(*age_type.get_label(&type_manager).unwrap(), age_label);
        assert_eq!(age_type.get_value_type(&type_manager).unwrap(), Some(ValueType::Long));

        // --- person sub entity @abstract ---
        let person_label = Label::build("person");
        let person_type = type_manager.create_entity_type(&person_label, false).unwrap();
        person_type.set_annotation(&type_manager, EntityTypeAnnotation::Abstract(AnnotationAbstract::new())).unwrap();

        assert!(!person_type.is_root(&type_manager).unwrap());
        assert!(person_type
            .get_annotations(&type_manager)
            .unwrap()
            .contains(&EntityTypeAnnotation::Abstract(AnnotationAbstract::new())));
        assert_eq!(*person_type.get_label(&type_manager).unwrap(), person_label);

        let supertype = person_type.get_supertype(&type_manager).unwrap().unwrap();
        assert_eq!(supertype, root_entity);

        // --- child sub person ---
        let child_label = Label::build("child");
        let child_type = type_manager.create_entity_type(&child_label, false).unwrap();
        child_type.set_supertype(&type_manager, person_type.clone()).unwrap();

        assert!(!child_type.is_root(&type_manager).unwrap());
        assert_eq!(*child_type.get_label(&type_manager).unwrap(), child_label);

        let supertype = child_type.get_supertype(&type_manager).unwrap().unwrap();
        assert_eq!(supertype, person_type);
        let supertypes = child_type.get_supertypes(&type_manager).unwrap();
        assert_eq!(supertypes.len(), 2);

        // --- child owns age ---
        child_type.set_owns(&type_manager, age_type.clone().into_owned(), Ordering::Unordered);
        let owns = child_type.get_owns_attribute(&type_manager, age_type.clone().into_owned()).unwrap().unwrap();
        // TODO: test 'owns' structure directly

        let all_owns = child_type.get_owns(&type_manager).unwrap();
        assert_eq!(all_owns.len(), 1);
        assert!(all_owns.contains(&owns));
        assert_eq!(child_type.get_owns_attribute(&type_manager, age_type.clone()).unwrap(), Some(owns));
        assert!(child_type.has_owns_attribute(&type_manager, age_type.clone()).unwrap());

        // --- adult sub person ---
        let adult = type_manager.create_entity_type(&Label::build("adult"), false).unwrap();
        adult.set_supertype(&type_manager, person_type.clone()).unwrap();
        assert_eq!(root_entity.get_subtypes(&type_manager).unwrap().len(), 1);
        assert_eq!(root_entity.get_subtypes_transitive(&type_manager).unwrap().len(), 3);
        assert_eq!(person_type.get_subtypes(&type_manager).unwrap().len(), 2);
        assert_eq!(person_type.get_subtypes_transitive(&type_manager).unwrap().len(), 2);
    }
    if let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap() {
        write_snapshot.commit().unwrap();
    }

    {
        // With cache, committed
        let snapshot: Arc<ReadSnapshot<_>> = Arc::new(storage.clone().open_snapshot_read());
        let type_cache = Arc::new(TypeCache::new(storage.clone(), snapshot.open_sequence_number()).unwrap());
        let type_manager = TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), Some(type_cache));

        let root_entity = type_manager.get_entity_type(&Kind::Entity.root_label()).unwrap().unwrap();
        assert_eq!(*root_entity.get_label(&type_manager).unwrap(), Kind::Entity.root_label());
        assert!(root_entity.is_root(&type_manager).unwrap());

        // --- age sub attribute ---
        let age_label = Label::build("age");
        let age_type = type_manager.get_attribute_type(&age_label).unwrap().unwrap();

        assert!(!age_type.is_root(&type_manager).unwrap());
        assert!(age_type.get_annotations(&type_manager).unwrap().is_empty());
        assert_eq!(*age_type.get_label(&type_manager).unwrap(), age_label);
        assert_eq!(age_type.get_value_type(&type_manager).unwrap(), Some(ValueType::Long));

        // --- person sub entity ---
        let person_label = Label::build("person");
        let person_type = type_manager.get_entity_type(&person_label).unwrap().unwrap();
        assert!(!person_type.is_root(&type_manager).unwrap());
        assert!(person_type
            .get_annotations(&type_manager)
            .unwrap()
            .contains(&EntityTypeAnnotation::Abstract(AnnotationAbstract::new())));
        assert_eq!(*person_type.get_label(&type_manager).unwrap(), person_label);

        let supertype = person_type.get_supertype(&type_manager).unwrap().unwrap();
        assert_eq!(supertype, root_entity);

        // --- child sub person ---
        let child_label = Label::build("child");
        let child_type = type_manager.get_entity_type(&child_label).unwrap().unwrap();

        assert!(!child_type.is_root(&type_manager).unwrap());
        assert_eq!(*child_type.get_label(&type_manager).unwrap(), child_label);

        let supertype = child_type.get_supertype(&type_manager).unwrap().unwrap();
        assert_eq!(supertype, person_type);
        let supertypes = child_type.get_supertypes(&type_manager).unwrap();
        assert_eq!(supertypes.len(), 2);

        // --- child owns age ---
        let all_owns = child_type.get_owns(&type_manager).unwrap();
        assert_eq!(all_owns.len(), 1);
        let expected_owns = Owns::new(ObjectType::Entity(child_type.clone()), age_type.clone());
        assert!(all_owns.contains(&expected_owns));
        assert_eq!(child_type.get_owns_attribute(&type_manager, age_type.clone()).unwrap(), Some(expected_owns));
        assert!(child_type.has_owns_attribute(&type_manager, age_type.clone()).unwrap());

        // --- adult sub person ---
        assert_eq!(root_entity.get_subtypes(&type_manager).unwrap().len(), 1);
        assert_eq!(root_entity.get_subtypes_transitive(&type_manager).unwrap().len(), 3);
        assert_eq!(person_type.get_subtypes(&type_manager).unwrap().len(), 2);
        assert_eq!(person_type.get_subtypes_transitive(&type_manager).unwrap().len(), 2);
    }
}

#[test]
fn role_usage() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>(Rc::from("storage"), &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();

    let friendship_label = Label::build("friendship");
    let friend_name = "friend";
    let person_label = Label::build("person");

    let snapshot: Arc<WriteSnapshot<_>> = Arc::new(storage.clone().open_snapshot_write());
    {
        // Without cache, uncommitted
        let type_manager = TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None);
        let root_relation = type_manager.get_relation_type(&Kind::Relation.root_label()).unwrap().unwrap();
        assert_eq!(*root_relation.get_label(&type_manager).unwrap(), Kind::Relation.root_label());
        assert!(root_relation.is_root(&type_manager).unwrap());
        assert!(root_relation.get_supertype(&type_manager).unwrap().is_none());
        assert_eq!(root_relation.get_supertypes(&type_manager).unwrap().len(), 0);
        assert!(root_relation
            .get_annotations(&type_manager)
            .unwrap()
            .contains(&RelationTypeAnnotation::Abstract(AnnotationAbstract::new())));

        let root_role = type_manager.get_role_type(&Kind::Role.root_label()).unwrap().unwrap();
        assert_eq!(*root_role.get_label(&type_manager).unwrap(), Kind::Role.root_label());
        assert!(root_role.is_root(&type_manager).unwrap());
        assert!(root_role.get_supertype(&type_manager).unwrap().is_none());
        assert_eq!(root_role.get_supertypes(&type_manager).unwrap().len(), 0);
        assert!(root_role
            .get_annotations(&type_manager)
            .unwrap()
            .contains(&RoleTypeAnnotation::Abstract(AnnotationAbstract::new())));

        // --- friendship sub relation, relates friend ---
        let friendship_type = type_manager.create_relation_type(&friendship_label, false).unwrap();
        friendship_type.create_relates(&type_manager, friend_name, Ordering::Unordered).unwrap();
        let relates = friendship_type.get_relates_role(&type_manager, friend_name).unwrap().unwrap();
        let role_type = friendship_type.get_role(&type_manager, friend_name).unwrap().unwrap();
        debug_assert_eq!(relates.relation(), friendship_type);
        debug_assert_eq!(relates.role(), role_type);

        // --- person plays friendship:friend ---
        let person_type = type_manager.create_entity_type(&person_label, false).unwrap();
        person_type.set_plays(&type_manager, role_type.clone().into_owned());
        let plays = person_type.get_plays_role(&type_manager, role_type.clone().into_owned()).unwrap().unwrap();
        debug_assert_eq!(plays.player(), ObjectType::Entity(person_type.clone()));
        debug_assert_eq!(plays.role(), role_type);
    }
    if let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap() {
        write_snapshot.commit().unwrap();
    }

    {
        // With cache, committed
        let snapshot: Arc<ReadSnapshot<_>> = Arc::new(storage.clone().open_snapshot_read());
        let type_cache = Arc::new(TypeCache::new(storage.clone(), snapshot.open_sequence_number()).unwrap());
        let type_manager = TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), Some(type_cache));

        // --- friendship sub relation, relates friend ---
        let friendship_type = type_manager.get_relation_type(&friendship_label).unwrap().unwrap();
        let relates = friendship_type.get_relates_role(&type_manager, friend_name).unwrap();
        debug_assert!(relates.is_some());
        let relates = relates.unwrap();
        let role_type = friendship_type.get_role(&type_manager, friend_name).unwrap().unwrap();
        debug_assert_eq!(relates.relation(), friendship_type);
        debug_assert_eq!(relates.role(), role_type);

        // --- person plays friendship:friend ---
        let person_type = type_manager.get_entity_type(&person_label).unwrap().unwrap();
        let plays = person_type.get_plays_role(&type_manager, role_type.clone().into_owned()).unwrap().unwrap();
        debug_assert_eq!(plays.player(), ObjectType::Entity(person_type.clone()));
        debug_assert_eq!(plays.role(), role_type);
    }
}
