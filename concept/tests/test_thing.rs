/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::{borrow::Cow, sync::Arc};

use concept::{
    thing::{object::Object, thing_manager::ThingManager, value::Value},
    type_::{
        annotation::{AnnotationCardinality, AnnotationDistinct, AnnotationIndependent},
        attribute_type::AttributeTypeAnnotation,
        owns::OwnsAnnotation,
        role_type::RoleTypeAnnotation,
        type_manager::TypeManager,
        Ordering, OwnerAPI, PlayerAPI,
    },
};
use durability::wal::WAL;
use encoding::{
    graph::{thing::vertex_generator::ThingVertexGenerator, type_::vertex_generator::TypeVertexGenerator},
    value::{label::Label, value_type::ValueType},
    EncodingKeyspace,
};
use storage::{
    snapshot::{ReadSnapshot, WriteSnapshot},
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging};

#[test]
fn thing_create_iterate() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();
    let snapshot: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());
    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));

        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());
        let person_label = Label::build("person");
        let person_type = type_manager.create_entity_type(&person_label, false).unwrap();

        let _person_1 = thing_manager.create_entity(person_type.clone()).unwrap();
        let _person_2 = thing_manager.create_entity(person_type.clone()).unwrap();
        let _person_3 = thing_manager.create_entity(person_type.clone()).unwrap();
        let _person_4 = thing_manager.create_entity(person_type.clone()).unwrap();

        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }

    let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();

    {
        let snapshot: Arc<ReadSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_read());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager);
        let entities = thing_manager.get_entities().collect_cloned();
        assert_eq!(entities.len(), 4);
    }
}

#[test]
fn attribute_create() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();

    let age_label = Label::build("age");
    let name_label = Label::build("name");

    let age_value: i64 = 10;
    let name_value: &str = "TypeDB Fan";

    let snapshot: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());
    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());

        let age_type = type_manager.create_attribute_type(&age_label, false).unwrap();
        age_type.set_value_type(&type_manager, ValueType::Long);
        age_type
            .set_annotation(&type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent::new()))
            .unwrap();
        let name_type = type_manager.create_attribute_type(&name_label, false).unwrap();
        name_type.set_value_type(&type_manager, ValueType::String);
        name_type
            .set_annotation(&type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent::new()))
            .unwrap();

        let mut age_1 = thing_manager.create_attribute(age_type.clone(), Value::Long(age_value)).unwrap();
        assert_eq!(age_1.get_value(&thing_manager).unwrap(), Value::Long(age_value));

        let mut name_1 =
            thing_manager.create_attribute(name_type.clone(), Value::String(Cow::Borrowed(name_value))).unwrap();
        assert_eq!(name_1.get_value(&thing_manager).unwrap(), Value::String(Cow::Borrowed(name_value)));

        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }
    let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();

    {
        let snapshot: Arc<ReadSnapshot<WAL>> = Arc::new(storage.open_snapshot_read());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());
        let attributes = thing_manager.get_attributes().collect_cloned();
        assert_eq!(attributes.len(), 2);

        let age_type = type_manager.get_attribute_type(&age_label).unwrap().unwrap();
        let mut ages = thing_manager.get_attributes_in(age_type).unwrap().collect_cloned();
        assert_eq!(ages.len(), 1);
        assert_eq!(ages.first_mut().unwrap().get_value(&thing_manager).unwrap(), Value::Long(age_value));
    }
}

#[test]
fn has() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();

    let age_label = Label::build("age");
    let name_label = Label::build("name");
    let person_label = Label::build("person");

    let age_value: i64 = 10;
    let name_value: &str = "TypeDB Fan";

    let snapshot: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());
    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());

        let age_type = type_manager.create_attribute_type(&age_label, false).unwrap();
        age_type.set_value_type(&type_manager, ValueType::Long);
        let name_type = type_manager.create_attribute_type(&name_label, false).unwrap();
        name_type.set_value_type(&type_manager, ValueType::String);

        let person_type = type_manager.create_entity_type(&person_label, false).unwrap();
        person_type.set_owns(&type_manager, age_type.clone(), Ordering::Unordered);
        person_type.set_owns(&type_manager, name_type.clone(), Ordering::Unordered);

        let person_1 = thing_manager.create_entity(person_type.clone()).unwrap();
        let age_1 = thing_manager.create_attribute(age_type.clone(), Value::Long(age_value)).unwrap();
        let name_1 = thing_manager
            .create_attribute(name_type.clone(), Value::String(Cow::Owned(String::from(name_value))))
            .unwrap();

        person_1.set_has_unordered(&thing_manager, age_1).unwrap();
        person_1.set_has_unordered(&thing_manager, name_1).unwrap();

        let retrieved_attributes_count = person_1.get_has(&thing_manager).count();
        assert_eq!(retrieved_attributes_count, 2);

        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }

    let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();

    {
        let snapshot: Arc<ReadSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_read());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());
        let attributes = thing_manager.get_attributes().collect_cloned();
        assert_eq!(attributes.len(), 2);

        let people = thing_manager.get_entities().collect_cloned();
        let person_1 = people.first().unwrap();
        let retrieved_attributes_count = person_1.get_has(&thing_manager).count();
        assert_eq!(retrieved_attributes_count, 2);
    }
}

#[test]
fn attribute_cleanup_on_concurrent_detach() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();

    let age_label = Label::build("age");
    let name_label = Label::build("name");
    let person_label = Label::build("person");

    let age_value: i64 = 10;
    let name_alice_value: &str = "Alice";
    let name_bob_value: &str = "Bob";

    let snapshot: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());
    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());

        let age_type = type_manager.create_attribute_type(&age_label, false).unwrap();
        age_type.set_value_type(&type_manager, ValueType::Long);
        let name_type = type_manager.create_attribute_type(&name_label, false).unwrap();
        name_type.set_value_type(&type_manager, ValueType::String);

        let person_type = type_manager.create_entity_type(&person_label, false).unwrap();
        let owns_age = person_type.set_owns(&type_manager, age_type.clone(), Ordering::Unordered);
        owns_age.set_annotation(&type_manager, OwnsAnnotation::Distinct(AnnotationDistinct::new()));
        let _ = person_type.set_owns(&type_manager, name_type.clone(), Ordering::Unordered);

        let person_1 = thing_manager.create_entity(person_type.clone()).unwrap();
        let person_2 = thing_manager.create_entity(person_type.clone()).unwrap();
        let age_1 = thing_manager.create_attribute(age_type.clone(), Value::Long(age_value)).unwrap();
        let name_alice =
            thing_manager.create_attribute(name_type.clone(), Value::String(Cow::Borrowed(name_alice_value))).unwrap();
        let name_bob = thing_manager
            .create_attribute(name_type.clone(), Value::String(Cow::Owned(String::from(name_bob_value))))
            .unwrap();

        person_1.set_has_unordered(&thing_manager, age_1.as_reference()).unwrap();
        person_1.set_has_unordered(&thing_manager, name_alice.as_reference()).unwrap();
        person_2.set_has_unordered(&thing_manager, age_1).unwrap();
        person_2.set_has_unordered(&thing_manager, name_bob.as_reference()).unwrap();
        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }

    let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();

    // two concurrent snapshots delete the independent ownerships
    let snapshot_1: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());
    let snapshot_2: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());

    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot_1.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(snapshot_1.clone(), thing_vertex_generator.clone(), type_manager.clone());
        let name_type = type_manager.get_attribute_type(&name_label).unwrap().unwrap();
        let age_type = type_manager.get_attribute_type(&age_label).unwrap().unwrap();

        let entities = thing_manager.get_entities().collect_cloned();
        let bob = entities
            .iter()
            .filter(|entity| {
                entity
                    .has_attribute(&thing_manager, name_type.clone(), Value::String(Cow::Borrowed(name_bob_value)))
                    .unwrap()
            })
            .next()
            .unwrap();

        let mut ages = thing_manager.get_attributes_in(age_type.clone()).unwrap().collect_cloned();
        let age = ages
            .iter_mut()
            .find_map(|attr| {
                if attr.get_value(&thing_manager).unwrap().unwrap_long() == age_value {
                    Some(attr.as_reference())
                } else {
                    None
                }
            })
            .unwrap();
        bob.delete_has_unordered(&thing_manager, age).unwrap();

        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }

    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot_2.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(snapshot_2.clone(), thing_vertex_generator.clone(), type_manager.clone());
        let name_type = type_manager.get_attribute_type(&name_label).unwrap().unwrap();
        let age_type = type_manager.get_attribute_type(&age_label).unwrap().unwrap();

        let entities = thing_manager.get_entities().collect_cloned();
        let alice = entities
            .iter()
            .filter(|entity| {
                entity
                    .has_attribute(&thing_manager, name_type.clone(), Value::String(Cow::Borrowed(name_bob_value)))
                    .unwrap()
            })
            .next()
            .unwrap();

        let mut ages = thing_manager.get_attributes_in(age_type.clone()).unwrap().collect_cloned();
        let age = ages
            .iter_mut()
            .find_map(|attr| {
                if attr.get_value(&thing_manager).unwrap().unwrap_long() == age_value {
                    Some(attr.as_reference())
                } else {
                    None
                }
            })
            .unwrap();
        alice.delete_has_unordered(&thing_manager, age).unwrap();

        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }

    let write_snapshot_1 = Arc::try_unwrap(snapshot_1).ok().unwrap();
    write_snapshot_1.commit().unwrap();
    let write_snapshot_2 = Arc::try_unwrap(snapshot_2).ok().unwrap();
    write_snapshot_2.commit().unwrap();
    {
        let snapshot: Arc<ReadSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_read());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());
        let age_type = type_manager.get_attribute_type(&age_label).unwrap().unwrap();

        let attributes = thing_manager.get_attributes_in(age_type).unwrap().collect_cloned();
        assert_eq!(attributes.len(), 0);
    }
}

#[test]
fn role_player_distinct() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();

    let employment_label = Label::build("employment");
    let employee_role = "employee";
    let employer_role = "employer";
    let person_label = Label::build("person");
    let company_label = Label::build("company");

    let snapshot: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());
    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());

        let employment_type = type_manager.create_relation_type(&employment_label, false).unwrap();
        employment_type.create_relates(&type_manager, employee_role, Ordering::Unordered).unwrap();
        let employee_type = employment_type.get_relates_role(&type_manager, employee_role).unwrap().unwrap().role();
        employee_type.set_annotation(&type_manager, RoleTypeAnnotation::Distinct(AnnotationDistinct::new())).unwrap();
        employment_type.create_relates(&type_manager, employer_role, Ordering::Unordered).unwrap();
        let employer_type = employment_type.get_relates_role(&type_manager, employer_role).unwrap().unwrap().role();
        employer_type.set_annotation(&type_manager, RoleTypeAnnotation::Distinct(AnnotationDistinct::new())).unwrap();
        employer_type
            .set_annotation(&type_manager, RoleTypeAnnotation::Cardinality(AnnotationCardinality::new(1, Some(2))))
            .unwrap();

        let person_type = type_manager.create_entity_type(&person_label, false).unwrap();
        let company_type = type_manager.create_entity_type(&company_label, false).unwrap();
        person_type.set_plays(&type_manager, employee_type.clone());
        company_type.set_plays(&type_manager, employee_type.clone());

        let person_1 = thing_manager.create_entity(person_type.clone()).unwrap();
        let company_1 = thing_manager.create_entity(company_type.clone()).unwrap();
        let company_2 = thing_manager.create_entity(company_type.clone()).unwrap();
        let company_3 = thing_manager.create_entity(company_type.clone()).unwrap();

        let employment_1 = thing_manager.create_relation(employment_type.clone()).unwrap();
        employment_1
            .add_player(&thing_manager, employee_type.clone(), Object::Entity(person_1.as_reference()))
            .unwrap();
        employment_1
            .add_player(&thing_manager, employer_type.clone(), Object::Entity(company_1.as_reference()))
            .unwrap();

        let employment_2 = thing_manager.create_relation(employment_type.clone()).unwrap();
        employment_2
            .add_player(&thing_manager, employee_type.clone(), Object::Entity(person_1.as_reference()))
            .unwrap();
        employment_2
            .add_player(&thing_manager, employer_type.clone(), Object::Entity(company_2.as_reference()))
            .unwrap();
        employment_2
            .add_player(&thing_manager, employer_type.clone(), Object::Entity(company_3.as_reference()))
            .unwrap();

        assert_eq!(employment_1.get_players(&thing_manager).count(), 2);
        assert_eq!(employment_2.get_players(&thing_manager).count(), 3);

        assert_eq!(person_1.get_relations(&thing_manager).count(), 2);
        assert_eq!(company_1.get_relations(&thing_manager).count(), 1);
        assert_eq!(company_2.get_relations(&thing_manager).count(), 1);
        assert_eq!(company_3.get_relations(&thing_manager).count(), 1);

        assert_eq!(person_1.get_indexed_players(&thing_manager).count(), 3);

        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }

    let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();
    {
        let snapshot: Arc<ReadSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_read());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());
        let entities = thing_manager.get_entities().collect_cloned();
        assert_eq!(entities.len(), 4);
        let relations = thing_manager.get_relations().collect_cloned();
        assert_eq!(relations.len(), 2);

        let players_0 = relations[0].get_players(&thing_manager).count();
        if players_0 == 2 {
            assert_eq!(relations[1].get_players(&thing_manager).count(), 3);
        } else {
            assert_eq!(relations[1].get_players(&thing_manager).count(), 2);
        }

        let person_1 = entities
            .iter()
            .find(|entity| entity.type_() == type_manager.get_entity_type(&person_label).unwrap().unwrap())
            .unwrap();

        assert_eq!(person_1.get_relations(&thing_manager).count(), 2);
        assert_eq!(person_1.get_indexed_players(&thing_manager).count(), 3);
    }
}

#[test]
fn role_player_duplicates() {
    init_logging();
    let storage_path = create_tmp_dir();
    let storage = Arc::new(MVCCStorage::<WAL>::open::<EncodingKeyspace>("storage", &storage_path).unwrap());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    TypeManager::<WriteSnapshot<WAL>>::initialise_types(storage.clone(), type_vertex_generator.clone()).unwrap();

    let list_label = Label::build("list");
    let entry_role_label = "entry";
    let owner_role_label = "owner";
    let resource_label = Label::build("resource");
    let group_label = Label::build("group");

    let snapshot: Arc<WriteSnapshot<WAL>> = Arc::new(storage.clone().open_snapshot_write());
    {
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator.clone(), type_manager.clone());

        let list_type = type_manager.create_relation_type(&list_label, false).unwrap();
        list_type.create_relates(&type_manager, entry_role_label, Ordering::Unordered).unwrap();
        let entry_type = list_type.get_relates_role(&type_manager, entry_role_label).unwrap().unwrap().role();
        entry_type
            .set_annotation(
                &type_manager,
                RoleTypeAnnotation::Cardinality(AnnotationCardinality::new(0, Some(4))), // must be small to allow index to kick in
            )
            .unwrap();
        list_type.create_relates(&type_manager, owner_role_label, Ordering::Unordered).unwrap();
        let owner_type = list_type.get_relates_role(&type_manager, owner_role_label).unwrap().unwrap().role();

        let resource_type = type_manager.create_entity_type(&resource_label, false).unwrap();
        let group_type = type_manager.create_entity_type(&group_label, false).unwrap();
        resource_type.set_plays(&type_manager, entry_type.clone());
        group_type.set_plays(&type_manager, owner_type.clone());

        let group_1 = thing_manager.create_entity(group_type.clone()).unwrap();
        let resource_1 = thing_manager.create_entity(resource_type.clone()).unwrap();

        let list_1 = thing_manager.create_relation(list_type.clone()).unwrap();
        list_1.add_player(&thing_manager, owner_type.clone(), Object::Entity(group_1.as_reference())).unwrap();
        list_1.add_player(&thing_manager, entry_type.clone(), Object::Entity(resource_1.as_reference())).unwrap();
        list_1.add_player(&thing_manager, entry_type.clone(), Object::Entity(resource_1.as_reference())).unwrap();

        let player_counts: u64 =
            list_1.get_players(&thing_manager).collect_cloned_vec(|(_, count)| count).unwrap().into_iter().sum();
        assert_eq!(player_counts, 3);

        let group_relations_count: u64 =
            group_1.get_relations(&thing_manager).collect_cloned_vec(|(_, _, count)| count).unwrap().into_iter().sum();
        assert_eq!(group_relations_count, 1);
        let resource_relations_count: u64 = resource_1
            .get_relations(&thing_manager)
            .collect_cloned_vec(|(_, _, count)| count)
            .unwrap()
            .into_iter()
            .sum();
        assert_eq!(resource_relations_count, 2);

        let group_1_indexed_count: u64 = group_1
            .get_indexed_players(&thing_manager)
            .collect_cloned_vec(|(_, _, _, count)| count)
            .unwrap()
            .into_iter()
            .sum();
        assert_eq!(group_1_indexed_count, 2);
        let resource_1_indexed_count: u64 = resource_1
            .get_indexed_players(&thing_manager)
            .collect_cloned_vec(|(_, _, _, count)| count)
            .unwrap()
            .into_iter()
            .sum();
        assert_eq!(resource_1_indexed_count, 2);

        let group_relations_count: u64 =
            group_1.get_relations(&thing_manager).collect_cloned_vec(|(_, _, count)| count).unwrap().into_iter().sum();
        assert_eq!(group_relations_count, 1);

        let finalise_result = thing_manager.finalise();
        assert!(finalise_result.is_ok());
    }

    let write_snapshot = Arc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();
    {
        let snapshot: Arc<ReadSnapshot<WAL>> = Arc::new(storage.open_snapshot_read());
        let type_manager = Arc::new(TypeManager::new(snapshot.clone(), type_vertex_generator.clone(), None));
        let thing_vertex_generator = ThingVertexGenerator::new();
        let thing_manager = ThingManager::new(snapshot.clone(), Arc::new(thing_vertex_generator), type_manager.clone());
        let entities = thing_manager.get_entities().collect_cloned();
        assert_eq!(entities.len(), 2);
        let relations = thing_manager.get_relations().collect_cloned();
        assert_eq!(relations.len(), 1);

        let list_1 = relations.get(0).unwrap();
        let player_counts: u64 =
            list_1.get_players(&thing_manager).collect_cloned_vec(|(_, count)| count).unwrap().into_iter().sum();
        assert_eq!(player_counts, 3);

        let group_1 = entities
            .iter()
            .find(|entity| entity.type_() == type_manager.get_entity_type(&group_label).unwrap().unwrap())
            .unwrap();

        let resource_1 = entities
            .iter()
            .find(|entity| entity.type_() == type_manager.get_entity_type(&resource_label).unwrap().unwrap())
            .unwrap();

        let group_relations_count: u64 =
            group_1.get_relations(&thing_manager).collect_cloned_vec(|(_, _, count)| count).unwrap().into_iter().sum();
        assert_eq!(group_relations_count, 1);
        let resource_relations_count: u64 = resource_1
            .get_relations(&thing_manager)
            .collect_cloned_vec(|(_, _, count)| count)
            .unwrap()
            .into_iter()
            .sum();
        assert_eq!(resource_relations_count, 2);

        let group_1_indexed_count: u64 = group_1
            .get_indexed_players(&thing_manager)
            .collect_cloned_vec(|(_, _, _, count)| count)
            .unwrap()
            .into_iter()
            .sum();
        assert_eq!(group_1_indexed_count, 2);
        let resource_1_indexed_count: u64 = resource_1
            .get_indexed_players(&thing_manager)
            .collect_cloned_vec(|(_, _, _, count)| count)
            .unwrap()
            .into_iter()
            .sum();
        assert_eq!(resource_1_indexed_count, 2);
    }
}
