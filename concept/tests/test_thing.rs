/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::{borrow::Cow, collections::HashMap, sync::Arc};

use concept::{
    error::ConceptReadError,
    thing::{
        attribute::Attribute,
        object::{Object, ObjectAPI},
        thing_manager::ThingManager,
    },
    type_::{
        annotation::{AnnotationCardinality, AnnotationDistinct, AnnotationIndependent},
        attribute_type::AttributeTypeAnnotation,
        owns::OwnsAnnotation,
        relates::RelatesAnnotation,
        role_type::RoleTypeAnnotation,
        type_manager::TypeManager,
        Ordering, OwnerAPI, PlayerAPI,
    },
};
use durability::wal::WAL;
use encoding::{
    error::EncodingError,
    graph::{
        definition::{definition_key::DefinitionKey, definition_key_generator::DefinitionKeyGenerator},
        thing::vertex_generator::ThingVertexGenerator,
        type_::vertex_generator::TypeVertexGenerator,
    },
    value::{
        label::Label,
        value::Value,
        value_struct::StructValue,
        value_type::{ValueType, ValueTypeCategory},
    },
    EncodingKeyspace,
};
use lending_iterator::LendingIterator;
use storage::{
    durability_client::WALClient,
    snapshot::{CommittableSnapshot, ReadSnapshot, ReadableSnapshot, WritableSnapshot, WriteSnapshot},
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging};

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

fn managers<Snapshot: ReadableSnapshot>(
    storage: Arc<MVCCStorage<WALClient>>,
) -> (Arc<TypeManager<Snapshot>>, ThingManager<Snapshot>) {
    let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
    let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
    let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
    let type_manager =
        Arc::new(TypeManager::new(definition_key_generator.clone(), type_vertex_generator.clone(), None));
    let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());

    (type_manager, thing_manager)
}

#[test]
fn thing_create_iterate() {
    let storage = setup_storage();

    let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    {
        let (type_manager, thing_manager) = managers(storage.clone());

        let person_label = Label::build("person");
        let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();

        let _person_1 = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
        let _person_2 = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
        let _person_3 = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
        let _person_4 = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();

        let finalise_result = thing_manager.finalise(&mut snapshot);
        assert!(finalise_result.is_ok());
    }
    snapshot.commit().unwrap();

    {
        let snapshot: ReadSnapshot<WALClient> = storage.clone().open_snapshot_read();
        let (type_manager, thing_manager) = managers(storage.clone());
        let entities = thing_manager.get_entities(&snapshot).collect_cloned();
        assert_eq!(entities.len(), 4);
    }
}

#[test]
fn attribute_create() {
    let storage = setup_storage();

    let age_label = Label::build("age");
    let name_label = Label::build("name");

    let age_value: i64 = 10;
    let name_value: &str = "TypeDB Fan";

    let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    {
        let (type_manager, thing_manager) = managers(storage.clone());
        let age_type = type_manager.create_attribute_type(&mut snapshot, &age_label, false).unwrap();
        age_type.set_value_type(&mut snapshot, &type_manager, ValueType::Long).unwrap();
        age_type
            .set_annotation(&mut snapshot, &type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent))
            .unwrap();
        let name_type = type_manager.create_attribute_type(&mut snapshot, &name_label, false).unwrap();
        name_type.set_value_type(&mut snapshot, &type_manager, ValueType::String).unwrap();
        name_type
            .set_annotation(&mut snapshot, &type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent))
            .unwrap();

        let mut age_1 =
            thing_manager.create_attribute(&mut snapshot, age_type.clone(), Value::Long(age_value)).unwrap();
        assert_eq!(age_1.get_value(&snapshot, &thing_manager).unwrap(), Value::Long(age_value));

        let mut name_1 = thing_manager
            .create_attribute(&mut snapshot, name_type.clone(), Value::String(Cow::Borrowed(name_value)))
            .unwrap();
        assert_eq!(name_1.get_value(&snapshot, &thing_manager).unwrap(), Value::String(Cow::Borrowed(name_value)));

        let finalise_result = thing_manager.finalise(&mut snapshot);
        assert!(finalise_result.is_ok());
    }
    snapshot.commit().unwrap();

    {
        let snapshot: ReadSnapshot<WALClient> = storage.clone().open_snapshot_read();
        let (type_manager, thing_manager) = managers(storage.clone());
        let attributes = thing_manager.get_attributes(&snapshot).collect_cloned();
        assert_eq!(attributes.len(), 2);

        let age_type = type_manager.get_attribute_type(&snapshot, &age_label).unwrap().unwrap();
        let mut ages = thing_manager.get_attributes_in(&snapshot, age_type).unwrap().collect_cloned();
        assert_eq!(ages.len(), 1);
        assert_eq!(ages.first_mut().unwrap().get_value(&snapshot, &thing_manager).unwrap(), Value::Long(age_value));
    }
}

#[test]
fn has() {
    let storage = setup_storage();

    let age_label = Label::build("age");
    let name_label = Label::build("name");
    let person_label = Label::build("person");

    let age_value: i64 = 10;
    let name_value: &str = "TypeDB Fan";

    let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    {
        let (type_manager, thing_manager) = managers(storage.clone());

        let age_type = type_manager.create_attribute_type(&mut snapshot, &age_label, false).unwrap();
        age_type.set_value_type(&mut snapshot, &type_manager, ValueType::Long).unwrap();
        age_type
            .set_annotation(&mut snapshot, &type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent))
            .unwrap();
        let name_type = type_manager.create_attribute_type(&mut snapshot, &name_label, false).unwrap();
        name_type.set_value_type(&mut snapshot, &type_manager, ValueType::String).unwrap();
        name_type
            .set_annotation(&mut snapshot, &type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent))
            .unwrap();

        let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();
        person_type.set_owns(&mut snapshot, &type_manager, age_type.clone(), Ordering::Unordered).unwrap();
        person_type.set_owns(&mut snapshot, &type_manager, name_type.clone(), Ordering::Unordered).unwrap();

        let person_1 = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
        let age_1 = thing_manager.create_attribute(&mut snapshot, age_type.clone(), Value::Long(age_value)).unwrap();
        let name_1 = thing_manager
            .create_attribute(&mut snapshot, name_type.clone(), Value::String(Cow::Owned(String::from(name_value))))
            .unwrap();

        person_1.set_has_unordered(&mut snapshot, &thing_manager, age_1).unwrap();
        person_1.set_has_unordered(&mut snapshot, &thing_manager, name_1).unwrap();

        let retrieved_attributes_count = person_1.get_has_unordered(&snapshot, &thing_manager).count();
        assert_eq!(retrieved_attributes_count, 2);

        let finalise_result = thing_manager.finalise(&mut snapshot);
        assert!(finalise_result.is_ok());
    }
    snapshot.commit().unwrap();

    {
        let snapshot: ReadSnapshot<WALClient> = storage.clone().open_snapshot_read();
        let (_, thing_manager) = managers(storage.clone());
        let attributes = thing_manager.get_attributes(&snapshot).collect_cloned();
        assert_eq!(attributes.len(), 2);

        let people = thing_manager.get_entities(&snapshot).collect_cloned();
        let person_1 = people.first().unwrap();
        let retrieved_attributes_count = person_1.get_has_unordered(&snapshot, &thing_manager).count();
        assert_eq!(retrieved_attributes_count, 2);
    }
}

#[test]
fn attribute_cleanup_on_concurrent_detach() {
    let storage = setup_storage();

    let age_label = Label::build("age");
    let name_label = Label::build("name");
    let person_label = Label::build("person");

    let age_value: i64 = 10;
    let name_alice_value: &str = "Alice";
    let name_bob_value: &str = "Bob";

    let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    {
        let (type_manager, thing_manager) = managers(storage.clone());
        let age_type = type_manager.create_attribute_type(&mut snapshot, &age_label, false).unwrap();
        age_type.set_value_type(&mut snapshot, &type_manager, ValueType::Long).unwrap();
        let name_type = type_manager.create_attribute_type(&mut snapshot, &name_label, false).unwrap();
        name_type.set_value_type(&mut snapshot, &type_manager, ValueType::String).unwrap();

        let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();
        let owns_age =
            person_type.set_owns(&mut snapshot, &type_manager, age_type.clone(), Ordering::Ordered).unwrap();
        owns_age.set_annotation(&mut snapshot, &type_manager, OwnsAnnotation::Distinct(AnnotationDistinct)).unwrap();

        person_type.set_owns(&mut snapshot, &type_manager, name_type.clone(), Ordering::Unordered).unwrap();

        let alice = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
        let bob = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
        let age = thing_manager.create_attribute(&mut snapshot, age_type.clone(), Value::Long(age_value)).unwrap();
        let name_alice = thing_manager
            .create_attribute(&mut snapshot, name_type.clone(), Value::String(Cow::Borrowed(name_alice_value)))
            .unwrap();
        let name_bob = thing_manager
            .create_attribute(&mut snapshot, name_type.clone(), Value::String(Cow::Owned(String::from(name_bob_value))))
            .unwrap();

        alice.set_has_ordered(&mut snapshot, &thing_manager, age_type.clone(), vec!(age.as_reference())).unwrap();
        alice.set_has_unordered(&mut snapshot, &thing_manager, name_alice).unwrap();
        bob.set_has_ordered(&mut snapshot, &thing_manager, age_type, vec!(age.as_reference())).unwrap();
        bob.set_has_unordered(&mut snapshot, &thing_manager, name_bob).unwrap();
        let finalise_result = thing_manager.finalise(&mut snapshot);
        assert!(finalise_result.is_ok());
    }
    snapshot.commit().unwrap();

    // two concurrent snapshots delete the independent ownerships
    let mut snapshot_1: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    let mut snapshot_2: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();

    {
        let (type_manager, thing_manager) = managers(storage.clone());

        let name_type = type_manager.get_attribute_type(&snapshot_1, &name_label).unwrap().unwrap();
        let age_type = type_manager.get_attribute_type(&snapshot_1, &age_label).unwrap().unwrap();

        let entities = thing_manager.get_entities(&snapshot_1).collect_cloned();
        let bob = entities
            .iter()
            .find(|entity| {
                entity
                    .has_attribute(
                        &snapshot_1,
                        &thing_manager,
                        name_type.clone(),
                        Value::String(Cow::Borrowed(name_bob_value)),
                    )
                    .unwrap()
            })
            .unwrap();

        let mut ages = thing_manager.get_attributes_in(&snapshot_1, age_type.clone()).unwrap().collect_cloned();
        let age = ages
            .iter_mut()
            .filter_map(|attr| {
                if attr.get_value(&snapshot_1, &thing_manager).unwrap().unwrap_long() == age_value {
                    Some(attr.as_reference())
                } else {
                    None
                }
            })
            .next()
            .unwrap();
        bob.unset_has_ordered(&mut snapshot_1, &thing_manager, age_type).unwrap();

        let finalise_result = thing_manager.finalise(&mut snapshot_1);
        assert!(finalise_result.is_ok());
    }

    {
        let (type_manager, thing_manager) = managers(storage.clone());

        let name_type = type_manager.get_attribute_type(&snapshot_2, &name_label).unwrap().unwrap();
        let age_type = type_manager.get_attribute_type(&snapshot_2, &age_label).unwrap().unwrap();

        let entities = thing_manager.get_entities(&snapshot_2).collect_cloned();
        let alice = entities
            .iter()
            .find(|entity| {
                entity
                    .has_attribute(
                        &snapshot_2,
                        &thing_manager,
                        name_type.clone(),
                        Value::String(Cow::Borrowed(name_alice_value)),
                    )
                    .unwrap()
            })
            .unwrap();

        let mut ages = thing_manager.get_attributes_in(&snapshot_2, age_type.clone()).unwrap().collect_cloned();
        let age = ages
            .iter_mut()
            .filter_map(|attr| {
                if attr.get_value(&snapshot_2, &thing_manager).unwrap().unwrap_long() == age_value {
                    Some(attr.as_reference())
                } else {
                    None
                }
            })
            .next()
            .unwrap();
        alice.unset_has_unordered(&mut snapshot_2, &thing_manager, age).unwrap();

        let finalise_result = thing_manager.finalise(&mut snapshot_2);
        assert!(finalise_result.is_ok());
    }
    snapshot_1.commit().unwrap();
    snapshot_2.commit().unwrap();

    {
        let snapshot: ReadSnapshot<WALClient> = storage.clone().open_snapshot_read();
        let (type_manager, thing_manager) = managers(storage.clone());

        let age_type = type_manager.get_attribute_type(&snapshot, &age_label).unwrap().unwrap();

        let attributes = thing_manager.get_attributes_in(&snapshot, age_type).unwrap().collect_cloned();
        assert_eq!(attributes.len(), 0);
    }
}

#[test]
fn role_player_distinct() {
    let storage = setup_storage();

    let employment_label = Label::build("employment");
    let employee_role = "employee";
    let employer_role = "employer";
    let person_label = Label::build("person");
    let company_label = Label::build("company");

    let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    {
        let (type_manager, thing_manager) = managers(storage.clone());

        let employment_type = type_manager.create_relation_type(&mut snapshot, &employment_label, false).unwrap();
        employment_type.create_relates(&mut snapshot, &type_manager, employee_role, Ordering::Ordered).unwrap();
        let employee_relates =
            employment_type.get_relates_role(&snapshot, &type_manager, employee_role).unwrap().unwrap();
        employee_relates
            .set_annotation(&mut snapshot, &type_manager, RelatesAnnotation::Distinct(AnnotationDistinct))
            .unwrap();
        let employee_type = employee_relates.role();

        employment_type.create_relates(&mut snapshot, &type_manager, employer_role, Ordering::Ordered).unwrap();
        let employer_relates =
            employment_type.get_relates_role(&snapshot, &type_manager, employer_role).unwrap().unwrap();
        employer_relates
            .set_annotation(&mut snapshot, &type_manager, RelatesAnnotation::Distinct(AnnotationDistinct))
            .unwrap();
        employer_relates
            .set_annotation(
                &mut snapshot,
                &type_manager,
                RelatesAnnotation::Cardinality(AnnotationCardinality::new(1, Some(2))),
            )
            .unwrap();
        let employer_type = employer_relates.role();

        let person_type = type_manager.create_entity_type(&mut snapshot, &person_label, false).unwrap();
        let company_type = type_manager.create_entity_type(&mut snapshot, &company_label, false).unwrap();
        person_type.set_plays(&mut snapshot, &type_manager, employee_type.clone()).unwrap();
        company_type.set_plays(&mut snapshot, &type_manager, employee_type.clone()).unwrap();

        let person_1 = thing_manager.create_entity(&mut snapshot, person_type.clone()).unwrap();
        let company_1 = thing_manager.create_entity(&mut snapshot, company_type.clone()).unwrap();
        let company_2 = thing_manager.create_entity(&mut snapshot, company_type.clone()).unwrap();
        let company_3 = thing_manager.create_entity(&mut snapshot, company_type.clone()).unwrap();

        let employment_1 = thing_manager.create_relation(&mut snapshot, employment_type.clone()).unwrap();
        employment_1
            .add_player(&mut snapshot, &thing_manager, employee_type.clone(), Object::Entity(person_1.as_reference()))
            .unwrap();
        employment_1
            .add_player(&mut snapshot, &thing_manager, employer_type.clone(), Object::Entity(company_1.as_reference()))
            .unwrap();

        let employment_2 = thing_manager.create_relation(&mut snapshot, employment_type.clone()).unwrap();
        employment_2
            .add_player(&mut snapshot, &thing_manager, employee_type.clone(), Object::Entity(person_1.as_reference()))
            .unwrap();
        employment_2
            .add_player(&mut snapshot, &thing_manager, employer_type.clone(), Object::Entity(company_2.as_reference()))
            .unwrap();
        employment_2
            .add_player(&mut snapshot, &thing_manager, employer_type.clone(), Object::Entity(company_3.as_reference()))
            .unwrap();

        assert_eq!(employment_1.get_players(&snapshot, &thing_manager).count(), 2);
        assert_eq!(employment_2.get_players(&snapshot, &thing_manager).count(), 3);

        assert_eq!(person_1.get_relations(&snapshot, &thing_manager).count(), 2);
        assert_eq!(company_1.get_relations(&snapshot, &thing_manager).count(), 1);
        assert_eq!(company_2.get_relations(&snapshot, &thing_manager).count(), 1);
        assert_eq!(company_3.get_relations(&snapshot, &thing_manager).count(), 1);

        assert_eq!(person_1.get_indexed_players(&snapshot, &thing_manager).count(), 3);

        let finalise_result = thing_manager.finalise(&mut snapshot);
        assert!(finalise_result.is_ok());
    }
    snapshot.commit().unwrap();
    {
        let snapshot: ReadSnapshot<WALClient> = storage.clone().open_snapshot_read();
        let (type_manager, thing_manager) = managers(storage.clone());

        let entities = thing_manager.get_entities(&snapshot).collect_cloned();
        assert_eq!(entities.len(), 4);
        let relations = thing_manager.get_relations(&snapshot).collect_cloned();
        assert_eq!(relations.len(), 2);

        let players_0 = relations[0].get_players(&snapshot, &thing_manager).count();
        if players_0 == 2 {
            assert_eq!(relations[1].get_players(&snapshot, &thing_manager).count(), 3);
        } else {
            assert_eq!(relations[1].get_players(&snapshot, &thing_manager).count(), 2);
        }

        let person_1 = entities
            .iter()
            .find(|entity| entity.type_() == type_manager.get_entity_type(&snapshot, &person_label).unwrap().unwrap())
            .unwrap();

        assert_eq!(person_1.get_relations(&snapshot, &thing_manager).count(), 2);
        assert_eq!(person_1.get_indexed_players(&snapshot, &thing_manager).count(), 3);
    }
}

#[test]
fn role_player_duplicates() {
    let storage = setup_storage();

    let list_label = Label::build("list");
    let entry_role_label = "entry";
    let owner_role_label = "owner";
    let resource_label = Label::build("resource");
    let group_label = Label::build("group");

    let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    {
        let (type_manager, thing_manager) = managers(storage.clone());
        let list_type = type_manager.create_relation_type(&mut snapshot, &list_label, false).unwrap();
        list_type.create_relates(&mut snapshot, &type_manager, entry_role_label, Ordering::Unordered).unwrap();
        let entry_relates =
            list_type.get_relates_role(&snapshot, &type_manager, entry_role_label).unwrap().unwrap();
        entry_relates
            .set_annotation(
                &mut snapshot,
                &type_manager,
                RelatesAnnotation::Cardinality(AnnotationCardinality::new(0, Some(4))), // must be small to allow index to kick in
            )
            .unwrap();
        let entry_type = entry_relates.role();
        list_type.create_relates(&mut snapshot, &type_manager, owner_role_label, Ordering::Unordered).unwrap();
        let owner_type =
            list_type.get_relates_role(&snapshot, &type_manager, owner_role_label).unwrap().unwrap().role();

        let resource_type = type_manager.create_entity_type(&mut snapshot, &resource_label, false).unwrap();
        let group_type = type_manager.create_entity_type(&mut snapshot, &group_label, false).unwrap();
        resource_type.set_plays(&mut snapshot, &type_manager, entry_type.clone()).unwrap();
        group_type.set_plays(&mut snapshot, &type_manager, owner_type.clone()).unwrap();

        let group_1 = thing_manager.create_entity(&mut snapshot, group_type.clone()).unwrap();
        let resource_1 = thing_manager.create_entity(&mut snapshot, resource_type.clone()).unwrap();

        let list_1 = thing_manager.create_relation(&mut snapshot, list_type.clone()).unwrap();
        list_1
            .add_player(&mut snapshot, &thing_manager, owner_type.clone(), Object::Entity(group_1.as_reference()))
            .unwrap();
        list_1
            .add_player(&mut snapshot, &thing_manager, entry_type.clone(), Object::Entity(resource_1.as_reference()))
            .unwrap();
        list_1
            .add_player(&mut snapshot, &thing_manager, entry_type.clone(), Object::Entity(resource_1.as_reference()))
            .unwrap();

        let player_counts: u64 =
            list_1.get_players(&snapshot, &thing_manager).map_static(|res| res.unwrap().1).into_iter().sum();
        assert_eq!(player_counts, 3);

        let group_relations_count: u64 = group_1
            .get_relations(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(group_relations_count, 1);
        let resource_relations_count: u64 = resource_1
            .get_relations(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(resource_relations_count, 2);

        let group_1_indexed_count: u64 = group_1
            .get_indexed_players(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(group_1_indexed_count, 2);
        let resource_1_indexed_count: u64 = resource_1
            .get_indexed_players(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(resource_1_indexed_count, 2);

        let group_relations_count: u64 = group_1
            .get_relations(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(group_relations_count, 1);

        let finalise_result = thing_manager.finalise(&mut snapshot);
        assert!(finalise_result.is_ok());
    }
    snapshot.commit().unwrap();
    {
        let snapshot: ReadSnapshot<WALClient> = storage.clone().open_snapshot_read();
        let (type_manager, thing_manager) = managers(storage.clone());
        let entities = thing_manager.get_entities(&snapshot).collect_cloned();
        assert_eq!(entities.len(), 2);
        let relations = thing_manager.get_relations(&snapshot).collect_cloned();
        assert_eq!(relations.len(), 1);

        let list_1 = relations.first().unwrap();
        let player_counts: u64 =
            list_1.get_players(&snapshot, &thing_manager).map_static(|res| res.unwrap().1).into_iter().sum();
        assert_eq!(player_counts, 3);

        let group_1 = entities
            .iter()
            .find(|entity| entity.type_() == type_manager.get_entity_type(&snapshot, &group_label).unwrap().unwrap())
            .unwrap();

        let resource_1 = entities
            .iter()
            .find(|entity| entity.type_() == type_manager.get_entity_type(&snapshot, &resource_label).unwrap().unwrap())
            .unwrap();

        let group_relations_count: u64 = group_1
            .get_relations(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(group_relations_count, 1);
        let resource_relations_count: u64 = resource_1
            .get_relations(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(resource_relations_count, 2);

        let group_1_indexed_count: u64 = group_1
            .get_indexed_players(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(group_1_indexed_count, 2);
        let resource_1_indexed_count: u64 = resource_1
            .get_indexed_players(&snapshot, &thing_manager)
            .map_static(|res| {
                let (_, _, _, count) = res.unwrap();
                count
            })
            .into_iter()
            .sum();
        assert_eq!(resource_1_indexed_count, 2);
    }
}

#[test]
fn attribute_string_write_read() {
    let storage = setup_storage();
    let (type_manager, thing_manager) = managers(storage.clone());
    let attr_label = Label::build("test_string_attr");
    let short_string = "short".to_owned();
    let long_string = "this string is 33 characters long".to_owned();
    let attr_type = {
        let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
        let attr_type = type_manager.create_attribute_type(&mut snapshot, &attr_label, false).unwrap();
        attr_type.set_value_type(&mut snapshot, &type_manager, ValueType::String).unwrap();
        attr_type
            .set_annotation(&mut snapshot, &type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent))
            .unwrap();

        snapshot.commit().unwrap();
        attr_type
    };

    {
        let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
        thing_manager
            .create_attribute(&mut snapshot, attr_type.clone(), Value::String(Cow::Borrowed(short_string.as_str())))
            .unwrap();
        thing_manager
            .create_attribute(&mut snapshot, attr_type.clone(), Value::String(Cow::Borrowed(long_string.as_str())))
            .unwrap();
        snapshot.commit().unwrap();
    };

    // read them back by type
    {
        let snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
        let mut attrs = thing_manager.get_attributes_in(&snapshot, attr_type.clone()).unwrap().collect_cloned();
        let attr_values: Vec<String> = attrs
            .into_iter()
            .map(|mut attr| (*attr.get_value(&snapshot, &thing_manager).unwrap().unwrap_string()).to_owned())
            .collect();
        assert!(attr_values.contains(&short_string));
        assert!(attr_values.contains(&long_string));
    }
    // read them back by value
    {
        let snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
        let mut read_short_string = thing_manager
            .get_attribute_with_value(&snapshot, attr_type.clone(), Value::String(Cow::Borrowed(short_string.as_str())))
            .unwrap()
            .unwrap();
        assert_eq!(short_string, read_short_string.get_value(&snapshot, &thing_manager).unwrap().unwrap_string());
        let mut read_long_string = thing_manager
            .get_attribute_with_value(&snapshot, attr_type.clone(), Value::String(Cow::Borrowed(long_string.as_str())))
            .unwrap()
            .unwrap();
        assert_eq!(long_string, read_long_string.get_value(&snapshot, &thing_manager).unwrap().unwrap_string());
    }
}

#[test]
fn attribute_struct_write_read() {
    let storage = setup_storage();
    let (type_manager, thing_manager) = managers(storage.clone());

    let attr_label = Label::build("struct_test_attr");
    let struct_name = "struct_test_test".to_owned();
    let fields: HashMap<String, (ValueType, bool)> =
        HashMap::from([("f0l".to_owned(), (ValueType::Long, false)), ("f1s".to_owned(), (ValueType::String, false))]);

    let instance_fields = HashMap::from([
        ("f0l".to_owned(), Value::Long(123)),
        ("f1s".to_owned(), Value::String(Cow::Owned("abc".to_owned()))),
    ]);
    let struct_key = {
        let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
        let struct_key = define_struct(&mut snapshot, &type_manager, struct_name, fields);
        let attr_type = type_manager.create_attribute_type(&mut snapshot, &attr_label, false).unwrap();
        attr_type
            .set_annotation(&mut snapshot, &type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent))
            .unwrap();
        attr_type.set_value_type(&mut snapshot, &type_manager, ValueType::Struct(struct_key.clone())).unwrap();
        snapshot.commit().unwrap();
        struct_key
    };

    let (attr_created, struct_value) = {
        let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
        let mut attr_type = type_manager.get_attribute_type(&snapshot, &attr_label).unwrap().unwrap();
        let struct_value = StructValue::build(
            struct_key.clone(),
            type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap().clone(),
            instance_fields,
        )
        .unwrap();

        let attr_value_type = attr_type.get_value_type(&snapshot, &type_manager).unwrap().unwrap();
        assert_eq!(ValueTypeCategory::Struct, attr_value_type.category());
        let attr_instance = thing_manager
            .create_attribute(&mut snapshot, attr_type, Value::Struct(Cow::Owned(struct_value.clone())))
            .unwrap();
        snapshot.commit().unwrap();
        (attr_instance, struct_value)
    };

    {
        let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
        let attr_type = type_manager.get_attribute_type(&snapshot, &attr_label).unwrap().unwrap();
        let attr_vec = thing_manager.get_attributes_in(&snapshot, attr_type.clone()).unwrap().collect_cloned();
        let mut attr = attr_vec.get(0).unwrap().clone();
        let value_0 = attr.get_value(&snapshot, &thing_manager).unwrap();
        match value_0 {
            Value::Struct(v) => {
                assert_eq!(struct_value, *v);
            }
            _ => assert!(false, "Wrong data type"),
        }

        let attr_by_id = thing_manager
            .get_attribute_with_value(&snapshot, attr_type.clone(), Value::Struct(Cow::Borrowed(&struct_value)))
            .unwrap()
            .unwrap();
        assert_eq!(attr, attr_by_id);
        assert_eq!(attr_created, attr);
        snapshot.close_resources();
    }
}

#[test]
fn read_attribute_struct_by_field() {
    let storage = setup_storage();
    let (type_manager, thing_manager) = managers(storage.clone());

    let attr_label = Label::build("index_test_attr");
    let nested_struct_spec =
        ("nested_test_struct".to_owned(), HashMap::from([("nested_string".to_owned(), (ValueType::String, false))]));

    let nested_struct_key = {
        let mut snapshot = storage.clone().open_snapshot_write();
        let nested_struct_key = define_struct(&mut snapshot, &type_manager, nested_struct_spec.0, nested_struct_spec.1);
        snapshot.commit().unwrap();
        nested_struct_key
    };

    let struct_spec = (
        "index_test_struct".to_owned(),
        HashMap::from([("f_nested".to_owned(), (ValueType::Struct(nested_struct_key.clone()), false))]),
    );
    let (attr_type, struct_key, struct_def) = {
        let mut snapshot = storage.clone().open_snapshot_write();
        let struct_key = define_struct(&mut snapshot, &type_manager, struct_spec.0, struct_spec.1);
        let mut attr_type = type_manager.create_attribute_type(&mut snapshot, &attr_label, false).unwrap();
        attr_type.set_value_type(&mut snapshot, &type_manager, ValueType::Struct(struct_key.clone())).unwrap();
        attr_type
            .set_annotation(&mut snapshot, &type_manager, AttributeTypeAnnotation::Independent(AnnotationIndependent))
            .unwrap();
        let struct_def = type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap();
        snapshot.commit().unwrap();
        (attr_type, struct_key.clone(), struct_def)
    };

    // Create value
    let field_values = ["abc", "xyz_but_long_enough_to_hash"];
    {
        let mut snapshot = storage.clone().open_snapshot_write();
        let mut attrs = Vec::new();
        for val in field_values {
            let nested_struct_value =
                StructValue::new(nested_struct_key.clone(), HashMap::from([(0, Value::String(Cow::Borrowed(val)))]));
            let outer_struct_value = StructValue::new(
                struct_key.clone(),
                HashMap::from([(0, Value::Struct(Cow::Owned(nested_struct_value)))]),
            );
            let attr = thing_manager
                .create_attribute(&mut snapshot, attr_type.clone(), Value::Struct(Cow::Borrowed(&outer_struct_value)))
                .unwrap();
            attrs.push(attr);
        }

        for (val, attr) in std::iter::zip(field_values, attrs.iter()) {
            let field_path = type_manager
                .resolve_struct_field(&snapshot, &vec!["f_nested", "nested_string"], struct_def.clone())
                .unwrap();
            let mut attr_by_field_iterator = thing_manager
                .get_attributes_by_struct_field(
                    &snapshot,
                    attr_type.clone(),
                    field_path,
                    Value::String(Cow::Borrowed(val)),
                )
                .unwrap();
            let mut attr_by_field: Vec<Attribute> = Vec::new();
            while let Some(res) = attr_by_field_iterator.next() {
                attr_by_field.push(res.as_ref().unwrap().clone().into_owned());
            }
            assert_eq!(1, attr_by_field.len());
            assert_eq!(attr, attr_by_field.get(0).unwrap());
        }
        snapshot.close_resources();
    };
}

#[test]
fn attribute_struct_errors() {
    let storage = setup_storage();
    let (type_manager, thing_manager) = managers(storage.clone());

    let (struct_key, nested_struct_key) = {
        let mut snapshot = storage.clone().open_snapshot_write();
        let nested_struct_spec = (
            "nested_test_struct".to_owned(),
            HashMap::from([("nested_string".to_owned(), (ValueType::String, false))]),
        );
        let nested_struct_key = define_struct(&mut snapshot, &type_manager, nested_struct_spec.0, nested_struct_spec.1);

        let struct_spec = (
            "errors_test_struct".to_owned(),
            HashMap::from([("f_nested".to_owned(), (ValueType::Struct(nested_struct_key.clone()), false))]),
        );
        let struct_key = define_struct(&mut snapshot, &type_manager, struct_spec.0, struct_spec.1);
        snapshot.commit().unwrap();
        (struct_key, nested_struct_key)
    };

    {
        let snapshot = storage.clone().open_snapshot_write();
        let struct_def = type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap();
        assert!(matches!(
            type_manager.resolve_struct_field(&snapshot, &vec!["non-existant"], struct_def.clone()),
            Err(ConceptReadError::Encoding { source: EncodingError::StructFieldUnresolvable { .. } })
        ));
        assert!(matches!(
            type_manager.resolve_struct_field(
                &snapshot,
                &vec!["f_nested", "nested_string", "but-strings-arent-structs"],
                struct_def.clone()
            ),
            Err(ConceptReadError::Encoding { source: EncodingError::IndexingIntoNonStructField { .. } })
        ));
        assert!(matches!(
            type_manager.resolve_struct_field(&snapshot, &vec![], struct_def.clone()),
            Err(ConceptReadError::Encoding { source: EncodingError::StructPathIncomplete { .. } })
        ));
    };

    {
        let mut snapshot = storage.clone().open_snapshot_write();
        let struct_def = type_manager.get_struct_definition(&snapshot, struct_key.clone()).unwrap();
        type_manager.get_struct_definition(&snapshot, nested_struct_key.clone()).unwrap();
        {
            let err = StructValue::build(
                struct_key.clone(),
                struct_def.clone(),
                HashMap::from([("f_nested".to_owned(), Value::Long(0))]),
            )
            .unwrap_err();
            assert!(
                err.len() == 1 && matches!(err.get(0).unwrap(), EncodingError::StructFieldValueTypeMismatch { .. })
            );
        }
        {
            let err = StructValue::build(struct_key.clone(), struct_def.clone(), HashMap::from([])).unwrap_err();
            assert!(err.len() == 1 && matches!(err.get(0).unwrap(), EncodingError::StructMissingRequiredField { .. }));
        }
        snapshot.close_resources();
    }
}

pub fn define_struct<Snapshot: WritableSnapshot>(
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
