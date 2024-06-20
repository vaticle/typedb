/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use concept::{
    error::ConceptWriteError,
    thing::{
        object::{Object, ObjectAPI},
        ThingAPI,
    },
    type_::{object_type::ObjectType, OwnerAPI, TypeAPI},
};
use itertools::Itertools;
use lending_iterator::LendingIterator;
use macro_rules_attribute::apply;

use crate::{
    assert::assert_matches,
    concept::thing::{
        attribute::{attribute_put_instance_with_value_impl, get_attribute_by_value},
        has::object_set_has_impl,
    },
    generic_step, params,
    params::check_boolean,
    thing_util::ObjectWithKey,
    transaction_context::{with_read_tx, with_write_tx},
    Context,
};

fn object_create_instance_impl(
    context: &mut Context,
    object_type_label: params::Label,
) -> Result<Object<'static>, ConceptWriteError> {
    with_write_tx!(context, |tx| {
        let object_type =
            tx.type_manager.get_object_type(&tx.snapshot, &object_type_label.into_typedb()).unwrap().unwrap();
        match object_type {
            ObjectType::Entity(entity_type) => {
                tx.thing_manager.create_entity(&mut tx.snapshot, entity_type).map(Object::Entity)
            }
            ObjectType::Relation(relation_type) => {
                tx.thing_manager.create_relation(&mut tx.snapshot, relation_type).map(Object::Relation)
            }
        }
    })
}

#[apply(generic_step)]
#[step(expr = r"{var} = {object_root_label}\({type_label}\) create new instance")]
async fn object_create_instance_var(
    context: &mut Context,
    var: params::Var,
    object_root: params::ObjectRootLabel,
    object_type_label: params::Label,
) {
    let object = object_create_instance_impl(context, object_type_label).unwrap();
    object_root.assert(&object.type_());
    context.objects.insert(var.name, Some(ObjectWithKey::new(object)));
}

#[apply(generic_step)]
#[step(expr = r"{var} = {object_root_label}\({type_label}\) create new instance with key\({type_label}\): {value}")]
async fn object_create_instance_with_key_var(
    context: &mut Context,
    var: params::Var,
    object_root: params::ObjectRootLabel,
    object_type_label: params::Label,
    key_type_label: params::Label,
    value: params::Value,
) {
    let object = object_create_instance_impl(context, object_type_label).unwrap();
    object_root.assert(&object.type_());
    let key = attribute_put_instance_with_value_impl(context, key_type_label, value).unwrap();
    object_set_has_impl(context, &object, &key).unwrap();
    context.objects.insert(var.name, Some(ObjectWithKey::new_with_key(object, key)));
}

#[apply(generic_step)]
#[step(expr = r"delete {object_root_label}: {var}")]
async fn delete_object(context: &mut Context, object_root: params::ObjectRootLabel, var: params::Var) {
    let object = context.objects[&var.name].as_ref().unwrap().object.clone();
    object_root.assert(&object.type_());
    with_write_tx!(context, |tx| { object.delete(&mut tx.snapshot, &tx.thing_manager).unwrap() })
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} is deleted: {boolean}")]
async fn object_is_deleted(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    var: params::Var,
    is_deleted: params::Boolean,
) {
    let object = &context.objects[&var.name].as_ref().unwrap().object;
    object_root.assert(&object.type_());
    let object_type = object.type_();
    let objects =
        with_read_tx!(context, |tx| { tx.thing_manager.get_objects_in(&tx.snapshot, object_type).collect_cloned() });
    check_boolean!(is_deleted, !objects.contains(object));
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} has type: {type_label}")]
async fn object_has_type(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    var: params::Var,
    type_label: params::Label,
) {
    let object_type = context.objects[&var.name].as_ref().unwrap().object.type_();
    object_root.assert(&object_type);
    with_read_tx!(context, |tx| {
        assert_eq!(object_type.get_label(&tx.snapshot, &tx.type_manager).unwrap(), type_label.into_typedb())
    });
}

#[apply(generic_step)]
#[step(expr = r"{var} = {object_root_label}\({type_label}\) get instance with key\({type_label}\): {value}")]
async fn object_get_instance_with_value(
    context: &mut Context,
    var: params::Var,
    object_root: params::ObjectRootLabel,
    object_type_label: params::Label,
    key_type_label: params::Label,
    value: params::Value,
) {
    let Some(key) = get_attribute_by_value(context, key_type_label, value).unwrap() else {
        // no key - no object
        context.objects.insert(var.name, None);
        return;
    };

    let owner = with_read_tx!(context, |tx| {
        let object_type =
            tx.type_manager.get_object_type(&tx.snapshot, &object_type_label.into_typedb()).unwrap().unwrap();
        object_root.assert(&object_type);
        let mut owners = key.get_owners_by_type(&tx.snapshot, &tx.thing_manager, object_type);
        let owner = owners.next().transpose().unwrap().map(|(owner, count)| {
            assert_eq!(count, 1, "found {count} keys owned by the same object, expected 1");
            owner.into_owned()
        });
        assert!(owners.next().is_none(), "multiple objects found with key {:?}", key);
        owner
    });
    context.objects.insert(var.name, owner.map(|owner| ObjectWithKey::new_with_key(owner, key)));
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label}\({type_label}\) get instances is empty")]
async fn object_instances_is_empty(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    type_label: params::Label,
) {
    with_read_tx!(context, |tx| {
        let object_type = tx.type_manager.get_object_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        object_root.assert(&object_type);
        assert_matches!(tx.thing_manager.get_objects_in(&tx.snapshot, object_type).next(), None);
    });
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label}\({type_label}\) get instances {contains_or_doesnt}: {var}")]
async fn object_instances_contain(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    type_label: params::Label,
    containment: params::ContainsOrDoesnt,
    var: params::Var,
) {
    let object = &context.objects.get(&var.name).expect("no variable {} in context.").as_ref().unwrap().object;
    object_root.assert(&object.type_());
    with_read_tx!(context, |tx| {
        let object_type = tx.type_manager.get_object_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let actuals = tx.thing_manager.get_objects_in(&tx.snapshot, object_type).collect_cloned();
        containment.check(std::slice::from_ref(object), &actuals);
    });
}

#[apply(generic_step)]
#[step(expr = r"attribute {var} get owners {contains_or_doesnt}: {var}")]
async fn attribute_owners_contains(
    context: &mut Context,
    attribute_var: params::Var,
    contains_or_doesnt: params::ContainsOrDoesnt,
    owner_var: params::Var,
) {
    // FIXME Object owner could be relation
    let object = context.objects[&owner_var.name].as_ref().unwrap().object.to_owned();
    let attribute = context.attributes[&attribute_var.name].as_ref().unwrap();
    let actuals = with_read_tx!(context, |tx| {
        attribute
            .get_owners(&tx.snapshot, &tx.thing_manager)
            .map_static(|res| {
                let (attribute, _count) = res.unwrap();
                attribute.into_owned()
            })
            .collect::<Vec<_>>()
    });
    contains_or_doesnt.check(std::slice::from_ref(&object), &actuals)
}
