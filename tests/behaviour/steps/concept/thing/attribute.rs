/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use concept::{
    error::{ConceptReadError, ConceptWriteError},
    thing::{attribute::Attribute, ThingAPI},
    type_::TypeAPI,
};
use macro_rules_attribute::apply;

use crate::{
    generic_step,
    params::{self, check_boolean},
    transaction_context::{with_read_tx, with_write_tx},
    Context,
};

pub fn attribute_put_instance_with_value_impl(
    context: &mut Context,
    type_label: params::Label,
    value: params::Value,
) -> Result<Attribute<'static>, ConceptWriteError> {
    with_write_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let value = value.into_typedb(attribute_type.get_value_type(&tx.snapshot, &tx.type_manager).unwrap().unwrap());
        tx.thing_manager.create_attribute(&mut tx.snapshot, attribute_type, value)
    })
}

#[apply(generic_step)]
#[step(expr = r"attribute\({type_label}\) put instance with value: {value}{may_error}")]
async fn attribute_put_instance_with_value(
    context: &mut Context,
    type_label: params::Label,
    value: params::Value,
    may_error: params::MayError,
) {
    may_error.check(&attribute_put_instance_with_value_impl(context, type_label, value));
}

#[apply(generic_step)]
#[step(expr = r"{var} = attribute\({type_label}\) put instance with value: {value}")]
async fn attribute_put_instance_with_value_var(
    context: &mut Context,
    var: params::Var,
    type_label: params::Label,
    value: params::Value,
) {
    let attribute = attribute_put_instance_with_value_impl(context, type_label, value).unwrap();
    context.attributes.insert(var.name, Some(attribute));
}

#[apply(generic_step)]
#[step(expr = r"attribute {var} has type: {type_label}")]
async fn attribute_has_type(context: &mut Context, var: params::Var, type_label: params::Label) {
    let attribute_type = context.attributes[&var.name].as_ref().unwrap().type_();
    with_read_tx!(context, |tx| {
        assert_eq!(attribute_type.get_label(&tx.snapshot, &tx.type_manager).unwrap(), type_label.into_typedb())
    });
}

#[apply(generic_step)]
#[step(expr = r"attribute {var} has value type: {value_type}")]
async fn attribute_has_value_type(context: &mut Context, var: params::Var, value_type: params::ValueType) {
    let attribute_type = context.attributes[&var.name].as_ref().unwrap().type_();
    with_read_tx!(context, |tx| {
        assert_eq!(
            attribute_type.get_value_type(&tx.snapshot, &tx.type_manager).unwrap().unwrap(),
            value_type.into_typedb()
        );
    });
}

#[apply(generic_step)]
#[step(expr = r"attribute {var} has value: {value}")]
async fn attribute_has_value(context: &mut Context, var: params::Var, value: params::Value) {
    let attribute = context.attributes.get_mut(&var.name).unwrap().as_mut().unwrap();
    let attribute_type = attribute.type_();
    with_read_tx!(context, |tx| {
        let value = value.into_typedb(attribute_type.get_value_type(&tx.snapshot, &tx.type_manager).unwrap().unwrap());
        assert_eq!(attribute.get_value(&tx.snapshot, &tx.thing_manager).unwrap(), value);
    });
}

#[apply(generic_step)]
#[step(expr = r"attribute {var}[{int}] is {var}")]
async fn attribute_list_at_index_is(
    context: &mut Context,
    list_var: params::Var,
    index: usize,
    attribute_var: params::Var,
) {
    let list_item = &context.attribute_lists[&list_var.name][index];
    let attribute = context.attributes[&attribute_var.name].as_ref().unwrap();
    assert_eq!(list_item, attribute);
}

pub fn get_attribute_by_value(
    context: &mut Context,
    type_label: params::Label,
    value: params::Value,
) -> Result<Option<Attribute<'static>>, ConceptReadError> {
    with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let value = value.into_typedb(attribute_type.get_value_type(&tx.snapshot, &tx.type_manager).unwrap().unwrap());
        tx.thing_manager.get_attribute_with_value(&tx.snapshot, attribute_type, value)
    })
}

#[apply(generic_step)]
#[step(expr = r"{var} = attribute\({type_label}\) get instance with value: {value}")]
async fn attribute_get_instance_with_value(
    context: &mut Context,
    var: params::Var,
    type_label: params::Label,
    value: params::Value,
) {
    let att = get_attribute_by_value(context, type_label, value).unwrap();
    context.attributes.insert(var.name, att);
}

#[apply(generic_step)]
#[step(expr = r"delete attribute: {var}")]
async fn delete_attribute(context: &mut Context, var: params::Var) {
    with_write_tx!(context, |tx| {
        context.attributes[&var.name].clone().unwrap().delete(&mut tx.snapshot, &tx.thing_manager).unwrap()
    })
}

#[apply(generic_step)]
#[step(expr = r"attribute {var} is deleted: {boolean}")]
async fn attribute_is_deleted(context: &mut Context, var: params::Var, is_deleted: params::Boolean) {
    let attribute = context.attributes.get_mut(&var.name).unwrap().as_mut().unwrap();
    let attribute_type = attribute.type_();
    let get = with_read_tx!(context, |tx| {
        let value = attribute.get_value(&tx.snapshot, &tx.thing_manager).unwrap();
        tx.thing_manager.get_attribute_with_value(&tx.snapshot, attribute_type, value).unwrap()
    });
    check_boolean!(is_deleted, get.is_none());
}

#[apply(generic_step)]
#[step(expr = r"attribute\({type_label}\) get instances {contains_or_doesnt}: {var}")]
async fn attribute_instances_contain(
    context: &mut Context,
    type_label: params::Label,
    containment: params::ContainsOrDoesnt,
    var: params::Var,
) {
    let attribute = context.attributes.get(&var.name).expect("no variable {} in context.").as_ref().unwrap();
    let actuals = with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        tx.thing_manager.get_attributes_in(&tx.snapshot, attribute_type).unwrap().collect_cloned()
    });
    containment.check(std::slice::from_ref(attribute), &actuals);
}
