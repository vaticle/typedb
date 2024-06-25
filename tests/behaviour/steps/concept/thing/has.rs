/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use concept::{
    error::ConceptWriteError,
    thing::{
        attribute::Attribute,
        object::{Object, ObjectAPI},
    },
    type_::{attribute_type::AttributeType, OwnerAPI},
};
use itertools::Itertools;
use lending_iterator::LendingIterator;
use macro_rules_attribute::apply;

use crate::{
    generic_step, params,
    transaction_context::{with_read_tx, with_write_tx},
    Context,
};

pub(super) fn object_set_has_impl(
    context: &mut Context,
    object: &Object<'static>,
    attribute: &Attribute<'static>,
) -> Result<(), ConceptWriteError> {
    with_write_tx!(context, |tx| object.set_has_unordered(
        &mut tx.snapshot,
        &tx.thing_manager,
        attribute.as_reference()
    ))
}

pub(super) fn object_set_has_ordered_impl(
    context: &mut Context,
    object: &Object<'static>,
    attribute_type: AttributeType<'static>,
    attributes: Vec<Attribute<'static>>,
) -> Result<(), ConceptWriteError> {
    with_write_tx!(context, |tx| object.set_has_ordered(
        &mut tx.snapshot,
        &tx.thing_manager,
        attribute_type,
        attributes
    ))
}

fn object_unset_has_impl(
    context: &mut Context,
    object: &Object<'static>,
    key: &Attribute<'static>,
) -> Result<(), ConceptWriteError> {
    with_write_tx!(context, |tx| object.unset_has_unordered(&mut tx.snapshot, &tx.thing_manager, key.as_reference()))
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} set has: {var}{may_error}")]
async fn object_set_has(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    object_var: params::Var,
    attribute_var: params::Var,
    may_error: params::MayError,
) {
    let object = context.objects[&object_var.name].as_ref().unwrap().object.to_owned();
    object_root.assert(&object.type_());
    let attribute = context.attributes[&attribute_var.name].as_ref().unwrap().to_owned();
    may_error.check(&object_set_has_impl(context, &object, &attribute));
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} set has\({type_label}[]\): {vars}{may_error}")]
async fn object_set_has_list(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    object_var: params::Var,
    attribute_type_label: params::Label,
    attribute_vars: params::Vars,
    may_error: params::MayError,
) {
    let object = context.objects[&object_var.name].as_ref().unwrap().object.to_owned();
    object_root.assert(&object.type_());
    let attribute_type = with_read_tx!(context, |tx| {
        tx.type_manager.get_attribute_type(&tx.snapshot, &attribute_type_label.into_typedb()).unwrap().unwrap()
    });
    let attributes = attribute_vars
        .names
        .into_iter()
        .map(|attr_name| context.attributes[&attr_name].as_ref().unwrap().to_owned())
        .collect_vec();
    may_error.check(&object_set_has_ordered_impl(context, &object, attribute_type, attributes));
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} unset has: {var}")]
async fn object_unset_has(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    object_var: params::Var,
    attribute_var: params::Var,
) {
    let object = context.objects[&object_var.name].as_ref().unwrap().object.to_owned();
    object_root.assert(&object.type_());
    let attribute = context.attributes[&attribute_var.name].as_ref().unwrap().to_owned();
    object_unset_has_impl(context, &object, &attribute).unwrap();
}

#[apply(generic_step)]
#[step(expr = r"{var} = {object_root_label} {var} get has\({type_label}[]\)")]
async fn object_get_has_list(
    context: &mut Context,
    attribute_var: params::Var,
    object_root: params::ObjectRootLabel,
    object_var: params::Var,
    attribute_type_label: params::Label,
) {
    let object = context.objects[&object_var.name].as_ref().unwrap().object.to_owned();
    object_root.assert(&object.type_());
    let attributes = with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &attribute_type_label.into_typedb()).unwrap().unwrap();
        object
            .get_has_ordered(&tx.snapshot, &tx.thing_manager, attribute_type)
            .unwrap()
            .into_iter()
            .map(|attr| attr.into_owned())
            .collect()
    });
    context.attribute_lists.insert(attribute_var.name, attributes);
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} get has {contains_or_doesnt}: {var}")]
async fn object_get_has(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    object_var: params::Var,
    contains_or_doesnt: params::ContainsOrDoesnt,
    attribute_var: params::Var,
) {
    let object = context.objects[&object_var.name].as_ref().unwrap().object.to_owned();
    object_root.assert(&object.type_());
    let attribute = context.attributes[&attribute_var.name].as_ref().unwrap();
    let actuals = with_read_tx!(context, |tx| {
        object
            .get_has_unordered(&tx.snapshot, &tx.thing_manager)
            .map_static(|res| {
                let (attribute, _count) = res.unwrap();
                attribute.into_owned()
            })
            .collect::<Vec<_>>()
    });
    contains_or_doesnt.check(std::slice::from_ref(attribute), &actuals);
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} get has\({type_label}\) {contains_or_doesnt}: {var}")]
async fn object_get_has_type(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    object_var: params::Var,
    attribute_type_label: params::Label,
    contains_or_doesnt: params::ContainsOrDoesnt,
    attribute_var: params::Var,
) {
    let object = context.objects[&object_var.name].as_ref().unwrap().object.to_owned();
    object_root.assert(&object.type_());
    let attribute = context.attributes[&attribute_var.name].as_ref().unwrap();
    let actuals = with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &attribute_type_label.into_typedb()).unwrap().unwrap();
        object
            .get_has_type(&tx.snapshot, &tx.thing_manager, attribute_type)
            .unwrap()
            .map_static(|res| {
                let (attribute, _count) = res.unwrap();
                attribute.into_owned()
            })
            .collect::<Vec<_>>()
    });
    contains_or_doesnt.check(std::slice::from_ref(attribute), &actuals);
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} get has with annotations: {annotations}; {contains_or_doesnt}: {var}")]
async fn object_get_has_with_annotations(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    object_var: params::Var,
    annotations: params::Annotations,
    contains_or_doesnt: params::ContainsOrDoesnt,
    attribute_var: params::Var,
) {
    let object = context.objects[&object_var.name].as_ref().unwrap().object.to_owned();
    object_root.assert(&object.type_());
    let attribute = context.attributes[&attribute_var.name].as_ref().unwrap();
    let annotations = annotations.into_typedb().into_iter().map(|anno| anno.into()).collect_vec();
    let actuals = with_read_tx!(context, |tx| {
        let attribute_types = object
            .type_()
            .get_owns_declared(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .into_iter()
            .filter(|owns| {
                annotations.iter().all(|anno| {
                    owns.get_annotations(&tx.snapshot, &tx.type_manager).unwrap().contains_key(anno)
                })
            })
            .map(|owns| owns.attribute())
            .collect_vec();
        attribute_types
            .into_iter()
            .flat_map(|attribute_type| {
                object
                    .get_has_type(&tx.snapshot, &tx.thing_manager, attribute_type)
                    .unwrap()
                    .map_static(|res| {
                        let (attribute, _count) = res.unwrap();
                        attribute.into_owned()
                    })
                    .collect::<Vec<_>>()
            })
            .collect_vec()
    });
    contains_or_doesnt.check(std::slice::from_ref(attribute), &actuals);
}
