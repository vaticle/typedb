/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::ascii::escape_default;
use concept::type_::{object_type::ObjectType, PlayerAPI, TypeAPI};
use cucumber::gherkin::Step;
use encoding::graph::type_::Kind;
use itertools::Itertools;
use macro_rules_attribute::apply;

use crate::{
    generic_step,
    params::{Annotation, ContainsOrDoesnt, ExistsOrDoesnt, Label, MayError, RootLabel},
    transaction_context::{with_read_tx, with_schema_tx, with_write_tx},
    util, with_type, Context,
};
use crate::params::ValueType;

#[apply(generic_step)]
#[step(expr = "create struct type: {type_label}{may_error}")]
pub async fn struct_type_create(context: &mut Context, type_label: Label, may_error: MayError) {
    with_schema_tx!(context, |tx| {
        unreachable!("Not implemented")
        // may_error.check(&tx.type_manager.create_struct_type(&mut tx.snapshot, &type_label.to_typedb(), false));
    });
}

#[apply(generic_step)]
#[step(expr = "delete struct type: {type_label}{may_error}")]
pub async fn struct_type_delete(context: &mut Context, type_label: Label, may_error: MayError) {
    with_schema_tx!(context, |tx| {
        unreachable!("Not implemented")
    });
}

#[apply(generic_step)]
#[step(expr = "struct\\({type_label}\\) {exists_or_doesnt}")]
pub async fn struct_type_exists(context: &mut Context, type_label: Label, exists: ExistsOrDoesnt) {
    with_read_tx!(context, |tx| {
        unreachable!("Not implemented")
        // let type_ = tx.type_manager.get_struct_type(&tx.snapshot, &type_label.to_typedb()).unwrap();
        // exists.check(&type_, &format!("type {}", type_label.to_typedb()));
    });
}

// TODO: {value_type} should be {struct_or_value_type}
#[apply(generic_step)]
#[step(expr = "struct\\({type_label}\\) create field: {type_label}, with value type: {value_type}{may_error}")]
pub async fn struct_type_create_field_with_value_type(
    context: &mut Context,
    type_label: Label,
    field_label: Label,
    value_type: ValueType,
    may_error: MayError,
) {
    unreachable!("Not implemented")
}

// TODO: {value_type} should be {struct_or_value_type}
#[apply(generic_step)]
#[step(expr = "struct\\({type_label}\\) delete field: {type_label}{may_error}")]
pub async fn struct_type_delete_field(
    context: &mut Context,
    type_label: Label,
    field_label: Label,
    may_error: MayError,
) {
    unreachable!("Not implemented")
}

// TODO: {value_type} should be {struct_or_value_type}
#[apply(generic_step)]
#[step(expr = "struct\\({type_label}\\) get fields {contains_or_doesnt}: {type_label}")]
pub async fn struct_type_get_fields_contains_or_doesnt(
    context: &mut Context,
    type_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    field_label: Label,
) {
    unreachable!("Not implemented")
}
