/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use concept::type_::{object_type::ObjectType, TypeAPI};
use cucumber::gherkin::Step;
use itertools::Itertools;
use macro_rules_attribute::apply;

use crate::{
    generic_step, params,
    transaction_context::{with_read_tx, with_schema_tx},
    util, Context,
};

#[apply(generic_step)]
#[step(expr = "attribute\\({type_label}\\) set value type: {value_type}{may_error}")]
pub async fn attribute_type_set_value_type(
    context: &mut Context,
    type_label: params::Label,
    value_type: params::ValueType,
    may_error: params::MayError,
) {
    with_schema_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let parsed_value_type = value_type.into_typedb(&tx.type_manager, &tx.snapshot);
        let res = attribute_type.set_value_type(&mut tx.snapshot, &tx.type_manager, parsed_value_type);
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = "attribute\\({type_label}\\) unset value type{may_error}")]
pub async fn attribute_type_unset_value_type(
    context: &mut Context,
    type_label: params::Label,
    may_error: params::MayError,
) {
    with_schema_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let res = attribute_type.unset_value_type(&mut tx.snapshot, &tx.type_manager);
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = "attribute\\({type_label}\\) get value type: {value_type}")]
pub async fn attribute_type_get_value_type(
    context: &mut Context,
    type_label: params::Label,
    value_type: params::ValueType,
) {
    with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        assert_eq!(
            value_type.into_typedb(&tx.type_manager, &tx.snapshot),
            attribute_type.get_value_type(&tx.snapshot, &tx.type_manager).unwrap().unwrap()
        );
    });
}

#[apply(generic_step)]
#[step(expr = "attribute\\({type_label}\\) get value type is none")]
pub async fn attribute_type_get_value_type_is_null(
    context: &mut Context,
    type_label: params::Label,
) {
    with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        assert_eq!(
            None,
            attribute_type.get_value_type(&tx.snapshot, &tx.type_manager).unwrap()
        );
    });
}

#[apply(generic_step)]
#[step(expr = "attribute\\({type_label}\\) get owners {contains_or_doesnt}:")]
pub async fn get_owners_contain(
    context: &mut Context,
    type_label: params::Label,
    contains: params::ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();

        let mut actual_labels = Vec::new();
        attribute_type.get_owns(&tx.snapshot, &tx.type_manager).unwrap().iter().for_each(
            |(owner, _owns)| {
                let owner_label = match owner {
                    ObjectType::Entity(owner) => {
                        owner.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                    }
                    ObjectType::Relation(owner) => {
                        owner.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                    }
                };
                actual_labels.push(owner_label);
            },
        );
        contains.check(&expected_labels, &actual_labels);
    });
}

#[apply(generic_step)]
#[step(expr = "attribute\\({type_label}\\) get owners explicit {contains_or_doesnt}:")]
pub async fn get_declaring_owners_contain(
    context: &mut Context,
    type_label: params::Label,
    contains: params::ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        let attribute_type =
            tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();

        let mut actual_labels = Vec::new();
        attribute_type.get_owns_declared(&tx.snapshot, &tx.type_manager).unwrap().iter().for_each(|owns| {
            let owner_label = match owns.owner() {
                ObjectType::Entity(owner) => {
                    owner.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                }
                ObjectType::Relation(owner) => {
                    owner.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                }
            };
            actual_labels.push(owner_label);
        });
        contains.check(&expected_labels, &actual_labels);
    });
}

// #[apply(generic_step)]
// #[step(expr = "attribute\\({type_label}\\)) get owners, with annotations: {annotations}; contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
// #[apply(generic_step)]
// #[step(expr = "attribute\\({type_label}\\)) get owners, with annotations: {annotations}; do not contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
// #[apply(generic_step)]
// #[step(expr = "attribute\\({type_label}\\)) get owners explicit, with annotations: {annotations}; contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
//
// #[apply(generic_step)]
// #[step(expr = "attribute\\({type_label}\\)) get owners explicit, with annotations: {annotations}; do not contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
// #[apply(generic_step)]
// #[step(expr = "attribute\\({type_label}\\)) get owners contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
// #[apply(generic_step)]
// #[step(expr = "attribute\\({type_label}\\)) get owners do not contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
// #[apply(generic_step)]
// #[step(expr = "attribute\\({type_label}\\)) get owners explicit contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
// #[step(expr = "attribute\\({type_label}\\)) get owners explicit do not contain:")]
// pub async fn TODO(context: &mut Context, type_label: params::Label, ...) { todo!(); }
