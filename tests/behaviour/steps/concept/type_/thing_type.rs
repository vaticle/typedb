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

use crate::{generic_step, params::{Annotation, ContainsOrDoesnt, ExistsOrDoesnt, Label, MayError, RootLabel}, transaction_context::{with_read_tx, with_schema_tx, with_write_tx}, util, with_type, Context, params};
use crate::params::IsEmptyOrNot;

#[macro_export]
macro_rules! with_type {
    ($tx:ident, $kind:expr, $label:ident, $assign_to:ident, $block:block) => {
        use encoding::graph::type_::Kind;
        match $kind.into_typedb() {
            Kind::Attribute => {
                let $assign_to =
                    $tx.type_manager.get_attribute_type(&$tx.snapshot, &$label.into_typedb()).unwrap().unwrap();
                $block
            }
            Kind::Entity => {
                let $assign_to = $tx.type_manager.get_entity_type(&$tx.snapshot, &$label.into_typedb()).unwrap().unwrap();
                $block
            }
            Kind::Relation => {
                let $assign_to =
                    $tx.type_manager.get_relation_type(&$tx.snapshot, &$label.into_typedb()).unwrap().unwrap();
                $block
            }
            Kind::Role => unreachable!(),
        };
    };
}

pub(super) fn get_as_object_type(context: &mut Context, kind: Kind, label: &Label) -> ObjectType<'static> {
    with_read_tx!(context, |tx| {
        match kind {
            Kind::Entity => {
                let type_ = tx.type_manager.get_entity_type(&tx.snapshot, &label.into_typedb()).unwrap().unwrap();
                return ObjectType::Entity(type_);
            }
            Kind::Relation => {
                let type_ = tx.type_manager.get_relation_type(&tx.snapshot, &label.into_typedb()).unwrap().unwrap();
                return ObjectType::Relation(type_);
            }
            _ => unreachable!("Attribute type as ObjectType is deprecated."),
        };
    })
}

#[apply(generic_step)]
#[step(expr = "create {root_label} type: {type_label}{may_error}")]
pub async fn type_create(context: &mut Context, root_label: RootLabel, type_label: Label, may_error: MayError) {
    with_schema_tx!(context, |tx| {
        match root_label.into_typedb() {
            Kind::Entity => {
                may_error.check(&tx.type_manager.create_entity_type(&mut tx.snapshot, &type_label.into_typedb(), false));
            }
            Kind::Relation => {
                may_error.check(&tx.type_manager.create_relation_type(&mut tx.snapshot, &type_label.into_typedb(), false));
            }
            Kind::Attribute => {
                may_error.check(&tx.type_manager.create_attribute_type(&mut tx.snapshot, &type_label.into_typedb(), false));
            }
            Kind::Role => unreachable!(),
        }
    });
}

#[apply(generic_step)]
#[step(expr = "delete {root_label} type: {type_label}{may_error}")]
pub async fn type_delete(context: &mut Context, root_label: RootLabel, type_label: Label, may_error: MayError) {
    with_schema_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let res = type_.delete(&mut tx.snapshot, &tx.type_manager);
            may_error.check(&res);
        });
    });
}

//
#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) {exists_or_doesnt}")]
pub async fn type_exists(context: &mut Context, root_label: RootLabel, type_label: Label, exists: ExistsOrDoesnt) {
    with_read_tx!(context, |tx| {
        match root_label.into_typedb() {
            Kind::Attribute => {
                let type_ = tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap();
                exists.check(&type_, &format!("type {}", type_label.into_typedb()));
            }
            Kind::Entity => {
                let type_ = tx.type_manager.get_entity_type(&tx.snapshot, &type_label.into_typedb()).unwrap();
                exists.check(&type_, &format!("type {}", type_label.into_typedb()));
            }
            Kind::Relation => {
                let type_ = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap();
                exists.check(&type_, &format!("type {}", type_label.into_typedb()));
            }
            Kind::Role => {
                let type_ = tx.type_manager.get_role_type(&tx.snapshot, &type_label.into_typedb()).unwrap();
                exists.check(&type_, &format!("type {}", type_label.into_typedb()));
            }
        };
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) set label: {type_label}")]
pub async fn type_set_label(context: &mut Context, root_label: RootLabel, type_label: Label, to_label: Label) {
    with_schema_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            type_.set_label(&mut tx.snapshot, &tx.type_manager, &to_label.into_typedb()).unwrap()
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get name: {type_label}")]
pub async fn type_get_name(context: &mut Context, root_label: RootLabel, type_label: Label, expected: Label) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let actual_label = type_.get_label(&tx.snapshot, &tx.type_manager);
            assert_eq!(expected.into_typedb().name(), actual_label.unwrap().name());
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get label: {type_label}")]
pub async fn type_get_label(context: &mut Context, root_label: RootLabel, type_label: Label, expected: Label) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let actual_label = type_.get_label(&tx.snapshot, &tx.type_manager);
            assert_eq!(expected.into_typedb().scoped_name(), actual_label.unwrap().scoped_name());
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) set annotation: {annotation}{may_error}")]
pub async fn type_set_annotation(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    annotation: Annotation,
    may_error: MayError,
) {
    with_write_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let res = type_.set_annotation(&mut tx.snapshot, &tx.type_manager, annotation.into_typedb().into());
            may_error.check(&res);
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) unset annotation: {annotation}{may_error}")]
pub async fn type_unset_annotation(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    annotation: Annotation,
    may_error: MayError,
) {
    with_write_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let res = type_.unset_annotation(&mut tx.snapshot, &tx.type_manager, annotation.into_typedb().into());
            may_error.check(&res);
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get annotations {contains_or_doesnt}: {annotation}")]
pub async fn type_annotations_contain(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation: Annotation,
) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let actual_contains = type_
                .get_annotations(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .contains_key(&annotation.into_typedb().into());
            assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get declared annotations {contains_or_doesnt}: {annotation}")]
pub async fn type_declared_annotations_contain(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation: Annotation,
) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let actual_contains = type_
                .get_annotations_declared(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .contains(&annotation.into_typedb().into());
            assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get annotations {is_empty_or_not}")]
pub async fn type_annotations_is_empty(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    is_empty_or_not: IsEmptyOrNot,
) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let actual_is_empty = type_
                .get_annotations(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .is_empty();
            is_empty_or_not.check(actual_is_empty);
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get declared annotations {is_empty_or_not}")]
pub async fn type_declared_annotations_is_empty(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    is_empty_or_not: IsEmptyOrNot,
) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let actual_is_empty = type_
                .get_annotations_declared(&tx.snapshot, &tx.type_manager)
                .unwrap().is_empty();
            is_empty_or_not.check(actual_is_empty);
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) set supertype: {type_label}{may_error}")]
pub async fn type_set_supertype(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    supertype_label: Label,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        match root_label.into_typedb() {
            Kind::Attribute => {
                let thistype =
                    tx.type_manager.get_attribute_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
                let supertype =
                    tx.type_manager.get_attribute_type(&tx.snapshot, &supertype_label.into_typedb()).unwrap().unwrap();
                let res = thistype.set_supertype(&mut tx.snapshot, &tx.type_manager, supertype);
                may_error.check(&res);
            }
            Kind::Entity => {
                let thistype = tx.type_manager.get_entity_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
                let supertype =
                    tx.type_manager.get_entity_type(&tx.snapshot, &supertype_label.into_typedb()).unwrap().unwrap();
                let res = thistype.set_supertype(&mut tx.snapshot, &tx.type_manager, supertype);
                may_error.check(&res);
            }
            Kind::Relation => {
                let thistype =
                    tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
                let supertype =
                    tx.type_manager.get_relation_type(&tx.snapshot, &supertype_label.into_typedb()).unwrap().unwrap();
                let res = thistype.set_supertype(&mut tx.snapshot, &tx.type_manager, supertype);
                may_error.check(&res);
            }
            Kind::Role => {
                let thistype = tx.type_manager.get_role_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
                let supertype =
                    tx.type_manager.get_role_type(&tx.snapshot, &supertype_label.into_typedb()).unwrap().unwrap();
                let res = thistype.set_supertype(&mut tx.snapshot, &tx.type_manager, supertype);
                may_error.check(&res);
            }
        };
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get supertype: {type_label}")]
pub async fn type_get_supertype(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    supertype_label: Label,
) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let supertype = type_.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
            assert_eq!(
                supertype_label.into_typedb().scoped_name(),
                supertype.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name()
            )
        });
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get supertypes {contains_or_doesnt}:")]
pub async fn get_supertypes_contain(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    contains: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let supertype_labels = type_
                .get_supertypes(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .iter()
                .map(|supertype| {
                    supertype.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                })
                .collect_vec();
            contains.check(&expected_labels, &supertype_labels);
        });
    });
}

// TODO: is_empty_or_not
#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get supertypes is empty")]
pub async fn get_supertypes_is_empty(context: &mut Context, root_label: RootLabel, type_label: Label, step: &Step) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            assert!(type_.get_supertypes(&tx.snapshot, &tx.type_manager).unwrap().is_empty());
        });
    });
}

// TODO: transitive / non-transitive separate checks?
#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get subtypes {contains_or_doesnt}:")]
pub async fn get_subtypes_contain(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    contains: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            let subtype_labels = type_
                .get_subtypes_transitive(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .iter()
                .map(|subtype| {
                    subtype.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                })
                .collect_vec();
            contains.check(&expected_labels, &subtype_labels);
        });
    });
}

// TODO: is_empty_or_not
#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get subtypes is empty")]
pub async fn get_subtypes_is_empty(context: &mut Context, root_label: RootLabel, type_label: Label, step: &Step) {
    with_read_tx!(context, |tx| {
        with_type!(tx, root_label, type_label, type_, {
            assert!(type_.get_subtypes_transitive(&tx.snapshot, &tx.type_manager).unwrap().is_empty());
        });
    });
}
