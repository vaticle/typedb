/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use concept::type_::{
    Ordering, OwnerAPI, PlayerAPI, TypeAPI,
    annotation,
    plays::PlaysAnnotation,
};

use cucumber::gherkin::Step;
use itertools::Itertools;
use macro_rules_attribute::apply;

use super::thing_type::get_as_object_type;
use crate::{
    generic_step, params,
    params::{Annotation, AnnotationCategory, ContainsOrDoesnt, IsEmptyOrNot, Label, MayError, RootLabel},
    transaction_context::{with_read_tx, with_schema_tx},
    util, Context,
};

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) set plays: {type_label}{may_error}")]
pub async fn set_plays(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    may_error: MayError,
) {
    let object_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_schema_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let res = object_type.set_plays(&mut tx.snapshot, &tx.type_manager, role_type);
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) unset plays: {type_label}{may_error}")]
pub async fn unset_plays(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    may_error: MayError,
) {
    let object_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_schema_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let res = object_type.delete_plays(&mut tx.snapshot, &tx.type_manager, role_type);
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get plays {contains_or_doesnt}:")]
pub async fn get_plays_contain(
    context: &mut Context,
    step: &Step,
    root_label: RootLabel,
    type_label: Label,
    contains: ContainsOrDoesnt,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    let object_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let actual_labels = object_type
            .get_plays(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|(_role, plays)| {
                plays.role().get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
            })
            .collect_vec();
        contains.check(&expected_labels, &actual_labels);
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get declared plays {contains_or_doesnt}:")]
pub async fn get_declared_plays_contain(
    context: &mut Context,
    step: &Step,
    root_label: RootLabel,
    type_label: Label,
    contains: ContainsOrDoesnt,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    let object_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let actual_labels = object_type
            .get_plays_declared(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|plays| {
                plays.role().get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
            })
            .collect_vec();
        contains.check(&expected_labels, &actual_labels);
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get plays {is_empty_or_not}")]
pub async fn get_plays_is_empty(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    is_empty_or_not: IsEmptyOrNot,
) {
    let object_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let actual_is_empty = object_type
            .get_plays(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .is_empty();
        is_empty_or_not.check(actual_is_empty);
    });
}

#[apply(generic_step)]
#[step(
    expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) set override: {type_label}{may_error}"
)]
pub async fn get_plays_set_override(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    overridden_role_label: Label,
    may_error: MayError,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_schema_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();

        let player_supertype = player_type.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
        let overridden_role_type =
            tx.type_manager.get_role_type(&tx.snapshot, &overridden_role_label.into_typedb()).unwrap().unwrap();
        let overridden_plays_opt =
            player_supertype.get_plays_role_transitive(&tx.snapshot, &tx.type_manager, overridden_role_type).unwrap();
        if let Some(overridden_plays) = overridden_plays_opt.as_ref() {
            let res = plays.set_override(&mut tx.snapshot, &tx.type_manager, overridden_plays_opt.unwrap());
            may_error.check(&res);
        } else {
            assert!(may_error.expects_error());
        }
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) unset override{may_error}")]
pub async fn get_plays_unset_override(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    may_error: MayError,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_schema_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let res = plays.unset_override(&mut tx.snapshot, &tx.type_manager);
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get plays overridden\\({type_label}\\) {exists_or_doesnt}")]
pub async fn get_plays_overridden_exists(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    exists: params::ExistsOrDoesnt,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_schema_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let plays_override_opt = plays.get_override(&tx.snapshot, &tx.type_manager).unwrap();
        exists.check(&plays_override_opt, &format!("no plays override for {} of {}", role_label.into_typedb(), type_label.into_typedb()));
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get plays overridden\\({type_label}\\) get label: {type_label}")]
pub async fn get_plays_overridden_get_label(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    expected_overridden: Label,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let actual_overridden_opt = plays.get_override(&tx.snapshot, &tx.type_manager).unwrap();
        let actual_overridden = actual_overridden_opt.as_ref().unwrap();
        let actual_overridden_label = actual_overridden
            .role()
            .get_label(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .scoped_name()
            .as_str()
            .to_owned();

        assert_eq!(expected_overridden.into_typedb().scoped_name().as_str().to_owned(), actual_overridden_label);
    });
}

#[apply(generic_step)]
#[step(
    expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) set annotation: {annotation}{may_error}"
)]
pub async fn get_plays_set_annotation(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    annotation: Annotation,
    may_error: MayError,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_schema_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let res = plays.set_annotation(&mut tx.snapshot, &tx.type_manager, annotation.into_typedb().into());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(
    expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) unset annotation: {annotation_category}{may_error}"
)]
pub async fn get_plays_unset_annotation(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    annotation_category: AnnotationCategory,
    may_error: MayError,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_schema_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let res = plays.unset_annotation(&mut tx.snapshot, &tx.type_manager, annotation_category.into_typedb());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(
    expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) get annotations {contains_or_doesnt}: {annotation}"
)]
pub async fn get_plays_annotations_contains(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation: Annotation,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let actual_contains = plays
            .get_annotations(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .contains_key(&annotation.into_typedb().into());
        assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
    });
}


#[apply(generic_step)]
#[step(
    expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) get annotation categories {contains_or_doesnt}: {annotation_category}"
)]
pub async fn get_plays_annotation_categories_contains(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation_category: AnnotationCategory,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let actual_contains = plays
            .get_annotations(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter().map(|(annotation, _)| <PlaysAnnotation as Into<annotation::Annotation>>::into(annotation.clone()).category())
            .contains(&annotation_category.into_typedb());
        assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
    });
}

#[apply(generic_step)]
#[step(
    expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) get declared annotations {contains_or_doesnt}: {annotation}"
)]
pub async fn get_plays_declared_annotations_contains(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation: Annotation,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let actual_contains = plays
            .get_annotations_declared(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .contains(&annotation.into_typedb().into());
        assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) get annotations {is_empty_or_not}")]
pub async fn get_owns_annotations_is_empty(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    is_empty_or_not: IsEmptyOrNot,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let actual_is_empty = plays
            .get_annotations(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .is_empty();
        is_empty_or_not.check(actual_is_empty);
    });
}

#[apply(generic_step)]
#[step(expr = "{root_label}\\({type_label}\\) get plays\\({type_label}\\) get declared annotations {is_empty_or_not}")]
pub async fn get_owns_declared_annotations_is_empty(
    context: &mut Context,
    root_label: RootLabel,
    type_label: Label,
    role_label: Label,
    is_empty_or_not: IsEmptyOrNot,
) {
    let player_type = get_as_object_type(context, root_label.into_typedb(), &type_label);
    with_read_tx!(context, |tx| {
        let role_type = tx.type_manager.get_role_type(&tx.snapshot, &role_label.into_typedb()).unwrap().unwrap();
        let plays = player_type.get_plays_role(&tx.snapshot, &tx.type_manager, role_type).unwrap().unwrap();
        let actual_is_empty = plays
            .get_annotations_declared(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .is_empty();
        is_empty_or_not.check(actual_is_empty);
    });
}