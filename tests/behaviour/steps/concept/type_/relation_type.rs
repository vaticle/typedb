/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use concept::type_::{object_type::ObjectType, Ordering, TypeAPI};
use cucumber::gherkin::Step;
use itertools::Itertools;
use macro_rules_attribute::apply;

use crate::{
    generic_step, params,
    transaction_context::{with_read_tx, with_schema_tx},
    util, Context,
};
use crate::params::MayError;

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) create role: {type_label}{may_error}")]
pub async fn relation_type_create_role(
    context: &mut Context,
    type_label: params::Label,
    role_label: params::Label,
    may_error: params::MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation_type = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let res = relation_type.create_relates(
            &mut tx.snapshot,
            &tx.type_manager,
            role_label.to_typedb().name().as_str(),
            Ordering::Unordered,
        );
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) create role: {type_label}[]{may_error}")]
pub async fn relation_type_create_ordered_role(
    context: &mut Context,
    type_label: params::Label,
    role_label: params::Label,
    may_error: params::MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation_type = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let res = relation_type.create_relates(
            &mut tx.snapshot,
            &tx.type_manager,
            role_label.to_typedb().name().as_str(),
            Ordering::Ordered,
        );
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\); set override: {type_label}{may_error}")]
pub async fn relation_type_override_role(
    context: &mut Context,
    type_label: params::Label,
    role_label: params::Label,
    overridden_label: params::Label,
    may_error: params::MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation_type = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let relates = relation_type
            .get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap();
        let relation_supertype = relation_type.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
        let overridden_relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation_supertype, overridden_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap();
        // TODO: Is it ok to just set supertype here?
        let res = relates.role().set_supertype(&mut tx.snapshot, &tx.type_manager, overridden_relates.role());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get roles {contains_or_doesnt}:")]
pub async fn get_roles_contain(
    context: &mut Context,
    type_label: params::Label,
    contains: params::ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels: Vec<String> = util::iter_table(step).map(|str| str.to_owned()).collect::<Vec<String>>();
    with_read_tx!(context, |tx| {
        let type_ = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let actual_labels = type_
            .get_relates_transitive(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|(_label, relates)| {
                relates.role().get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
            })
            .collect_vec();
        contains.check(&expected_labels, &actual_labels);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get declared roles {contains_or_doesnt}:")]
pub async fn get_declared_roles_contain(
    context: &mut Context,
    type_label: params::Label,
    contains: params::ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels: Vec<String> = util::iter_table(step).map(|str| str.to_owned()).collect::<Vec<String>>();
    with_read_tx!(context, |tx| {
        let type_ = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let actual_labels = type_
            .get_relates(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|relates| {
                relates.role().get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
            })
            .collect_vec();
        contains.check(&expected_labels, &actual_labels);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) {exists_or_doesnt}")]
pub async fn get_role_exists(
    context: &mut Context,
    type_label: params::Label,
    role_label: params::Label,
    exists: params::ExistsOrDoesnt,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let role_opt =
            relation.get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name.as_str()).unwrap();
        exists.check(&role_opt, &format!("role {}:{}", type_label.to_typedb(), role_label.to_typedb()));
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get label: {type_label}")]
pub async fn get_role_label(
    context: &mut Context,
    type_label: params::Label,
    role_label: params::Label,
    expected_label: params::Label,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name.as_str())
            .unwrap()
            .unwrap()
            .role();
        assert_eq!(
            expected_label.to_typedb().scoped_name.as_str(),
            role.get_label(&tx.snapshot, &tx.type_manager).unwrap().name.as_str()
        );
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) delete role: {type_label}{may_error}")]
pub async fn delete_role(
    context: &mut Context,
    type_label: params::Label,
    role_label: params::Label,
    may_error: params::MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.to_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name.as_str())
            .unwrap()
            .unwrap()
            .role();
        let res = role.delete(&mut tx.snapshot, &tx.type_manager);
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get supertype: {type_label}")]
pub async fn type_get_supertype(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    expected_superrole_label: params::Label,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let superrole = role.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
        assert_eq!(
            expected_superrole_label.to_typedb().scoped_name(),
            superrole.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name() // TODO: Why is the root role named y:role?
        )
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get supertypes {contains_or_doesnt}:")]
pub async fn get_supertypes_contain(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    contains: params::ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let supertype_labels = role
            .get_supertypes(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|supertype| {
                supertype.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
            })
            .collect_vec();
        contains.check(&expected_labels, &supertype_labels);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get subtypes {contains_or_doesnt}:")]
pub async fn get_subtypes_contain(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    contains: params::ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let subtype_labels = role
            .get_subtypes_transitive(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|subtype| subtype.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned())
            .collect_vec();
        contains.check(&expected_labels, &subtype_labels);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get subtypes is empty")]
pub async fn get_subtypes_is_empty(context: &mut Context, relation_label: params::Label, role_label: params::Label) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let subtype_labels = role
            .get_subtypes_transitive(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|subtype| subtype.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned())
            .collect_vec();
        assert!(subtype_labels.is_empty(), "{:?} is not empty", subtype_labels);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) set name: {type_label}")]
pub async fn type_set_label(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    to_label: params::Label,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        role.set_name(&mut tx.snapshot, &tx.type_manager, to_label.to_typedb().name.as_str());
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get overridden role\({type_label}\) {exists_or_doesnt}")]
pub async fn get_overridden_role_exists(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    exists: params::ExistsOrDoesnt,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let superrole_opt = role.get_supertype(&tx.snapshot, &tx.type_manager).unwrap();
        exists.check(
            &superrole_opt,
            &format!("overridden role for {}:{}", relation_label.to_typedb(), role_label.to_typedb()),
        );
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get overridden role\({type_label}\) get label: {type_label}")]
pub async fn get_overridden_role_label(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    expected_label: params::Label,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let superrole = role.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
        println!(
            "{}, {}",
            expected_label.to_typedb().name().as_str(),
            superrole.get_label(&tx.snapshot, &tx.type_manager).unwrap().name().as_str()
        );
        assert_eq!(
            expected_label.to_typedb().name(),
            superrole.get_label(&tx.snapshot, &tx.type_manager).unwrap().name()
        )
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) set annotation: {annotation}{may_error}")]
pub async fn relation_role_set_annotation(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    annotation: params::Annotation,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let res = role.set_annotation(&mut tx.snapshot, &tx.type_manager, annotation.into_typedb().into());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) unset annotation: {annotation}{may_error}")]
pub async fn relation_role_unset_annotation(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    annotation: params::Annotation,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let res = role.unset_annotation(&mut tx.snapshot, &tx.type_manager, annotation.into_typedb().into());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get annotations {contains_or_doesnt}: {annotation}")]
pub async fn relation_role_annotations_contain(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    contains_or_doesnt: params::ContainsOrDoesnt,
    annotation: params::Annotation,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let actual_contains =
            role.get_annotations(&tx.snapshot, &tx.type_manager).unwrap().contains(&annotation.into_typedb().into());
        assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get players {contains_or_doesnt}:")]
pub async fn role_type_players_contain(
    context: &mut Context,
    relation_label: params::Label,
    role_label: params::Label,
    contains_or_doesnt: params::ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels: Vec<String> = util::iter_table(step).map(|str| str.to_owned()).collect::<Vec<String>>();
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.to_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let actual_labels = role
            .get_plays(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|plays| match plays.player() {
                ObjectType::Entity(entity_type) => {
                    entity_type.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                }
                ObjectType::Relation(relation_type) => {
                    relation_type.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
                }
            })
            .collect::<Vec<String>>();
        contains_or_doesnt.check(expected_labels.as_slice(), actual_labels.as_slice());
    });
}
