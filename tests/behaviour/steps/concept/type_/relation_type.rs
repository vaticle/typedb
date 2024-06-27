/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use concept::type_::{
    object_type::ObjectType, TypeAPI, Ordering, annotation,
    relates::RelatesAnnotation,
    role_type::RoleTypeAnnotation,
};

use cucumber::gherkin::Step;
use itertools::Itertools;
use macro_rules_attribute::apply;

use crate::{
    generic_step, params,
    params::{IsEmptyOrNot, Label, RootLabel, MayError, ContainsOrDoesnt, ExistsOrDoesnt, Annotation, AnnotationCategory},
    transaction_context::{with_read_tx, with_schema_tx},
    util, Context,
};

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) create role: {type_label}{may_error}")]
pub async fn relation_type_create_role(
    context: &mut Context,
    type_label: Label,
    role_label: Label,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation_type = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let res = relation_type.create_relates(
            &mut tx.snapshot,
            &tx.type_manager,
            role_label.into_typedb().name().as_str(),
            Ordering::Unordered,
        );
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) create role: {type_label}[]{may_error}")]
pub async fn relation_type_create_ordered_role(
    context: &mut Context,
    type_label: Label,
    role_label: Label,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation_type = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let res = relation_type.create_relates(
            &mut tx.snapshot,
            &tx.type_manager,
            role_label.into_typedb().name().as_str(),
            Ordering::Ordered,
        );
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) set supertype: {type_label}{may_error}")]
pub async fn relation_role_set_supertype(
    context: &mut Context,
    type_label: Label,
    role_label: Label,
    supertype_label: Label,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation_type = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let relates = relation_type
            .get_relates_of_role(&tx.snapshot, &tx.type_manager, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();
        let relation_supertype = relation_type.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
        let overridden_relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation_supertype, supertype_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();
        // TODO: Is it ok to just set supertype here?
        let res = relates.role().set_supertype(&mut tx.snapshot, &tx.type_manager, overridden_relates.role());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get roles {contains_or_doesnt}:")]
pub async fn relation_roles_contain(
    context: &mut Context,
    type_label: Label,
    contains: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels: Vec<String> = util::iter_table(step).map(|str| str.to_owned()).collect::<Vec<String>>();
    with_read_tx!(context, |tx| {
        let relation_type = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let actual_labels = relation_type
            .get_relates(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|(_label, relates)| {
                relates.role().get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned()
            })
            .collect_vec();
        contains.check(&expected_labels, &actual_labels);
    });
}

// TODO: Add steps into .feature for declared checks!
#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get declared roles {contains_or_doesnt}:")]
pub async fn relation_declared_roles_contain(
    context: &mut Context,
    type_label: Label,
    contains: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels: Vec<String> = util::iter_table(step).map(|str| str.to_owned()).collect::<Vec<String>>();
    with_read_tx!(context, |tx| {
        let type_ = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let actual_labels = type_
            .get_relates_declared(&tx.snapshot, &tx.type_manager)
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
pub async fn relation_role_exists(
    context: &mut Context,
    type_label: Label,
    role_label: Label,
    exists: ExistsOrDoesnt,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let role_opt =
            relation.get_relates_of_role(&tx.snapshot, &tx.type_manager, role_label.into_typedb().name.as_str()).unwrap();
        exists.check(&role_opt, &format!("role {}:{}", type_label.into_typedb(), role_label.into_typedb()));
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get label: {type_label}")]
pub async fn relation_role_get_label(
    context: &mut Context,
    type_label: Label,
    role_label: Label,
    expected_label: Label,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_of_role(&tx.snapshot, &tx.type_manager, role_label.into_typedb().name.as_str())
            .unwrap()
            .unwrap()
            .role();
        assert_eq!(
            expected_label.into_typedb().scoped_name.as_str(),
            role.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name.as_str()
        );
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get name: {type_label}")]
pub async fn relation_role_get_name(
    context: &mut Context,
    type_label: Label,
    role_label: Label,
    expected_label: Label,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_of_role(&tx.snapshot, &tx.type_manager, role_label.into_typedb().name.as_str())
            .unwrap()
            .unwrap()
            .role();
        assert_eq!(
            expected_label.into_typedb().name.as_str(),
            role.get_label(&tx.snapshot, &tx.type_manager).unwrap().name.as_str()
        );
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) delete role: {type_label}{may_error}")]
pub async fn relation_type_delete_role(
    context: &mut Context,
    type_label: Label,
    role_label: Label,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &type_label.into_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_of_role(&tx.snapshot, &tx.type_manager, role_label.into_typedb().name.as_str())
            .unwrap()
            .unwrap()
            .role();
        let res = role.delete(&mut tx.snapshot, &tx.type_manager);
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get supertype: {type_label}")]
pub async fn relation_role_get_supertype(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    expected_superrole_label: Label,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let superrole = role.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
        assert_eq!(
            expected_superrole_label.into_typedb().scoped_name(),
            superrole.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name() // TODO: Why is the root role named y:role?
        )
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get supertypes {contains_or_doesnt}:")]
pub async fn relation_role_supertypes_contain(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    contains: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
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

// TODO: Make different transitive / non-transitive steps?
#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get subtypes {contains_or_doesnt}:")]
pub async fn relation_role_subtypes_contain(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    contains: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels = util::iter_table(step).map(|str| str.to_owned()).collect_vec();
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
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

// TODO: is_empty_or_not
#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get subtypes {is_empty_or_not}")]
pub async fn relation_role_subtypes_is_empty(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    is_empty_or_not: IsEmptyOrNot
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let subtype_labels = role
            .get_subtypes_transitive(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|subtype| subtype.get_label(&tx.snapshot, &tx.type_manager).unwrap().scoped_name().as_str().to_owned())
            .collect_vec();
        is_empty_or_not.check(subtype_labels.is_empty());
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) set name: {type_label}{may_error}")]
pub async fn relation_role_set_name(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    to_label: Label,
    may_error: MayError
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let res = role.set_name(&mut tx.snapshot, &tx.type_manager, to_label.into_typedb().name.as_str());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get overridden role\({type_label}\) {exists_or_doesnt}")]
pub async fn relation_get_overridden_role(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    exists: ExistsOrDoesnt,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let superrole_opt = role.get_supertype(&tx.snapshot, &tx.type_manager).unwrap();
        exists.check(
            &superrole_opt,
            &format!("overridden role for {}:{}", relation_label.into_typedb(), role_label.into_typedb()),
        );
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get overridden role\({type_label}\) get label: {type_label}")]
pub async fn relation_overridden_role_get_label(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    expected_label: Label,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let superrole = role.get_supertype(&tx.snapshot, &tx.type_manager).unwrap().unwrap();
        println!(
            "{}, {}",
            expected_label.into_typedb().name().as_str(),
            superrole.get_label(&tx.snapshot, &tx.type_manager).unwrap().name().as_str()
        );
        assert_eq!(
            expected_label.into_typedb().name(),
            superrole.get_label(&tx.snapshot, &tx.type_manager).unwrap().name()
        )
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) set annotation: {annotation}{may_error}")]
pub async fn relation_role_set_annotation(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    annotation: Annotation,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();

        let parsed_annotation = annotation.into_typedb();
        let res;
        match parsed_annotation {
            annotation::Annotation::Abstract(_) => {
                res = relates.role().set_annotation(&mut tx.snapshot, &tx.type_manager, parsed_annotation.into());
            },
            annotation::Annotation::Distinct(_) | annotation::Annotation::Cardinality(_) => {
                res = relates.set_annotation(&mut tx.snapshot, &tx.type_manager, parsed_annotation.into());
            },
            _ => {
                unimplemented!("Annotation {:?} is not supported by roles and relates", parsed_annotation);
            }
        }
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) unset annotation: {annotation_category}{may_error}")]
pub async fn relation_role_unset_annotation(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    annotation_category: AnnotationCategory,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();

        let parsed_annotation_category = annotation_category.into_typedb();
        let res;
        if RoleTypeAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            res = relates.role().unset_annotation(&mut tx.snapshot, &tx.type_manager, parsed_annotation_category);
        } else if RelatesAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            res = relates.unset_annotation(&mut tx.snapshot, &tx.type_manager, parsed_annotation_category);
        } else {
            unimplemented!("Annotation {:?} is not supported by roles and relates", parsed_annotation_category);
        }
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get annotations {contains_or_doesnt}: {annotation}")]
pub async fn relation_role_annotations_contain(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation: Annotation,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();

        let parsed_annotation = annotation.into_typedb();
        let parsed_annotation_category = parsed_annotation.clone().category();
        let actual_contains;
        if RoleTypeAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            actual_contains = relates.role()
                .get_annotations(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .contains_key(&parsed_annotation.into());
        } else if RelatesAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            actual_contains = relates
                .get_annotations(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .contains_key(&parsed_annotation.into());
        } else {
            unimplemented!("Annotation {:?} is not supported by roles and relates", parsed_annotation_category);
        }
        assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
    });
}


#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get annotation categories {contains_or_doesnt}: {annotation_category}")]
pub async fn relation_role_annotation_categories_contain(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation_category: AnnotationCategory,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();

        let parsed_annotation_category = annotation_category.into_typedb();
        let actual_contains;
        if RoleTypeAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            actual_contains = relates
                .role()
                .get_annotations(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .iter().map(|(annotation, _)| <RoleTypeAnnotation as Into<annotation::Annotation>>::into(annotation.clone()).category())
                .contains(&parsed_annotation_category);
        } else if RelatesAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            actual_contains = relates
                .get_annotations(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .iter().map(|(annotation, _)| <RelatesAnnotation as Into<annotation::Annotation>>::into(annotation.clone()).category())
                .contains(&parsed_annotation_category);
        } else {
            unimplemented!("Annotation {:?} is not supported by roles and relates", parsed_annotation_category);
        }
        assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get declared annotations {contains_or_doesnt}: {annotation}")]
pub async fn relation_role_declared_annotations_contain(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    annotation: Annotation,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();

        let parsed_annotation = annotation.into_typedb();
        let parsed_annotation_category = parsed_annotation.clone().category();
        let actual_contains;
        if RoleTypeAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            actual_contains = relates.role()
                .get_annotations_declared(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .contains(&parsed_annotation.into());
        } else if RelatesAnnotation::try_getting_default(parsed_annotation_category).is_ok() {
            actual_contains = relates
                .get_annotations_declared(&tx.snapshot, &tx.type_manager)
                .unwrap()
                .contains(&parsed_annotation.into());
        } else {
            unimplemented!("Annotation {:?} is not supported by roles and relates", parsed_annotation_category);
        }
        assert_eq!(contains_or_doesnt.expected_contains(), actual_contains);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get annotations {is_empty_or_not}")]
pub async fn relation_role_annotations_is_empty(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    is_empty_or_not: IsEmptyOrNot,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();
        let relates_empty =
            relates.get_annotations(&tx.snapshot, &tx.type_manager).unwrap().is_empty();
        let role_empty =
            relates.role().get_annotations(&tx.snapshot, &tx.type_manager).unwrap().is_empty();

        let actual_is_empty = relates_empty && role_empty;
        is_empty_or_not.check(actual_is_empty);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get declared annotations {is_empty_or_not}")]
pub async fn relation_role_declared_annotations_is_empty(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    is_empty_or_not: IsEmptyOrNot,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let relates = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap();
        let relates_empty =
            relates.get_annotations_declared(&tx.snapshot, &tx.type_manager).unwrap().is_empty();
        let role_empty =
            relates.role().get_annotations_declared(&tx.snapshot, &tx.type_manager).unwrap().is_empty();

        let actual_is_empty = relates_empty && role_empty;
        is_empty_or_not.check(actual_is_empty);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) set ordering: {ordering}{may_error}")]
pub async fn relation_role_set_ordering(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    ordering: params::Ordering,
    may_error: MayError,
) {
    with_schema_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let res = role.set_ordering(&mut tx.snapshot, &tx.type_manager, ordering.into_typedb().into());
        may_error.check(&res);
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get ordering: {ordering}")]
pub async fn relation_role_get_ordering(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    ordering: params::Ordering,
) {
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = tx
            .type_manager
            .resolve_relates(&tx.snapshot, relation, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        assert_eq!(role.get_ordering(&tx.snapshot, &tx.type_manager).unwrap(), ordering.into_typedb().into());
    });
}

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get players {contains_or_doesnt}:")]
pub async fn role_type_players_contain(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels: Vec<String> = util::iter_table(step).map(|str| str.to_owned()).collect::<Vec<String>>();
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_of_role(&tx.snapshot, &tx.type_manager, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let actual_labels = role
            .get_plays(&tx.snapshot, &tx.type_manager)
            .unwrap()
            .iter()
            .map(|(_, plays)| match plays.player() {
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

#[apply(generic_step)]
#[step(expr = r"relation\({type_label}\) get role\({type_label}\) get declared players {contains_or_doesnt}:")]
pub async fn role_type_declared_players_contain(
    context: &mut Context,
    relation_label: Label,
    role_label: Label,
    contains_or_doesnt: ContainsOrDoesnt,
    step: &Step,
) {
    let expected_labels: Vec<String> = util::iter_table(step).map(|str| str.to_owned()).collect::<Vec<String>>();
    with_read_tx!(context, |tx| {
        let relation = tx.type_manager.get_relation_type(&tx.snapshot, &relation_label.into_typedb()).unwrap().unwrap();
        let role = relation
            .get_relates_of_role(&tx.snapshot, &tx.type_manager, role_label.into_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        let actual_labels = role
            .get_plays_declared(&tx.snapshot, &tx.type_manager)
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
