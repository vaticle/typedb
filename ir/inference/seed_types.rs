/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeSet, HashMap};
use itertools::Itertools;

use crate::pattern::constraint::{Constraint, Type};
use storage::snapshot::ReadableSnapshot;
use concept::type_::type_manager::TypeManager;
use concept::type_::TypeAPI;
use encoding::value::label::Label;
use crate::pattern::variable::Variable;

fn seed_types<Snapshot: ReadableSnapshot>(constraints: &Vec<Constraint>, snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>) {
    // Seed unary types
    let unary_type_constraints = HashMap::new();
    seed_types_for_unary_constraints(constraints, snapshot, type_manager);


}

fn seed_types_for_unary_constraints<Snapshot: ReadableSnapshot>(constraints: &Vec<Constraint>, snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>, unary_annotations: &mut HashMap<Variable, BTreeSet<Type>>) {
    // First we populate the type variables
    for constraint in constraints {
        match constraint {
            Constraint::Type(type_constraint) => {
                merge_unary(unary_annotations, type_constraint.var, get_subtypes_by_label(snapshot, type_manager, &type_constraint));
            },
            _ => {} // Ignore
        }
    }
    for constraint in constraints {
        match constraint {
            Constraint::Isa(isa_constraint) => {

            },
            _ => {}
        }
    }
    for constraint in constraints {
        match constraint {
            Constraint::FunctionCallBinding(function_constraint) => todo!("Apply?"),
            Constraint::ExpressionBinding(_) => todo!("Apply?"), // For the lhs?

            Constraint::Isa(_) |
            Constraint::Type(_) |
            Constraint::RolePlayer(_) |
            Constraint::Has(_) |
            Constraint::Comparison(_) => {} // Do nothing
        }
    }


}

fn merge_unary(unary_annotations: &mut HashMap<Variable, BTreeSet<Type>>, variable: Variable, new_annotations: BTreeSet<Type>) {
    if let Some(existing_annotations) = unary_annotations.get_mut(&variable) {
        existing_annotations.retain(|x| new_annotations.contains(x))
    } else {
        unary_annotations.insert(variable, new_annotations.into());
    }
}

fn get_subtypes_by_label<Snapshot: ReadableSnapshot>(snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>, type_: &Type) -> BTreeSet<Type> {
    if let Some(attribute) = type_manager.get_attribute_type(snapshot, &type_.type_).unwrap() {
        attribute.get_subtypes(snapshot, type_manager).unwrap().iter()
            .map(|subtype| Type { var: type_.var, type_: subtype.get_label(snapshot, type_manager).unwrap().into_owned() })
            .collect()
    } else if let Some(entity) = type_manager.get_entity_type(snapshot, &type_.type_).unwrap() {
        entity.get_subtypes(snapshot, type_manager).unwrap().iter()
            .map(|subtype| Type { var: type_.var, type_: subtype.get_label(snapshot, type_manager).unwrap().into_owned() })
            .collect()
    } else if let Some(relation) = type_manager.get_relation_type(snapshot, &type_.type_).unwrap() {
        relation.get_subtypes(snapshot, type_manager).unwrap().iter()
            .map(|subtype| Type { var: type_.var, type_: subtype.get_label(snapshot, type_manager).unwrap().into_owned() })
            .collect()
    } else if let Some(role_type) = type_manager.get_role_type(snapshot, &type_.type_).unwrap() {
        role_type.get_subtypes(snapshot, type_manager).unwrap().iter()
            .map(|subtype| Type { var: type_.var, type_: subtype.get_label(snapshot, type_manager).unwrap().into_owned() })
            .collect()
    } else {
        unreachable!()
    }
}

