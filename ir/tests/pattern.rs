/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use ir::{
    pattern::{conjunction::Conjunction, variable_category::VariableCategory},
    PatternDefinitionError,
};

#[test]
fn build_conjunction_constraints() {
    let mut conjunction = Conjunction::new_root();

    let var_person = conjunction.get_or_declare_variable(&"person").unwrap();
    let var_name = conjunction.get_or_declare_variable(&"name").unwrap();
    let var_person_type = conjunction.get_or_declare_variable(&"person_type").unwrap();
    let var_name_type = conjunction.get_or_declare_variable(&"name_type").unwrap();

    conjunction.constraints_mut().add_isa(var_person, var_person_type).unwrap();
    conjunction.constraints_mut().add_has(var_person, var_name).unwrap();
    conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
    conjunction.constraints_mut().add_type(var_person_type, "person").unwrap();
    conjunction.constraints_mut().add_type(var_name_type, "name").unwrap();
}

#[test]
fn variable_category_mismatch() {
    let mut conjunction = Conjunction::new_root();

    let var_person = conjunction.get_or_declare_variable(&"person").unwrap();
    let var_person_type = conjunction.get_or_declare_variable(&"person_type").unwrap();

    let result = conjunction.constraints_mut().add_isa(var_person, var_person_type);
    assert!(result.is_ok());
    let result = conjunction.constraints_mut().add_isa(var_person_type, var_person);
    assert!(matches!(
        result,
        Err(PatternDefinitionError::VariableCategoryMismatch {
            variable: var_person_type,
            category_1: VariableCategory::Thing,
            category_2: VariableCategory::Type,
            ..
        })
    ));
}

#[test]
fn variable_category_narrowing() {
    let mut conjunction = Conjunction::new_root();

    let var_person = conjunction.get_or_declare_variable(&"person").unwrap();
    let var_name = conjunction.get_or_declare_variable(&"name").unwrap();
    let var_person_type = conjunction.get_or_declare_variable(&"person_type").unwrap();
    let var_name_type = conjunction.get_or_declare_variable(&"name_type").unwrap();

    conjunction.constraints_mut().add_isa(var_person, var_person_type).unwrap();
    conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
    // narrow name from Isa Thing to Attribute and person from Isa thing to Object owner
    conjunction.constraints_mut().add_has(var_person, var_name).unwrap();

    println!("{}", conjunction)
}
