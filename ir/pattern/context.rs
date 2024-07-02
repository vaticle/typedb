/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
};

use answer::variable::Variable;
use itertools::Itertools;

use crate::{
    pattern::{
        constraint::Constraint,
        variable_category::{VariableCategory, VariableOptionality},
        Scope, ScopeId,
    },
    PatternDefinitionError,
};

#[derive(Debug)]
pub struct PatternContext {
    variable_names: HashMap<Variable, String>,
    variable_declaration: HashMap<Variable, ScopeId>,
    variable_names_index: HashMap<String, Variable>,
    variable_id_allocator: u16,

    scope_id_allocator: u16,
    scope_parents: HashMap<ScopeId, ScopeId>,

    variable_categories: HashMap<Variable, (VariableCategory, Constraint<Variable>)>,
    variable_optionality: HashMap<Variable, VariableOptionality>,
}

impl PatternContext {
    pub(crate) fn new() -> PatternContext {
        Self {
            variable_names: HashMap::new(),
            variable_declaration: HashMap::new(),
            variable_names_index: HashMap::new(),
            variable_id_allocator: 0,
            scope_id_allocator: 0,
            scope_parents: HashMap::new(),
            variable_categories: HashMap::new(),
            variable_optionality: HashMap::new(),
        }
    }

    pub(crate) fn get_or_declare_variable_named(
        &mut self,
        name: &str,
        scope: &impl Scope,
    ) -> Result<Variable, PatternDefinitionError> {
        match self.variable_names_index.get(name) {
            None => {
                let variable = self.allocate_variable();
                self.variable_names.insert(variable, name.to_string());
                self.variable_declaration.insert(variable, scope.scope_id());
                self.variable_names_index.insert(name.to_string(), variable);
                Ok(variable)
            }
            Some(existing_variable) => {
                let existing_scope = self.variable_declaration.get_mut(existing_variable).unwrap();
                if Self::is_equal_or_parent_scope(&self.scope_parents, scope.scope_id(), *existing_scope) {
                    // Parent defines same name: ok, reuse the variable
                    Ok(*existing_variable)
                } else if Self::is_child_scope(&self.scope_parents, scope.scope_id(), *existing_scope) {
                    // Child defines the same name: ok, reuse the variable, and change the declaration scope to the current one
                    *existing_scope = scope.scope_id();
                    Ok(*existing_variable)
                } else {
                    Err(PatternDefinitionError::DisjointVariableReuse { variable_name: name.to_string() })
                }
            }
        }
    }

    pub(crate) fn get_variable(&self, name: &str) -> Option<Variable> {
        self.variable_names_index.get(name).cloned()
    }

    pub(crate) fn get_variables(&self) -> impl Iterator<Item = Variable> + '_ {
        self.variable_declaration.keys().into_iter().cloned()
    }

    fn allocate_variable(&mut self) -> Variable {
        let variable = Variable::new(self.variable_id_allocator);
        self.variable_id_allocator += 1;
        variable
    }

    pub(crate) fn is_variable_available(&self, scope: ScopeId, variable: Variable) -> bool {
        let variable_scope = self.variable_declaration.get(&variable);
        match variable_scope {
            None => false,
            Some(variable_scope) => return Self::is_equal_or_parent_scope(&self.scope_parents, scope, *variable_scope),
        }
    }

    pub(crate) fn create_root_scope(&mut self) -> ScopeId {
        debug_assert!(self.scope_id_allocator == 0);
        let scope = ScopeId::new(self.scope_id_allocator);
        self.scope_id_allocator += 1;
        scope
    }

    pub(crate) fn create_child_scope(&mut self, parent: ScopeId) -> ScopeId {
        let scope = ScopeId::new(self.scope_id_allocator);
        self.scope_id_allocator += 1;
        self.scope_parents.insert(scope, parent);
        scope
    }

    pub(crate) fn get_variable_category(&self, variable: Variable) -> Option<VariableCategory> {
        self.variable_categories.get(&variable).map(|(category, optionality)| *category)
    }

    pub(crate) fn set_variable_category(
        &mut self,
        variable: Variable,
        category: VariableCategory,
        source: Constraint<Variable>,
    ) -> Result<(), PatternDefinitionError> {
        let mut existing_category = self.variable_categories.get_mut(&variable);
        match existing_category {
            None => {
                self.variable_categories.insert(variable, (category, source));
                Ok(())
            }
            Some((existing_category, existing_source)) => {
                let narrowest = existing_category.narrowest(category);
                match narrowest {
                    None => Err(PatternDefinitionError::VariableCategoryMismatch {
                        variable,
                        variable_name: self.variable_names.get(&variable).cloned(),
                        category_1: category,
                        category_1_source: source,
                        category_2: *existing_category,
                        category_2_source: existing_source.clone(),
                    }),
                    Some(narrowed) => {
                        if narrowed == *existing_category {
                            Ok(())
                        } else {
                            *existing_category = narrowed;
                            *existing_source = source;
                            Ok(())
                        }
                    }
                }
            }
        }
    }

    pub(crate) fn set_variable_is_optional(&mut self, variable: Variable) {
        self.variable_optionality.insert(variable, VariableOptionality::Optional);
    }

    pub(crate) fn is_variable_optional(&self, variable: Variable) -> bool {
        match self.variable_optionality.get(&variable).unwrap_or(&VariableOptionality::Required) {
            VariableOptionality::Required => false,
            VariableOptionality::Optional => true,
        }
    }

    fn is_equal_or_parent_scope(parents: &HashMap<ScopeId, ScopeId>, scope: ScopeId, maybe_parent: ScopeId) -> bool {
        scope == maybe_parent
            || Self::get_scope_parent(parents, scope)
                .map(|p| Self::is_equal_or_parent_scope(parents, p, maybe_parent))
                .unwrap_or(false)
    }

    fn is_child_scope(parents: &HashMap<ScopeId, ScopeId>, scope: ScopeId, maybe_child: ScopeId) -> bool {
        Self::get_scope_parent(parents, maybe_child)
            .map(|c| c == scope || Self::is_child_scope(parents, scope, c))
            .unwrap_or(false)
    }

    fn get_scope_parent(parents: &HashMap<ScopeId, ScopeId>, scope: ScopeId) -> Option<ScopeId> {
        parents.get(&scope).cloned()
    }
}

impl Display for PatternContext {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Named variables:")?;
        for entry in self.variable_names.iter().sorted_by_key(|e| e.0) {
            writeln!(f, "  {}: ${}", entry.0, entry.1)?;
        }
        writeln!(f, "Variable categories:")?;
        for entry in self.variable_categories.iter().sorted_by_key(|e| e.0) {
            writeln!(f, "  {}: {}", entry.0, entry.1 .0)?;
        }
        writeln!(f, "Optional variables:")?;
        for entry in self.variable_optionality.iter().sorted_by_key(|e| e.0) {
            writeln!(f, "  {}", entry.0)?;
        }
        Ok(())
    }
}
