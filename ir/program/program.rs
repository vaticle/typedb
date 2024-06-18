/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashMap;

use encoding::graph::definition::definition_key::DefinitionKey;

use crate::{
    pattern::pattern::Pattern,
    program::{
        function::FunctionIR,
        modifier::{Filter, Limit, Modifier, ModifierDefinitionError, Offset, Sort},
        FunctionalBlock,
    },
};

pub struct Program {
    entry: Pattern,
    modifiers: Vec<Modifier>,
    functions: HashMap<DefinitionKey<'static>, FunctionIR>,
}

impl Program {
    pub fn new(pattern: Pattern, functions: HashMap<DefinitionKey<'static>, FunctionIR>) -> Self {
        // TODO: verify exactly the required functions are provided
        debug_assert!(Self::all_variables_categorised(&pattern));

        Self { entry: pattern, modifiers: Vec::new(), functions: functions }
    }

    fn all_variables_categorised(pattern: &Pattern) -> bool {
        let context = pattern.context();
        let mut variables = context.get_variables();
        variables.all(|var| context.get_variable_category(var).is_some())
    }

    pub(crate) fn functions(&self) -> &HashMap<DefinitionKey<'static>, FunctionIR> {
        &self.functions
    }
}

impl FunctionalBlock for Program {
    fn pattern(&self) -> &Pattern {
        &self.entry
    }

    fn add_limit(&mut self, limit: u64) {
        self.modifiers.push(Modifier::Limit(Limit::new(limit)));
    }

    fn add_offset(&mut self, offset: u64) {
        self.modifiers.push(Modifier::Offset(Offset::new(offset)))
    }

    fn add_sort(&mut self, sort_variables: Vec<(&str, bool)>) -> Result<(), ModifierDefinitionError> {
        let sort = Sort::new(sort_variables, &self.entry.context())?;
        self.modifiers.push(Modifier::Sort(sort));
        Ok(())
    }

    fn add_filter(&mut self, variables: Vec<&str>) -> Result<(), ModifierDefinitionError> {
        let filter = Filter::new(variables, &self.entry.context())?;
        self.modifiers.push(Modifier::Filter(filter));
        Ok(())
    }
}
