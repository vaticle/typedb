/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{error::Error, fmt};

use crate::pattern::{
    constraint::Constraint,
    variable::{Variable, VariableCategory},
};

mod inference;
mod optimisation;
pub mod pattern;
pub mod program;

#[derive(Debug)]
pub enum PatternDefinitionError {
    DisjointVariableReuse {
        variable_name: String,
    },
    VariableCategoryMismatch {
        variable: Variable,
        variable_name: Option<String>,
        category_1: VariableCategory,
        category_1_source: Constraint,
        category_2: VariableCategory,
        category_2_source: Constraint,
    },
    FunctionArgumentUnused {
        argument_variable: String,
    },
    FunctionCallReturnArgCountMismatch {
        assigned_var_count: usize,
        function_return_count: usize,
    },
}

impl fmt::Display for PatternDefinitionError {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for PatternDefinitionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::DisjointVariableReuse { .. } => None,
            Self::VariableCategoryMismatch { .. } => None,
            Self::FunctionArgumentUnused { .. } => None,
            PatternDefinitionError::FunctionCallReturnArgCountMismatch { .. } => None,
        }
    }
}
