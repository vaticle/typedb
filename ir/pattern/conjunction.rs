/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    fmt::{Display, Formatter},
    sync::{Arc, Mutex, MutexGuard},
};

use answer::variable::Variable;
use itertools::Itertools;

use crate::{
    pattern::{constraint::Constraints, context::PatternContext, pattern::Patterns, Scope, ScopeId},
    PatternDefinitionError,
};

#[derive(Debug)]
pub struct Conjunction {
    scope_id: ScopeId,
    context: Arc<Mutex<PatternContext>>,

    constraints: Constraints,
    patterns: Patterns,
}

impl Conjunction {
    pub fn new_root() -> Self {
        let context = Arc::new(Mutex::from(PatternContext::new()));
        let scope_id = context.lock().unwrap().create_root_scope();

        Conjunction {
            scope_id,
            context: context.clone(),
            constraints: Constraints::new(scope_id, context.clone()),
            patterns: Patterns::new(scope_id, context),
        }
    }

    pub(crate) fn new_child(parent_scope_id: ScopeId, context: Arc<Mutex<PatternContext>>) -> Self {
        let scope_id = context.lock().unwrap().create_child_scope(parent_scope_id);
        Conjunction {
            scope_id,
            context: context.clone(),
            constraints: Constraints::new(scope_id, context.clone()),
            patterns: Patterns::new(scope_id, context),
        }
    }

    pub(crate) fn scope_id(&self) -> ScopeId {
        self.scope_id
    }

    pub fn constraints(&self) -> &Constraints {
        &self.constraints
    }

    pub fn patterns(&self) -> &Patterns {
        &self.patterns
    }

    pub fn constraints_mut(&mut self) -> &mut Constraints {
        &mut self.constraints
    }

    pub fn patterns_mut(&mut self) -> &mut Patterns {
        &mut self.patterns
    }

    pub(crate) fn context(&self) -> MutexGuard<PatternContext> {
        self.context.lock().unwrap()
    }

    pub fn get_or_declare_variable(&mut self, name: &str) -> Result<Variable, PatternDefinitionError> {
        self.context.lock().unwrap().get_or_declare_variable_named(name, self)
    }
}

impl Scope for Conjunction {
    fn scope_id(&self) -> ScopeId {
        self.scope_id
    }
}

impl Display for Conjunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let current_width = f.width().unwrap_or(0);
        let indent = (0..current_width).map(|_| " ").join("");
        writeln!(f, "{}{} Conjunction", indent, self.scope_id)?;
        write!(f, "{:>width$}", &self.constraints, width = current_width + 2)?;
        write!(f, "{:>width$}", &self.patterns, width = current_width + 2)?;
        write!(f, "{}", self.context.lock().unwrap())?;
        Ok(())
    }
}
