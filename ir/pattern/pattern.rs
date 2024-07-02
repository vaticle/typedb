/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    fmt::{Debug, Display, Formatter},
    sync::{Arc, Mutex, MutexGuard},
};

use crate::pattern::{
    conjunction::Conjunction, context::PatternContext, disjunction::Disjunction, negation::Negation,
    optional::Optional, ScopeId,
};

#[derive(Debug)]
pub(crate) struct Patterns {
    scope: ScopeId,
    context: Arc<Mutex<PatternContext>>,
    pub(crate) patterns: Vec<Pattern>,
}

impl Patterns {
    pub(crate) fn new(scope: ScopeId, context: Arc<Mutex<PatternContext>>) -> Self {
        Self { scope, context, patterns: Vec::new() }
    }

    pub(crate) fn add_conjunction(&mut self) -> &mut Conjunction {
        let conjunction = Conjunction::new_child(self.scope, self.context.clone());
        self.patterns.push(Pattern::Conjunction(conjunction));
        self.patterns.last_mut().unwrap().as_conjunction_mut().unwrap()
    }

    pub(crate) fn add_disjunction(&mut self) -> &mut Disjunction {
        let disjunction = Disjunction::new_child(self.scope, self.context.clone());
        self.patterns.push(Pattern::Disjunction(disjunction));
        self.patterns.last_mut().unwrap().as_disjunction_mut().unwrap()
    }
}

impl Display for Patterns {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for pattern in &self.patterns {
            write!(f, "{}", pattern)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Pattern {
    Conjunction(Conjunction),
    Disjunction(Disjunction),
    Negation(Negation),
    Optional(Optional),
}

impl Pattern {
    pub(crate) fn context(&self) -> MutexGuard<PatternContext> {
        match self {
            Pattern::Conjunction(conjunction) => conjunction.context(),
            Pattern::Disjunction(disjunction) => disjunction.context(),
            Pattern::Negation(negation) => negation.context(),
            Pattern::Optional(optional) => optional.context(),
        }
    }

    pub(crate) fn as_conjunction(&self) -> Option<&Conjunction> {
        match self {
            Pattern::Conjunction(conjunction) => Some(conjunction),
            _ => None,
        }
    }

    pub(crate) fn as_conjunction_mut(&mut self) -> Option<&mut Conjunction> {
        match self {
            Pattern::Conjunction(conjunction) => Some(conjunction),
            _ => None,
        }
    }

    pub(crate) fn as_disjunction(&self) -> Option<&Disjunction> {
        match self {
            Pattern::Disjunction(disjunction) => Some(disjunction),
            _ => None,
        }
    }

    pub(crate) fn as_disjunction_mut(&mut self) -> Option<&mut Disjunction> {
        match self {
            Pattern::Disjunction(disjunction) => Some(disjunction),
            _ => None,
        }
    }

    fn as_negation(&self) -> Option<&Negation> {
        match self {
            Pattern::Negation(negation) => Some(negation),
            _ => None,
        }
    }

    pub(crate) fn as_negation_mut(&mut self) -> Option<&mut Negation> {
        match self {
            Pattern::Negation(negation) => Some(negation),
            _ => None,
        }
    }

    pub(crate) fn as_optional(&self) -> Option<&Optional> {
        match self {
            Pattern::Optional(optional) => Some(optional),
            _ => None,
        }
    }

    pub(crate) fn as_optional_mut(&mut self) -> Option<&mut Optional> {
        match self {
            Pattern::Optional(optional) => Some(optional),
            _ => None,
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Conjunction(pattern) => Display::fmt(pattern, f),
            Pattern::Disjunction(pattern) => Display::fmt(pattern, f),
            Pattern::Negation(pattern) => Display::fmt(pattern, f),
            Pattern::Optional(pattern) => Display::fmt(pattern, f),
        }
    }
}
