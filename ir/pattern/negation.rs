/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    fmt::{Display, Formatter},
    sync::{Arc, Mutex, MutexGuard},
};

use crate::pattern::{conjunction::Conjunction, context::PatternContext, Scope, ScopeId};

#[derive(Debug)]
pub(crate) struct Negation {
    context: Arc<Mutex<PatternContext>>,
    conjunction: Conjunction,
}

impl Negation {
    pub(crate) fn TODO__new(context: Arc<Mutex<PatternContext>>, conjunction: Conjunction) -> Negation {
        Self { context, conjunction }
    }

    pub(crate) fn context(&self) -> MutexGuard<PatternContext> {
        self.context.lock().unwrap()
    }

    pub(crate) fn conjunction(&self) -> &Conjunction {
        &self.conjunction
    }
}

impl Scope for Negation {
    fn scope_id(&self) -> ScopeId {
        todo!()
    }
}

impl Display for Negation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
