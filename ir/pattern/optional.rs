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

use crate::pattern::{conjunction::Conjunction, context::PatternContext, Scope, ScopeId};

#[derive(Debug)]
pub struct Optional {
    context: Arc<Mutex<PatternContext>>,
    conjunction: Conjunction,
}

impl Optional {
    pub(crate) fn TODO__new(context: Arc<Mutex<PatternContext>>, conjunction: Conjunction) -> Optional {
        Self { context, conjunction }
    }

    pub(crate) fn context(&self) -> MutexGuard<PatternContext> {
        self.context.lock().unwrap()
    }

    pub(crate) fn conjunction(&self) -> &Conjunction {
        &self.conjunction
    }
}

impl Optional {
    pub(crate) fn variables(&self) -> Box<dyn Iterator<Item = Variable>> {
        todo!()
    }
}

impl Scope for Optional {
    fn scope_id(&self) -> ScopeId {
        todo!()
    }
}

impl Display for Optional {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
