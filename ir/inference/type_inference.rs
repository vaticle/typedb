/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use answer::{variable::Variable};
use encoding::graph::definition::definition_key::DefinitionKey;

use crate::{
    pattern::{
        conjunction::Conjunction,
        constraint::{Constraint, Type},
        pattern::Pattern,
    },
    program::{program::Program, FunctionalBlock},
};
use crate::inference::pattern_type_inference::{TypeInferenceGraph};

/*
Design:
1. Assign a static, deterministic ordering over the functions in the Program.
2. Assign a static, deterministic ordering over the connected variables in each functional block's Pattern.
3. Set the possible types for each variable to all types of its category initially (note: function input and output variables can be restricted to subtypes of labelled types initially!)
4. For each variable in the ordering, go over each constraint and intersect types

Output data structure:
TypeAnnotations per FunctionalBlock

Note: On function call boundaries, can assume the current set of schema types per input and output variable.
      However, we should then recurse into the sub-function IRs and tighten their input/output types based on their type inference.

 */

pub(crate) type VertexConstraints = BTreeMap<Variable, BTreeSet<Type>>;

pub fn infer_types(program: &Program) {
    // let mut entry_type_annotations = TypeAnnotations::new();
    // let mut function_type_annotations: HashMap<DefinitionKey<'static>, TypeAnnotations> = HashMap::new();
    todo!()
}
