/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use answer::{variable::Variable, Type};
use encoding::graph::definition::definition_key::DefinitionKey;

use crate::{
    pattern::{
        constraint::{Constraint, Type},
    },
    program::{program::Program, FunctionalBlock},
};
use crate::pattern::pattern::Pattern;

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
//
// pub fn infer_types(program: &Program) {
//     let mut entry_type_annotations = TypeAnnotations::new();
//     let mut function_type_annotations: HashMap<DefinitionKey<'static>, TypeAnnotations> = HashMap::new();
//     todo!()
// }

pub(crate) type VertexConstraints = BTreeMap<Variable, BTreeSet<Type>>;
//
// pub fn infer_types(program: &Program) {
//     let mut entry_type_annotations = TypeAnnotations::new();
//
//
//     // Bottom-up information flow. This should already have been done at schema commit time.
//
//     todo!()
// }
//
// pub fn bottom_up_function_inference(pattern: Pattern) -> HashMap<DefinitionKey<'static>, VertexConstraints> {
//     let mut first_pass_annotations: HashMap<&DefinitionKey<'static>, VertexConstraints> = HashMap::new();
//     for function in program.pattern().function_calls() {
//         bottom_up_function_inference_rec(pattern, &HashMap::new(), &mut first_pass_annotations);
//     }
//
//     let mut final_annotations: HashMap<&DefinitionKey<'static>, VertexConstraints> = HashMap::new();
//     bottom_up_function_inference_rec(pattern, &first_pass_annotations, &mut final_annotations);
//     final_annotations
// }
//
// pub fn bottom_up_function_inference_rec(pattern: Pattern) -> HashMap<DefinitionKey<'static>, VertexConstraints> {
//     let mut first_pass_annotations: HashMap<&DefinitionKey<'static>, VertexConstraints> = HashMap::new();
//     for function in program.pattern().function_calls() {
//         bottom_up_function_inference_rec(pattern, &HashMap::new(), &mut first_pass_annotations);
//     }
//
//     let mut final_annotations: HashMap<&DefinitionKey<'static>, VertexConstraints> = HashMap::new();
//     bottom_up_function_inference_rec(pattern, &first_pass_annotations, &mut final_annotations);
//     final_annotations
// }
//
// pub fn recursively_infer_types(
//     pattern: Pattern,
//     existing_constraints: &HashMap<&DefinitionKey<'static>, VertexConstraints>,
//     refined_constraints: &mut HashMap<&DefinitionKey<'static>, VertexConstraints>
// ) {
//
// }
