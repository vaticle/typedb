/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use answer::{variable::Variable, Type};
use encoding::graph::definition::definition_key::DefinitionKey;
use log::debug;

use crate::{pattern::constraint::Constraint, program::program::Program};

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

pub fn infer_types(program: &Program) {
    let mut entry_type_annotations = TypeAnnotations::new();
    let mut function_type_annotations: HashMap<DefinitionKey<'static>, TypeAnnotations> = HashMap::new();
}

struct TypeAnnotations {
    variables: HashMap<Variable, HashSet<Type>>,
    constraints: HashMap<Constraint<Variable>, ConstraintTypeAnnotations>,
}

impl TypeAnnotations {
    fn new() -> Self {
        TypeAnnotations { variables: HashMap::new(), constraints: HashMap::new() }
    }
}

enum ConstraintTypeAnnotations {
    LeftRight(LeftRightAnnotations),
    LeftRightFiltered(LeftRightFilteredAnnotations), // note: function calls, comparators, and value assignments are not stored here, since they do not actually co-constrain Schema types possible.
                                                     //       in other words, they are always right to left or deal only in value types.
}

struct LeftRightAnnotations {
    left_to_right: BTreeMap<Type, BTreeSet<Type>>,
    right_to_left: BTreeMap<Type, BTreeSet<Type>>,
}

struct LeftRightFilteredAnnotations {
    left_to_right: BTreeMap<Type, (BTreeSet<Type>, HashSet<Type>)>,
    right_to_left: BTreeMap<Type, (BTreeSet<Type>, HashSet<Type>)>,
    // TODO: I think we'll need to be able to traverse from the Filter variable to the left and right. example: `match $role sub friendship:friend; $r ($role: $x);`
    // filter_to_left
    // filter_to_right
}

struct TypeInferenceGraph {
    vertices: HashMap<Variable, HashSet<Type>>,
    edges: Vec<TypeInferenceEdge>
}

struct TypeInferenceEdge {
    left: Variable,
    right: Variable,
    left_support: HashMap<Type, usize>,
    right_support: HashMap<Type, usize>,

    left_right_annotations: LeftRightAnnotations,
}

impl TypeInferenceEdge {

    // Construction
    fn new(left: Variable, right: Variable, left_right_annotations: LeftRightAnnotations) -> TypeInferenceEdge {
        // (Assuming) the binary constraints were built based on the unary constraints of the variable on the same-side,
        // We must construct the support set in a way that left_to_right and right_to_left are made consistent.
        // This is a pre-condition to the type-inference loop.
        let mut left_support: HashMap<Type, usize> = HashMap::new();
        let mut right_support: HashMap<Type, usize> = HashMap::new();
        Self::populate_support(&mut right_support, &left_right_annotations.left_to_right);
        Self::populate_support(&mut left_support, &left_right_annotations.right_to_left);
        TypeInferenceEdge { left, right, left_support, right_support, left_right_annotations }
    }

    fn populate_support(support: &mut HashMap<Type, usize>, reverse_annotations: &BTreeMap<Type, BTreeSet<Type>>) {
        for (_, types) in reverse_annotations {
            for type_ in types {
                if !support.contains_key(&type_) {
                    support.insert(type_.clone(), 0);
                }
                Self::update_support(support, &type_, 1);
            }
        }
    }

    // Updates
    fn remove_type(&mut self, from_variable: Variable, type_: Type) {
        let TypeInferenceEdge { left, right, left_support, right_support, left_right_annotations}  = &mut self;
        if &from_variable == left {
            Self::remove_type_and_decrement_support(type_, left_support, right_support, &left_right_annotations.left_to_right)
        } else if &from_variable == right {
            Self::remove_type_and_decrement_support(type_, right_support, left_support, &left_right_annotations.right_to_left)
        } else {
            unreachable!("Bad argument. Expected variable to be {} or {}, but was {}", self.left, self.right, from_variable)
        }
    }

    fn remove_type_and_decrement_support(type_: Type, remove_from_side: &mut HashMap<Type, usize>, propagate_to_side: &mut HashMap<Type, usize>, annotations: &BTreeMap<Type, BTreeSet<Type>>) {
        debug_assert!(remove_from_side.contains_key(&type_) && annotations.contains_key(&type_));
        remove_from_side.remove(&type_);
        for other_type in annotations.get(&type_).unwrap() {
            let remaining_support = Self::update_support(propagate_to_side, other_type, -1);
            if remaining_support == 0 {
                propagate_to_side.remove(&other_type);
            }
        }
    }

    // Utils
    fn update_support(support_map: &mut HashMap<Type, usize>, type_: &Type, delta: isize) -> usize{
        debug_assert!(support_map.contains_key(&type_));
        let support = support_map.get_mut(&type_).unwrap();
        *support = *support + delta;
        *support
    }
}

impl TypeInferenceGraph {
    fn run_type_inference(&mut self) {
        let mut is_modified= self.prune_vertices_from_edges(); // We may need this as pre-condition
        while is_modified {
            self.prune_edges_from_vertices();
            is_modified = self.prune_vertices_from_edges();
        }
    }

    fn prune_edges_from_vertices(&mut self) {
        for edge in &mut self.edges {
            {
                let left_vertices = self.vertices.get_mut(&edge.left).unwrap();
                let prune_left: Vec<Type> = (edge.left_support.keys() - left_vertices);
                prune_left.into_iter().for_each(|type_| { edge.remove_type(edge.left, type_) });
            }
            {
                let right_vertices = self.vertices.get_mut(&edge.right).unwrap();
                let prune_right: Vec<Type> = (edge.right_support.keys() - right_vertices);
                prune_right.into_iter().for_each(|type_| { edge.remove_type(edge.right, type_) })
            }
        }
    }

    fn prune_vertices_from_edges(&mut self) -> bool {
        let mut is_modified = false;
        for edge in &mut self.edges {
            {
                let left_vertices = self.vertices.get_mut(&edge.left).unwrap();
                let size_before = left_vertices.len();
                left_vertices.retain(|k| { edge.left_support.contains_key(k) });
                is_modified = is_modified || size_before != left_vertices.len();
            }
            {
                let right_vertices = self.vertices.get_mut(&edge.right).unwrap();
                let size_before = right_vertices.len();
                right_vertices.retain(|k| { edge.right_support.contains_key(k) });
                is_modified = is_modified || size_before != right_vertices.len();
            }
        }
        is_modified
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
    use crate::inference::type_inference::{LeftRightAnnotations, TypeInferenceEdge, TypeInferenceGraph};
    use crate::pattern::constraint::tests::tests__new_type;
    use crate::pattern::constraint::Type;
    use crate::pattern::variable::Variable;

    #[test]
    fn basic() {
        // dog sub animal, owns dog-name; cat sub animal owns cat-name;
        // cat-name sub animal-name; dog-name sub animal-name;


        // Some version of `$a isa animal, has name $n;`
        let var_animal = Variable::new(0);
        let var_name = Variable::new(1);

        let type_animal = tests__new_type(var_animal, "animal".to_owned());
        let type_cat = tests__new_type(var_animal, "cat".to_owned());
        let type_dog = tests__new_type(var_animal, "dog".to_owned());

        let type_name = tests__new_type(var_name, "name".to_owned());
        let type_catname = tests__new_type(var_name, "cat-name".to_owned());
        let type_dogname = tests__new_type(var_name, "dog-name".to_owned());

        let all_animals = BTreeSet::from([type_animal.clone(), type_cat.clone(), type_dog.clone()]))];

        {
            // Case 1: $a isa cat, has animal-name $n;
            let types_a = HashSet::from(type_cat);
            let types_n = HashSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);
            let left_right = LeftRightAnnotations {
                left_to_right: BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]),
                right_to_left: BTreeMap::from([(type_name.clone(), all_animals.clone())])
            };
            let mut tig = TypeInferenceGraph {
                vertices: HashMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_right)],
            };

            tig.run_type_inference();
            todo!();
        }


        // Case 2: $a isa animal, has cat-name $n;

        // Case 3: $a isa cat, has dog-name $n;


    }

}