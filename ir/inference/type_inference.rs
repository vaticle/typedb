/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use answer::{variable::Variable, Type};
use encoding::graph::definition::definition_key::DefinitionKey;

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

#[derive(Debug)]
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

#[derive(Debug)]
struct TypeInferenceGraph {
    vertices: BTreeMap<Variable, BTreeSet<Type>>,
    edges: Vec<TypeInferenceEdge>
}

#[derive(Debug)]
struct TypeInferenceEdge {
    left: Variable,
    right: Variable,
    left_support: BTreeMap<Type, usize>,
    right_support: BTreeMap<Type, usize>,

    left_right_annotations: LeftRightAnnotations,
}

impl TypeInferenceEdge {

    // Construction
    fn new(left: Variable, right: Variable, left_right_annotations: LeftRightAnnotations) -> TypeInferenceEdge {
        // The constructed support sets must be consistent with each other. i.e.
        //      left_support.keys() == left_to_right.keys() == flatten(right_to_left.values()) AND
        //      right_support.keys() == right_to_left.keys() == flatten(left_to_right.values())
        // This is a pre-condition to the type-inference loop.
        let mut left_support: BTreeMap<Type, usize> = BTreeMap::new();
        Self::populate_support(&mut left_support, &left_right_annotations.right_to_left, &left_right_annotations.left_to_right);

        let mut right_support: BTreeMap<Type, usize> = BTreeMap::new();
        Self::populate_support(&mut right_support, &left_right_annotations.left_to_right, &left_right_annotations.right_to_left);

        TypeInferenceEdge { left, right, left_support, right_support, left_right_annotations }
    }

    fn populate_support(support: &mut BTreeMap<Type, usize>, reverse_annotations: &BTreeMap<Type, BTreeSet<Type>>, annotations: &BTreeMap<Type, BTreeSet<Type>>) {
        // TODO: There is a bug because the support for the types is not correct in the final graph.
        for (_, types) in reverse_annotations {
            for type_ in types {
                if !annotations.contains_key(&type_) {continue;} // Don't even bother inserting
                if !support.contains_key(&type_) {
                    support.insert(type_.clone(), 0);
                }
                Self::update_support(support, &type_, 1);
            }
        }
    }

    // Updates
    fn remove_type(&mut self, from_variable: Variable, type_: Type) {
        let TypeInferenceEdge { left, right, left_support, right_support, left_right_annotations}  = self;
        if &from_variable == left {
            Self::remove_type_and_decrement_support(type_, left_support, right_support, &left_right_annotations.left_to_right)
        } else if &from_variable == right {
            Self::remove_type_and_decrement_support(type_, right_support, left_support, &left_right_annotations.right_to_left)
        } else {
            unreachable!("Bad argument. Expected variable to be {} or {}, but was {}", self.left, self.right, from_variable)
        }
    }

    fn remove_type_and_decrement_support(type_: Type, remove_from_side: &mut BTreeMap<Type, usize>, propagate_to_side: &mut BTreeMap<Type, usize>, annotations: &BTreeMap<Type, BTreeSet<Type>>) {
        println!("Remove {:?} \n\tfrom {:?} \n\tand {:?}", type_, remove_from_side, annotations);
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
    fn update_support(support_map: &mut BTreeMap<Type, usize>, type_: &Type, delta: isize) -> usize{
        debug_assert!(support_map.contains_key(&type_));
        let support = support_map.get_mut(&type_).unwrap();
        *support = ((*support as isize) + delta) as usize;
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
                // let prune_left: Vec<Type> = (edge.left_support.keys() - left_vertices);
                let prune_left: Vec<Type> = edge.left_support.iter().filter_map(|(k, _)| {
                    if left_vertices.contains(k) { None } else { Some(k.clone()) }
                }).collect();
                prune_left.into_iter().for_each(|type_| { edge.remove_type(edge.left, type_) });
            }
            {
                let right_vertices = self.vertices.get_mut(&edge.right).unwrap();
                // let prune_right: Vec<Type> = (edge.right_support.keys() - right_vertices);
                let prune_right: Vec<Type> = edge.right_support.iter().filter_map(|(k, _)| {
                    if right_vertices.contains(k) { None } else { Some(k.clone()) }
                }).collect();
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
    use answer::variable::Variable;

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

        let all_animals = BTreeSet::from([type_animal.clone(), type_cat.clone(), type_dog.clone()]);
        let all_names = BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);

        {
            // Case 1: $a isa cat, has animal-name $n;
            let types_a = BTreeSet::from([type_cat.clone()]);
            let types_n = BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);
            let left_right = LeftRightAnnotations {
                left_to_right: BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]),
                right_to_left: BTreeMap::from([
                    (type_name.clone(), all_animals.clone()),
                    (type_catname.clone(), BTreeSet::from([type_cat.clone()])),
                    (type_dogname.clone(), BTreeSet::from([type_dog.clone()]))
                ])
            };
            let mut tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_right)],
            };

            tig.run_type_inference();
            println!("{:?}", tig);
            // todo!("assert_eq!(expected_tig, tig)");
        }

        {
            // Case 2: $a isa animal, has cat-name $n;
            let types_a = all_animals.clone();
            let types_n = BTreeSet::from([type_catname.clone()]);
            let left_right = LeftRightAnnotations {
                left_to_right: BTreeMap::from([
                    (type_cat.clone(), BTreeSet::from([type_catname.clone()])),
                    (type_dog.clone(), BTreeSet::from([type_dogname.clone()])),
                    (type_animal.clone(), BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]))
                ]),
                right_to_left: BTreeMap::from([(type_catname.clone(), BTreeSet::from([type_cat.clone()]))]),
            };
            let mut tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_right)],
            };

            tig.run_type_inference();
            println!("{:?}", tig);
            // todo!("assert_eq!(expected_tig, tig)");
        }

        {
            // Case 3: $a isa cat, has dog-name $n;
            let types_a = BTreeSet::from([type_cat.clone()]);
            let types_n = BTreeSet::from([type_dogname.clone()]);
            let left_right = LeftRightAnnotations {
                left_to_right: BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]),
                right_to_left: BTreeMap::from([(type_dogname.clone(), BTreeSet::from([type_dog.clone()]))]),
            };
            let mut tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_right)],
            };

            tig.run_type_inference();
            println!("{:?}", tig);
            todo!("assert_eq!(expected_tig, tig)");
        }
        todo!("The three TODOs")
    }

}