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
    left_right_annotations: LeftRightAnnotations,
}

impl TypeInferenceEdge {

    // Construction
    fn new(left: Variable, right: Variable, initial_left_right_annotations: LeftRightAnnotations) -> TypeInferenceEdge {
        // The constructed support sets must be consistent with each other. i.e.
        //      left_support.keys() == left_to_right.keys() == flatten(right_to_left.values()) AND
        //      right_support.keys() == right_to_left.keys() == flatten(left_to_right.values())
        // This is a pre-condition to the type-inference loop.
        let mut left_right_annotations = initial_left_right_annotations;
        let left_types = Self::intersect_first_keys_with_union_of_second_values(&left_right_annotations.left_to_right, &left_right_annotations.right_to_left);
        let right_types = Self::intersect_first_keys_with_union_of_second_values(&left_right_annotations.right_to_left, &left_right_annotations.left_to_right);
        Self::prune_keys_not_in_first_and_values_not_in_second(&mut left_right_annotations.left_to_right, &left_types, &right_types);
        Self::prune_keys_not_in_first_and_values_not_in_second(&mut left_right_annotations.right_to_left, &right_types, &left_types);
        TypeInferenceEdge { left, right, left_right_annotations }
    }

    fn intersect_first_keys_with_union_of_second_values(keys_from: &BTreeMap<Type, BTreeSet<Type>>, values_from: &BTreeMap<Type, BTreeSet<Type>>) -> BTreeSet<Type> {
        let mut types: BTreeSet<Type> = values_from.iter().flat_map(|(_, v)| {
            v.clone().into_iter()
        }).collect();
        types.retain(|v| { keys_from.contains_key(&v) });
        types
    }

    fn prune_keys_not_in_first_and_values_not_in_second(prune_from: &mut BTreeMap<Type, BTreeSet<Type>>, allowed_keys: &BTreeSet<Type>, allowed_values: &BTreeSet<Type>) {
        prune_from.retain(|type_, _| allowed_keys.contains(type_));
        for (_, v) in prune_from {
            v.retain(|type_| allowed_values.contains(type_));
        }
    }

    // Updates
    fn remove_type(&mut self, from_variable: Variable, type_: Type) {
        let TypeInferenceEdge { left, right, left_right_annotations}  = self;
        if &from_variable == left {
            let LeftRightAnnotations { left_to_right, right_to_left} = left_right_annotations;
            Self::remove_type_from(&type_, left_to_right, right_to_left);
        } else if &from_variable == right {
            let LeftRightAnnotations { left_to_right, right_to_left} = left_right_annotations;
            Self::remove_type_from(&type_, right_to_left, left_to_right);
        } else {
            unreachable!("Bad argument. Expected variable to be {} or {}, but was {}", self.left, self.right, from_variable)
        }
    }

    fn remove_type_from(type_: &Type, remove_key: &mut BTreeMap<Type, BTreeSet<Type>>, remove_values: &mut BTreeMap<Type, BTreeSet<Type>>) {
        println!("Remove {:?} \n\tfrom keys of {:?} \n\tand values of {:?}", type_, remove_key, remove_values);
        for other_type in remove_key.get(&type_).unwrap() {
            let remaining_size = Self::remove_from_value_set(remove_values, other_type, type_);
            if 0 == remaining_size {
                remove_values.remove(&other_type);
            }
        }
        remove_key.remove(&type_);
    }

    fn remove_from_value_set(remove_from_values_of: &mut BTreeMap<Type, BTreeSet<Type>>, for_key: &Type, value: &Type) -> usize {
        let value_set_to_remove_from = remove_from_values_of.get_mut(&for_key).unwrap();
        value_set_to_remove_from.remove(&value);
        value_set_to_remove_from.len()
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
                let prune_left: Vec<Type> = edge.left_right_annotations.left_to_right.iter().filter_map(|(k, _)| {
                    if left_vertices.contains(k) { None } else { Some(k.clone()) }
                }).collect();
                prune_left.into_iter().for_each(|type_| { edge.remove_type(edge.left, type_) });
            }
            {
                let right_vertices = self.vertices.get_mut(&edge.right).unwrap();
                // let prune_right: Vec<Type> = (edge.right_support.keys() - right_vertices);
                let prune_right: Vec<Type> = edge.left_right_annotations.right_to_left.iter().filter_map(|(k, _)| {
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
                left_vertices.retain(|k| { edge.left_right_annotations.left_to_right.contains_key(k) });
                is_modified = is_modified || size_before != left_vertices.len();
            }
            {
                let right_vertices = self.vertices.get_mut(&edge.right).unwrap();
                let size_before = right_vertices.len();
                right_vertices.retain(|k| { edge.left_right_annotations.right_to_left.contains_key(k) });
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
            let types_n = all_names.clone();
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
            // todo!("assert_eq!(expected_tig, tig)");
        }


        {
            // Case 4: $a isa animal, has name $n; // Just to be sure
            let types_a = all_animals.clone();
            let types_n = all_names.clone();
            let left_right = LeftRightAnnotations {
                left_to_right: BTreeMap::from([
                    (type_cat.clone(), BTreeSet::from([type_catname.clone()])),
                    (type_dog.clone(), BTreeSet::from([type_dogname.clone()])),
                    (type_animal.clone(), BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]))
                ]),
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
        todo!("Check the results!!!")
    }
}
