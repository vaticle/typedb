/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    inference::type_inference::VertexConstraints,
    pattern::{constraint::Type, variable::Variable},
};

// TODO: Resolve questions in the comment below & delete
/*
The basic algorithm for a single pattern (with nested disjunctions, e.g.) is implemented below.
It iteratively intersects the type annotations on vertices and with those on each constraint, and vice-versa.

We can model a function as a set of unary (i.e. VertexConstraints) constraints
    determined from the declared types, or by doing type-inference on it in isolation.
*/

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeInferenceGraph {
    vertices: VertexConstraints,
    edges: Vec<TypeInferenceEdge>,
    nested_graphs: Vec<NestedTypeInferenceGraph>,
}

impl TypeInferenceGraph {
    fn run_type_inference(&mut self) {
        let mut is_modified = self.prune_vertices_from_constraints(); // We may need this as pre-condition
        while is_modified {
            self.prune_constraints_from_vertices();
            is_modified = self.prune_vertices_from_constraints();
        }
    }

    fn prune_constraints_from_vertices(&mut self) {
        for edge in &mut self.edges {
            edge.prune_self_from_vertices(&self.vertices)
        }
        for nested_graph in &mut self.nested_graphs {
            nested_graph.prune_self_from_vertices(&self.vertices)
        }
    }

    fn prune_vertices_from_constraints(&mut self) -> bool {
        let mut is_modified = false;
        for edge in &mut self.edges {
            is_modified = is_modified || edge.prune_vertices_from_self(&mut self.vertices);
        }
        for nested_graph in &mut self.nested_graphs {
            is_modified = is_modified || nested_graph.prune_vertices_from_self(&mut self.vertices);
        }
        is_modified
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeInferenceEdge {
    left: Variable,
    right: Variable,
    left_to_right: BTreeMap<Type, BTreeSet<Type>>,
    right_to_left: BTreeMap<Type, BTreeSet<Type>>,
}

impl TypeInferenceEdge {
    // Construction
    fn new(
        left: Variable,
        right: Variable,
        initial_left_to_right: BTreeMap<Type, BTreeSet<Type>>,
        initial_right_to_left: BTreeMap<Type, BTreeSet<Type>>,
    ) -> TypeInferenceEdge {
        // The final left_to_right & right_to_left sets must be consistent with each other. i.e.
        //      left_to_right.keys() == union(right_to_left.values()) AND
        //      right_to_left.keys() == union(left_to_right.values())
        // This is a pre-condition to the type-inference loop.
        let mut left_to_right = initial_left_to_right;
        let mut right_to_left = initial_right_to_left;
        let left_types = Self::intersect_first_keys_with_union_of_second_values(&left_to_right, &right_to_left);
        let right_types = Self::intersect_first_keys_with_union_of_second_values(&right_to_left, &left_to_right);
        Self::prune_keys_not_in_first_and_values_not_in_second(&mut left_to_right, &left_types, &right_types);
        Self::prune_keys_not_in_first_and_values_not_in_second(&mut right_to_left, &right_types, &left_types);
        TypeInferenceEdge { left, right, left_to_right, right_to_left }
    }

    fn intersect_first_keys_with_union_of_second_values(
        keys_from: &BTreeMap<Type, BTreeSet<Type>>,
        values_from: &BTreeMap<Type, BTreeSet<Type>>,
    ) -> BTreeSet<Type> {
        let mut types: BTreeSet<Type> = values_from.iter().flat_map(|(_, v)| v.clone().into_iter()).collect();
        types.retain(|v| keys_from.contains_key(&v));
        types
    }

    fn prune_keys_not_in_first_and_values_not_in_second(
        prune_from: &mut BTreeMap<Type, BTreeSet<Type>>,
        allowed_keys: &BTreeSet<Type>,
        allowed_values: &BTreeSet<Type>,
    ) {
        prune_from.retain(|type_, _| allowed_keys.contains(type_));
        for (_, v) in prune_from {
            v.retain(|type_| allowed_values.contains(type_));
        }
    }

    // Updates
    fn remove_type(&mut self, from_variable: Variable, type_: Type) {
        let TypeInferenceEdge { left, right, left_to_right, right_to_left } = self;
        if &from_variable == left {
            Self::remove_type_from(&type_, left_to_right, right_to_left);
        } else if &from_variable == right {
            Self::remove_type_from(&type_, right_to_left, left_to_right);
        } else {
            unreachable!(
                "Bad argument. Expected variable to be {} or {}, but was {}",
                self.left, self.right, from_variable
            )
        }
    }

    fn remove_type_from(
        type_: &Type,
        remove_key: &mut BTreeMap<Type, BTreeSet<Type>>,
        remove_values: &mut BTreeMap<Type, BTreeSet<Type>>,
    ) {
        for other_type in remove_key.get(&type_).unwrap() {
            let remaining_size = Self::remove_from_value_set(remove_values, other_type, type_);
            if 0 == remaining_size {
                remove_values.remove(&other_type);
            }
        }
        remove_key.remove(&type_);
    }

    fn remove_from_value_set(
        remove_from_values_of: &mut BTreeMap<Type, BTreeSet<Type>>,
        for_key: &Type,
        value: &Type,
    ) -> usize {
        let value_set_to_remove_from = remove_from_values_of.get_mut(&for_key).unwrap();
        value_set_to_remove_from.remove(&value);
        value_set_to_remove_from.len()
    }

    // prune_vertices
    fn prune_vertices_from_self(&self, vertices: &mut VertexConstraints) -> bool {
        let mut is_modified = false;
        {
            let left_vertices = vertices.get_mut(&self.left).unwrap();
            let size_before = left_vertices.len();
            left_vertices.retain(|k| self.left_to_right.contains_key(k));
            is_modified = is_modified || size_before != left_vertices.len();
        };
        {
            let right_vertices = vertices.get_mut(&self.right).unwrap();
            let size_before = right_vertices.len();
            right_vertices.retain(|k| self.right_to_left.contains_key(k));
            is_modified = is_modified || size_before != right_vertices.len();
        };
        is_modified
    }

    fn prune_self_from_vertices(&mut self, vertices: &VertexConstraints) {
        {
            let left_vertices = vertices.get(&self.left).unwrap();
            let prune_left: Vec<Type> = self
                .left_to_right
                .iter()
                .filter_map(|(k, _)| if left_vertices.contains(k) { None } else { Some(k.clone()) })
                .collect();
            prune_left.into_iter().for_each(|type_| self.remove_type(self.left, type_));
        };
        {
            let right_vertices = vertices.get(&self.right).unwrap();
            let prune_right: Vec<Type> = self
                .right_to_left
                .iter()
                .filter_map(|(k, _)| if right_vertices.contains(k) { None } else { Some(k.clone()) })
                .collect();
            prune_right.into_iter().for_each(|type_| self.remove_type(self.right, type_))
        };
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedTypeInferenceGraph {
    nested_graph_disjunction: Vec<TypeInferenceGraph>,
}

impl NestedTypeInferenceGraph {
    fn prune_self_from_vertices(&mut self, parent_vertices: &VertexConstraints) {
        for nested_graph in &mut self.nested_graph_disjunction {
            for (vertex, vertex_types) in &mut nested_graph.vertices {
                if let Some(parent_vertex_types) = parent_vertices.get(&vertex) {
                    vertex_types.retain(|type_| parent_vertex_types.contains(&type_))
                }
            }
            nested_graph.run_type_inference();
        }
    }

    fn prune_vertices_from_self(&self, parent_vertices: &mut VertexConstraints) -> bool {
        let mut is_modified = false;
        for (parent_vertex, parent_vertex_types) in parent_vertices {
            let size_before = parent_vertex_types.len();
            parent_vertex_types.retain(|type_| {
                self.nested_graph_disjunction.iter().any(|nested_graph| {
                    nested_graph
                        .vertices
                        .get(&parent_vertex)
                        .map(|nested_types| nested_types.contains(&type_))
                        .unwrap_or(true)
                })
            });
            is_modified = is_modified || size_before != parent_vertex_types.len();
        }
        is_modified
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::{
        inference::pattern_type_inference::{NestedTypeInferenceGraph, TypeInferenceEdge, TypeInferenceGraph},
        pattern::{constraint::tests::tests__new_type, variable::Variable},
    };

    #[test]
    fn basic_binary_edges() {
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
            let left_to_right = BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]);
            let right_to_left = BTreeMap::from([
                (type_name.clone(), BTreeSet::from([type_animal.clone()])),
                (type_catname.clone(), BTreeSet::from([type_cat.clone()])),
                (type_dogname.clone(), BTreeSet::from([type_dog.clone()])),
            ]);

            let mut tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_to_right.clone(), right_to_left.clone())],
                nested_graphs: vec![],
            };

            tig.run_type_inference();

            let expected_left_to_right = BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]);
            let expected_right_to_left = BTreeMap::from([(type_catname.clone(), BTreeSet::from([type_cat.clone()]))]);
            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone()])),
                ]),
                edges: vec![TypeInferenceEdge::new(
                    var_animal,
                    var_name,
                    expected_left_to_right,
                    expected_right_to_left,
                )],
                nested_graphs: vec![],
            };
            assert_eq!(expected_tig, tig);
        }

        {
            // Case 2: $a isa animal, has cat-name $n;
            let types_a = all_animals.clone();
            let types_n = BTreeSet::from([type_catname.clone()]);

            let left_to_right = BTreeMap::from([
                (type_animal.clone(), BTreeSet::from([type_name.clone()])),
                (type_cat.clone(), BTreeSet::from([type_catname.clone()])),
                (type_dog.clone(), BTreeSet::from([type_dogname.clone()])),
            ]);
            let right_to_left = BTreeMap::from([(type_catname.clone(), BTreeSet::from([type_cat.clone()]))]);

            let mut tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_to_right, right_to_left)],
                nested_graphs: vec![],
            };

            tig.run_type_inference();

            let expected_left_to_right = BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]);
            let expected_right_to_left = BTreeMap::from([(type_catname.clone(), BTreeSet::from([type_cat.clone()]))]);
            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone()])),
                ]),
                edges: vec![TypeInferenceEdge::new(
                    var_animal,
                    var_name,
                    expected_left_to_right,
                    expected_right_to_left,
                )],
                nested_graphs: vec![],
            };
            assert_eq!(expected_tig, tig);
        }

        {
            // Case 3: $a isa cat, has dog-name $n;
            let types_a = BTreeSet::from([type_cat.clone()]);
            let types_n = BTreeSet::from([type_dogname.clone()]);
            let left_to_right = BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]);
            let right_to_left = BTreeMap::from([(type_dogname.clone(), BTreeSet::from([type_dog.clone()]))]);
            let mut tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_to_right, right_to_left)],
                nested_graphs: vec![],
            };

            tig.run_type_inference();

            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, BTreeSet::new()), (var_name, BTreeSet::new())]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, BTreeMap::new(), BTreeMap::new())],
                nested_graphs: vec![],
            };
            assert_eq!(expected_tig, tig);
        }

        {
            // Case 4: $a isa animal, has name $n; // Just to be sure
            let types_a = all_animals.clone();
            let types_n = all_names.clone();

            let left_to_right = BTreeMap::from([
                (type_animal.clone(), BTreeSet::from([type_name.clone()])),
                (type_cat.clone(), BTreeSet::from([type_catname.clone()])),
                (type_dog.clone(), BTreeSet::from([type_dogname.clone()])),
            ]);
            let right_to_left = BTreeMap::from([
                (type_name.clone(), BTreeSet::from([type_animal.clone()])),
                (type_catname.clone(), BTreeSet::from([type_cat.clone()])),
                (type_dogname.clone(), BTreeSet::from([type_dog.clone()])),
            ]);

            let mut tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a.clone()), (var_name, types_n.clone())]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_to_right.clone(), right_to_left.clone())],
                nested_graphs: vec![],
            };

            tig.run_type_inference();

            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n)]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_to_right.clone(), right_to_left.clone())],
                nested_graphs: vec![],
            };
            assert_eq!(expected_tig, tig);
        }
    }

    #[test]
    fn basic_nested_graphs() {
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
            // Case 1: {$a isa cat;} or {$a isa dog;} $a has animal-name $n;
            let branch_1_graph = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, BTreeSet::from([type_cat.clone()]))]),
                edges: vec![],
                nested_graphs: vec![],
            };
            let branch_2_graph = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, BTreeSet::from([type_dog.clone()]))]),
                edges: vec![],
                nested_graphs: vec![],
            };

            let left_to_right = BTreeMap::from([
                (type_animal.clone(), BTreeSet::from([type_name.clone()])),
                (type_cat.clone(), BTreeSet::from([type_catname.clone()])),
                (type_dog.clone(), BTreeSet::from([type_dogname.clone()])),
            ]);
            let right_to_left = BTreeMap::from([
                (type_name.clone(), BTreeSet::from([type_animal.clone()])),
                (type_catname.clone(), BTreeSet::from([type_cat.clone()])),
                (type_dogname.clone(), BTreeSet::from([type_dog.clone()])),
            ]);
            let mut top_level_graph = TypeInferenceGraph {
                vertices: BTreeMap::from([(var_animal, all_animals.clone()), (var_name, all_names.clone())]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_to_right, right_to_left)],
                nested_graphs: vec![NestedTypeInferenceGraph {
                    nested_graph_disjunction: vec![branch_1_graph.clone(), branch_2_graph.clone()],
                }],
            };
            top_level_graph.run_type_inference();

            let expected_left_to_right = BTreeMap::from([
                (type_cat.clone(), BTreeSet::from([type_catname.clone()])),
                (type_dog.clone(), BTreeSet::from([type_dogname.clone()])),
            ]);
            let expected_right_to_left = BTreeMap::from([
                (type_catname.clone(), BTreeSet::from([type_cat.clone()])),
                (type_dogname.clone(), BTreeSet::from([type_dog.clone()])),
            ]);
            let expected_graph = TypeInferenceGraph {
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone(), type_dog.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone(), type_dogname.clone()])),
                ]),
                edges: vec![TypeInferenceEdge::new(
                    var_animal,
                    var_name,
                    expected_left_to_right,
                    expected_right_to_left,
                )],
                nested_graphs: vec![NestedTypeInferenceGraph {
                    nested_graph_disjunction: vec![branch_1_graph.clone(), branch_2_graph.clone()],
                }],
            };
            assert_eq!(expected_graph, top_level_graph);
        }
    }
}
