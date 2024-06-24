/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet, HashMap};

use answer::variable::Variable;
use crate::{
    inference::type_inference::VertexConstraints,
};
use crate::inference::type_inference::TypeAnnotation;

// TODO: Resolve questions in the comment below & delete
/*
The basic algorithm for a single pattern (with nested disjunctions, e.g.) is implemented below.
It iteratively intersects the type annotations on vertices and with those on each constraint, and vice-versa.

We can model a function as a set of unary (i.e. VertexConstraints) constraints
    determined from the declared types, or by doing type-inference on it in isolation.
*/

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeInferenceGraph {
    pub(crate) vertices: VertexConstraints,
    pub(crate) edges: Vec<TypeInferenceEdge>,
    pub(crate) nested_graphs: Vec<NestedTypeInferenceGraph>,
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
pub(crate) struct TypeInferenceEdge {
    left: Variable,
    right: Variable,
    left_to_right: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
    right_to_left: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
}

impl TypeInferenceEdge {
    // Construction
    pub(crate) fn new(
        left: Variable,
        right: Variable,
        initial_left_to_right: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
        initial_right_to_left: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
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
        keys_from: &BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
        values_from: &BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
    ) -> BTreeSet<TypeAnnotation> {
        let mut types: BTreeSet<TypeAnnotation> = values_from.iter().flat_map(|(_, v)| v.clone().into_iter()).collect();
        types.retain(|v| keys_from.contains_key(&v));
        types
    }

    fn prune_keys_not_in_first_and_values_not_in_second(
        prune_from: &mut BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
        allowed_keys: &BTreeSet<TypeAnnotation>,
        allowed_values: &BTreeSet<TypeAnnotation>,
    ) {
        prune_from.retain(|type_, _| allowed_keys.contains(type_));
        for (_, v) in prune_from {
            v.retain(|type_| allowed_values.contains(type_));
        }
    }

    // Updates
    fn remove_type(&mut self, from_variable: Variable, type_: TypeAnnotation) {
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
        type_: &TypeAnnotation,
        remove_key: &mut BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
        remove_values: &mut BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
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
        remove_from_values_of: &mut BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
        for_key: &TypeAnnotation,
        value: &TypeAnnotation,
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
            let prune_left: Vec<TypeAnnotation> = self
                .left_to_right
                .iter()
                .filter_map(|(k, _)| if left_vertices.contains(k) { None } else { Some(k.clone()) })
                .collect();
            prune_left.into_iter().for_each(|type_| self.remove_type(self.left, type_));
        };
        {
            let right_vertices = vertices.get(&self.right).unwrap();
            let prune_right: Vec<TypeAnnotation> = self
                .right_to_left
                .iter()
                .filter_map(|(k, _)| if right_vertices.contains(k) { None } else { Some(k.clone()) })
                .collect();
            prune_right.into_iter().for_each(|type_| self.remove_type(self.right, type_))
        };
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NestedTypeInferenceGraph {
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
    use std::sync::Arc;

    use answer::variable::Variable;
    use encoding::graph::type_::Kind;
    use concept::thing::thing_manager::ThingManager;
    use concept::type_::annotation::AnnotationAbstract;
    use concept::type_::attribute_type::AttributeTypeAnnotation;
    use concept::type_::{Ordering, OwnerAPI};
    use concept::type_::type_manager::TypeManager;
    use durability::wal::WAL;
    use encoding::EncodingKeyspace;
    use encoding::graph::definition::definition_key_generator::DefinitionKeyGenerator;
    use encoding::graph::thing::vertex_generator::ThingVertexGenerator;
    use encoding::graph::type_::Kind;
    use encoding::graph::type_::vertex_generator::TypeVertexGenerator;
    use encoding::value::label::Label;
    use storage::durability_client::WALClient;
    use storage::MVCCStorage;
    use storage::snapshot::{CommittableSnapshot, ReadableSnapshot, WritableSnapshot, WriteSnapshot};
    use test_utils::{create_tmp_dir, init_logging};

    use crate::{
        inference::pattern_type_inference::{NestedTypeInferenceGraph, TypeInferenceEdge, TypeInferenceGraph},
    };
    use crate::inference::seed_types::seed_types;
    use crate::inference::type_inference::tests::tests__new_type;
    use crate::inference::type_inference::TypeAnnotation;
    use crate::inference::type_inference::TypeAnnotation::{SchemaTypeAttribute, SchemaTypeEntity};
    use crate::pattern::constraint::{Constraint, Has, Isa, Type};

    const LABEL_ANIMAL: &str = "animal";
    const LABEL_CAT: &str = "cat";
    const LABEL_DOG: &str = "dog";

    const LABEL_NAME: &str = "name";
    const LABEL_CATNAME: &str = "cat-name";
    const LABEL_DOGNAME: &str = "dog-name";


    fn setup_storage() -> Arc<MVCCStorage<WALClient>> {
        init_logging();
        let storage_path = create_tmp_dir();
        let wal = WAL::create(&storage_path).unwrap();
        let storage = Arc::new(
            MVCCStorage::<WALClient>::create::<EncodingKeyspace>("storage", &storage_path, WALClient::new(wal)).unwrap(),
        );

        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        TypeManager::<WriteSnapshot<WALClient>>::initialise_types(
            storage.clone(),
            definition_key_generator.clone(),
            type_vertex_generator.clone(),
        )
            .unwrap();
        storage
    }

    fn managers<Snapshot: ReadableSnapshot>(
        storage: Arc<MVCCStorage<WALClient>>,
    ) -> (Arc<TypeManager<Snapshot>>, ThingManager<Snapshot>) {
        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager =
            Arc::new(TypeManager::new(definition_key_generator.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());

        (type_manager, thing_manager)
    }

    fn setup_types<Snapshot: WritableSnapshot + CommittableSnapshot<WALClient>>(snapshot_: Snapshot, type_manager: &TypeManager<Snapshot>)
       -> (
            (TypeAnnotation, TypeAnnotation, TypeAnnotation),
            (TypeAnnotation, TypeAnnotation, TypeAnnotation)
        )
    {
        // dog sub animal, owns dog-name; cat sub animal owns cat-name;
        // cat-name sub animal-name; dog-name sub animal-name;
        let mut snapshot = snapshot_;

        let name = type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_NAME), false).unwrap();
        let catname = type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_CATNAME), false).unwrap();
        let dogname = type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_DOGNAME), false).unwrap();
        name.set_annotation(&mut snapshot, type_manager, AttributeTypeAnnotation::Abstract(AnnotationAbstract)).unwrap();
        catname.set_supertype(&mut snapshot, type_manager, name.clone()).unwrap();
        dogname.set_supertype(&mut snapshot, type_manager, name.clone()).unwrap();

        let animal = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_ANIMAL), false).unwrap();
        let cat = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_CAT), false).unwrap();
        let dog = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_DOG), false).unwrap();
        cat.set_supertype(&mut snapshot, type_manager, animal.clone()).unwrap();
        dog.set_supertype(&mut snapshot, type_manager, animal.clone()).unwrap();

        let animal_owns = animal.set_owns(&mut snapshot, type_manager, name.clone(), Ordering::Unordered).unwrap();
        let cat_owns = cat.set_owns(&mut snapshot, type_manager, catname.clone(), Ordering::Unordered).unwrap();
        let dog_owns = dog.set_owns(&mut snapshot, type_manager, dogname.clone(), Ordering::Unordered).unwrap();
        cat_owns.set_override(&mut snapshot, type_manager, animal_owns.clone()).unwrap();
        dog_owns.set_override(&mut snapshot, type_manager, animal_owns.clone()).unwrap();
        snapshot.commit().unwrap();


        (
            (SchemaTypeEntity(animal), SchemaTypeEntity(cat), SchemaTypeEntity(dog)),
            (SchemaTypeAttribute(name), SchemaTypeAttribute(catname), SchemaTypeAttribute(dogname))
        )
    }

    #[test]
    fn basic_binary_edges() {
        // Some version of `$a isa animal, has name $n;`
        let storage = setup_storage();
        let (type_manager, thing_manager) = managers(storage.clone());

        let (
            (type_animal, type_cat, type_dog),
            (type_name, type_catname, type_dogname)
        ) = setup_types(storage.clone().open_snapshot_write(), &type_manager);

        let all_animals = BTreeSet::from([type_animal.clone(), type_cat.clone(), type_dog.clone()]);
        let all_names = BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);

        let var_animal = Variable::new(0);
        let var_name = Variable::new(1);
        let var_animal_type = Variable::new(2);
        let var_name_type = Variable::new(3);

        {
            // Case 1: $a isa cat, has animal-name $n;
            let snapshot = storage.clone().open_snapshot_write();
            let constraints = vec![
                Constraint::Isa(Isa::new(var_animal, var_animal_type)),
                Constraint::Type(Type::new(var_animal_type, LABEL_CAT.to_owned())),

                Constraint::Isa(Isa::new(var_name, var_name_type)),
                Constraint::Type(Type::new(var_name_type, LABEL_NAME.to_owned())),

                Constraint::Has(Has::new(var_animal, var_name)),
            ];
            let mut tig = seed_types(&constraints, &snapshot, &type_manager);
            tig.run_type_inference();

            let expected_left_to_right = BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]);
            let expected_right_to_left = BTreeMap::from([(type_catname.clone(), BTreeSet::from([type_cat.clone()]))]);
            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone()])),
                    (var_animal_type, BTreeSet::from([type_cat.clone()])),
                    (var_name_type, BTreeSet::from([type_name.clone()])),
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
            let snapshot = storage.clone().open_snapshot_write();
            let constraints = vec![
                Constraint::Isa(Isa::new(var_animal, var_animal_type)),
                Constraint::Type(Type::new(var_animal_type, LABEL_ANIMAL.to_owned())),

                Constraint::Isa(Isa::new(var_name, var_name_type)),
                Constraint::Type(Type::new(var_name_type, LABEL_CATNAME.to_owned())),

                Constraint::Has(Has::new(var_animal, var_name)),
            ];
            let mut tig = seed_types(&constraints, &snapshot, &type_manager);
            tig.run_type_inference();

            let expected_left_to_right = BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]);
            let expected_right_to_left = BTreeMap::from([(type_catname.clone(), BTreeSet::from([type_cat.clone()]))]);
            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone()])),
                    (var_animal_type, BTreeSet::from([type_animal.clone()])),
                    (var_name_type, BTreeSet::from([type_catname.clone()])),
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
            let snapshot = storage.clone().open_snapshot_write();
            let constraints = vec![
                Constraint::Isa(Isa::new(var_animal, var_animal_type)),
                Constraint::Type(Type::new(var_animal_type, LABEL_CAT.to_owned())),

                Constraint::Isa(Isa::new(var_name, var_name_type)),
                Constraint::Type(Type::new(var_name_type, LABEL_DOGNAME.to_owned())),

                Constraint::Has(Has::new(var_animal, var_name)),
            ];
            let mut tig = seed_types(&constraints, &snapshot, &type_manager);
            tig.run_type_inference();

            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::new()),
                    (var_name, BTreeSet::new()),
                    (var_animal_type, BTreeSet::from([type_cat.clone()])),
                    (var_name_type, BTreeSet::from([type_dogname.clone()])),]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, BTreeMap::new(), BTreeMap::new())],
                nested_graphs: vec![],
            };
            assert_eq!(expected_tig, tig);
        }

        {
            // Case 4: $a isa animal, has name $n; // Just to be sure
            let types_a = all_animals.clone();
            let types_n = all_names.clone();
            let snapshot = storage.clone().open_snapshot_write();
            let constraints = vec![
                Constraint::Isa(Isa::new(var_animal, var_animal_type)),
                Constraint::Type(Type::new(var_animal_type, LABEL_ANIMAL.to_owned())),

                Constraint::Isa(Isa::new(var_name, var_name_type)),
                Constraint::Type(Type::new(var_name_type, LABEL_NAME.to_owned())),

                Constraint::Has(Has::new(var_animal, var_name)),
            ];
            let mut tig = seed_types(&constraints, &snapshot, &type_manager);
            tig.run_type_inference();


            let expected_left_to_right = BTreeMap::from([
                (type_animal.clone(), BTreeSet::from([type_name.clone()])),
                (type_cat.clone(), BTreeSet::from([type_catname.clone()])),
                (type_dog.clone(), BTreeSet::from([type_dogname.clone()])),
            ]);
            let expected_right_to_left = BTreeMap::from([
                (type_name.clone(), BTreeSet::from([type_animal.clone()])),
                (type_catname.clone(), BTreeSet::from([type_cat.clone()])),
                (type_dogname.clone(), BTreeSet::from([type_dog.clone()])),
            ]);
            let expected_tig = TypeInferenceGraph {
                vertices: BTreeMap::from([
                    (var_animal, types_a),
                    (var_name, types_n),
                    (var_animal_type, BTreeSet::from([type_animal.clone()])),
                    (var_name_type, BTreeSet::from([type_name.clone()])),
                ]),
                edges: vec![TypeInferenceEdge::new(var_animal, var_name, expected_left_to_right.clone(), expected_right_to_left.clone())],
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

        let type_animal = tests__new_type(Kind::Entity, 0);
        let type_cat = tests__new_type(Kind::Entity, 1);
        let type_dog = tests__new_type(Kind::Entity, 2);

        let type_name = tests__new_type(Kind::Attribute, 80);
        let type_catname = tests__new_type(Kind::Attribute, 81);
        let type_dogname = tests__new_type(Kind::Attribute, 82);

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
