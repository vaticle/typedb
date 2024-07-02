/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet};

use answer::variable::Variable;

use crate::{
    inference::type_inference::{TypeAnnotation, VertexAnnotations},
    pattern::{conjunction::Conjunction, constraint::Constraint},
};

/*
The basic algorithm for a single pattern (with nested disjunctions, e.g.) is implemented below.
It iteratively intersects the type annotations on vertices and with those on each constraint, and vice-versa.

We can model a function as a set of unary (i.e. VertexConstraints) constraints
    determined from the declared types, or by doing type-inference on it in isolation.
*/

fn run_type_inference<'graph>(tig: &mut TypeInferenceGraph<'graph>) {
    let mut is_modified = tig.prune_vertices_from_constraints();
    while is_modified {
        tig.prune_constraints_from_vertices();
        is_modified = tig.prune_vertices_from_constraints();
    }

    // Then do it for the nested negations & optionals
    tig.nested_negations.iter_mut().for_each(|nested| run_type_inference(nested));
    tig.nested_optionals.iter_mut().for_each(|nested| run_type_inference(nested));
}

#[derive(Debug)]
pub struct TypeInferenceGraph<'this> {
    pub(crate) conjunction: &'this Conjunction,
    pub(crate) vertices: VertexAnnotations,
    pub(crate) edges: Vec<TypeInferenceEdge<'this>>,
    pub(crate) nested_disjunctions: Vec<NestedTypeInferenceGraphDisjunction<'this>>,
    pub(crate) nested_negations: Vec<TypeInferenceGraph<'this>>,
    pub(crate) nested_optionals: Vec<TypeInferenceGraph<'this>>,
}

impl<'this> TypeInferenceGraph<'this> {
    fn prune_constraints_from_vertices(&mut self) {
        for edge in &mut self.edges {
            edge.prune_self_from_vertices(&self.vertices)
        }
        for nested_graph in &mut self.nested_disjunctions {
            nested_graph.prune_self_from_vertices(&self.vertices)
        }
    }

    fn prune_vertices_from_constraints(&mut self) -> bool {
        let mut is_modified = false;
        for edge in &mut self.edges {
            is_modified = is_modified || edge.prune_vertices_from_self(&mut self.vertices);
        }
        for nested_graph in &mut self.nested_disjunctions {
            is_modified = is_modified || nested_graph.prune_vertices_from_self(&mut self.vertices);
        }
        is_modified
    }
}

#[derive(Debug)]

pub struct TypeInferenceEdge<'this> {
    pub(crate) constraint: &'this Constraint<Variable>,
    pub(crate) left: Variable,
    pub(crate) right: Variable,
    pub(crate) left_to_right: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
    pub(crate) right_to_left: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
}

impl<'this> TypeInferenceEdge<'this> {
    // Construction

    pub(crate) fn build(
        constraint: &'this Constraint<Variable>,
        left: Variable,
        right: Variable,
        initial_left_to_right: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
        initial_right_to_left: BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>,
    ) -> TypeInferenceEdge<'this> {
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
        TypeInferenceEdge { constraint, left, right, left_to_right, right_to_left }
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
        let TypeInferenceEdge { constraint, left, right, left_to_right, right_to_left } = self;
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
    fn prune_vertices_from_self(&self, vertices: &mut VertexAnnotations) -> bool {
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

    fn prune_self_from_vertices(&mut self, vertices: &VertexAnnotations) {
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

#[derive(Debug)]
pub(crate) struct NestedTypeInferenceGraphDisjunction<'this> {
    pub(crate) disjunction: Vec<TypeInferenceGraph<'this>>,
    pub(crate) shared_variables: BTreeSet<Variable>,
    pub(crate) shared_vertex_annotations: BTreeMap<Variable, BTreeSet<TypeAnnotation>>,
}

impl<'this> NestedTypeInferenceGraphDisjunction<'this> {
    fn prune_self_from_vertices<'a>(&mut self, parent_vertices: &VertexAnnotations) {
        for nested_graph in &mut self.disjunction {
            for (vertex, vertex_types) in &mut nested_graph.vertices {
                if let Some(parent_vertex_types) = parent_vertices.get(&vertex) {
                    vertex_types.retain(|type_| parent_vertex_types.contains(&type_))
                }
            }
            nested_graph.prune_constraints_from_vertices();
        }
    }

    fn prune_vertices_from_self<'a>(&mut self, parent_vertices: &mut VertexAnnotations) -> bool {
        let mut is_modified = false;
        for nested_graph in &mut self.disjunction {
            nested_graph.prune_vertices_from_constraints();
        }

        for (parent_vertex, parent_vertex_types) in parent_vertices {
            let size_before = parent_vertex_types.len();
            parent_vertex_types.retain(|type_| {
                self.disjunction.iter().any(|nested_graph| {
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

    use std::{
        collections::{BTreeMap, BTreeSet},
        sync::Arc,
    };

    use answer::variable::Variable;
    use concept::{
        thing::thing_manager::ThingManager,
        type_::{
            annotation::AnnotationAbstract, attribute_type::AttributeTypeAnnotation, type_manager::TypeManager,
            Ordering, OwnerAPI, PlayerAPI,
        },
    };
    use durability::wal::WAL;
    use encoding::{
        graph::{
            definition::definition_key_generator::DefinitionKeyGenerator,
            thing::vertex_generator::ThingVertexGenerator, type_::vertex_generator::TypeVertexGenerator,
        },
        value::label::Label,
        EncodingKeyspace,
    };
    use itertools::Itertools;
    use storage::{
        durability_client::WALClient,
        snapshot::{CommittableSnapshot, ReadableSnapshot, WritableSnapshot, WriteSnapshot},
        MVCCStorage,
    };
    use test_utils::{create_tmp_dir, init_logging};

    use crate::{
        inference::{
            pattern_type_inference::{
                run_type_inference, NestedTypeInferenceGraphDisjunction, TypeInferenceEdge, TypeInferenceGraph,
            },
            seed_types::TypeSeeder,
            type_inference::{
                TypeAnnotation,
                TypeAnnotation::{SchemaTypeAttribute, SchemaTypeEntity, SchemaTypeRelation, SchemaTypeRole},
            },
        },
        pattern::{conjunction::Conjunction, constraint::Constraint},
    };

    const LABEL_ANIMAL: &str = "animal";
    const LABEL_CAT: &str = "cat";
    const LABEL_DOG: &str = "dog";

    const LABEL_NAME: &str = "name";
    const LABEL_CATNAME: &str = "cat-name";
    const LABEL_DOGNAME: &str = "dog-name";

    const LABEL_FEARS: &str = "fears";
    const LABEL_HAS_FEAR: &str = "has-fear";
    const LABEL_IS_FEARED: &str = "is-feared";

    impl<'this> PartialEq<Self> for TypeInferenceEdge<'this> {
        fn eq(&self, other: &Self) -> bool {
            self.constraint == other.constraint
                && self.right == other.right
                && self.left == other.left
                && self.left_to_right == other.left_to_right
                && self.right_to_left == other.right_to_left
        }
    }

    impl<'this> Eq for TypeInferenceEdge<'this> {}

    impl<'this> PartialEq<Self> for TypeInferenceGraph<'this> {
        fn eq(&self, other: &Self) -> bool {
            self.vertices == other.vertices
                && self.edges == other.edges
                && self.nested_disjunctions == other.nested_disjunctions
        }
    }

    impl<'this> Eq for TypeInferenceGraph<'this> {}

    impl<'this> PartialEq<Self> for NestedTypeInferenceGraphDisjunction<'this> {
        fn eq(&self, other: &Self) -> bool {
            self.disjunction == other.disjunction
        }
    }

    impl<'this> Eq for NestedTypeInferenceGraphDisjunction<'this> {}

    pub(crate) fn expected_edge(
        constraint: &Constraint<Variable>,
        left: Variable,
        right: Variable,
        left_right_type_pairs: Vec<(TypeAnnotation, TypeAnnotation)>,
    ) -> TypeInferenceEdge {
        let mut left_to_right = BTreeMap::new();
        let mut right_to_left = BTreeMap::new();
        for (l, r) in left_right_type_pairs {
            if !left_to_right.contains_key(&l) {
                left_to_right.insert(l.clone(), BTreeSet::new());
            }
            left_to_right.get_mut(&l).unwrap().insert(r.clone());
            if !right_to_left.contains_key(&r) {
                right_to_left.insert(r.clone(), BTreeSet::new());
            }
            right_to_left.get_mut(&r).unwrap().insert(l.clone());
        }
        TypeInferenceEdge { constraint, left, right, left_to_right, right_to_left }
    }

    fn setup_storage() -> Arc<MVCCStorage<WALClient>> {
        init_logging();
        let storage_path = create_tmp_dir();
        let wal = WAL::create(&storage_path).unwrap();
        let storage = Arc::new(
            MVCCStorage::<WALClient>::create::<EncodingKeyspace>("storage", &storage_path, WALClient::new(wal))
                .unwrap(),
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

    fn managers<Snapshot: ReadableSnapshot>() -> (Arc<TypeManager<Snapshot>>, ThingManager<Snapshot>) {
        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager =
            Arc::new(TypeManager::new(definition_key_generator.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());

        (type_manager, thing_manager)
    }

    fn setup_types<Snapshot: WritableSnapshot + CommittableSnapshot<WALClient>>(
        snapshot_: Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> (
        (TypeAnnotation, TypeAnnotation, TypeAnnotation),
        (TypeAnnotation, TypeAnnotation, TypeAnnotation),
        (TypeAnnotation, TypeAnnotation, TypeAnnotation),
    ) {
        // dog sub animal, owns dog-name; cat sub animal owns cat-name;
        // cat-name sub animal-name; dog-name sub animal-name;
        let mut snapshot = snapshot_;

        // Attributes
        let name = type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_NAME), false).unwrap();
        let catname = type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_CATNAME), false).unwrap();
        let dogname = type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_DOGNAME), false).unwrap();
        name.set_annotation(&mut snapshot, type_manager, AttributeTypeAnnotation::Abstract(AnnotationAbstract))
            .unwrap();
        catname.set_supertype(&mut snapshot, type_manager, name.clone()).unwrap();
        dogname.set_supertype(&mut snapshot, type_manager, name.clone()).unwrap();

        // Entities
        let animal = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_ANIMAL), false).unwrap();
        let cat = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_CAT), false).unwrap();
        let dog = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_DOG), false).unwrap();
        cat.set_supertype(&mut snapshot, type_manager, animal.clone()).unwrap();
        dog.set_supertype(&mut snapshot, type_manager, animal.clone()).unwrap();

        // Ownerships
        let animal_owns = animal.set_owns(&mut snapshot, type_manager, name.clone(), Ordering::Unordered).unwrap();
        let cat_owns = cat.set_owns(&mut snapshot, type_manager, catname.clone(), Ordering::Unordered).unwrap();
        let dog_owns = dog.set_owns(&mut snapshot, type_manager, dogname.clone(), Ordering::Unordered).unwrap();
        cat_owns.set_override(&mut snapshot, type_manager, animal_owns.clone()).unwrap();
        dog_owns.set_override(&mut snapshot, type_manager, animal_owns.clone()).unwrap();

        // Relations
        let fears = type_manager.create_relation_type(&mut snapshot, &Label::build(LABEL_FEARS), false).unwrap();
        let has_fear = fears.create_relates(&mut snapshot, &type_manager, LABEL_HAS_FEAR, Ordering::Unordered).unwrap();
        let is_feared =
            fears.create_relates(&mut snapshot, &type_manager, LABEL_IS_FEARED, Ordering::Unordered).unwrap();
        cat.set_plays(&mut snapshot, &type_manager, has_fear.clone());
        dog.set_plays(&mut snapshot, &type_manager, is_feared.clone());

        snapshot.commit().unwrap();

        (
            (SchemaTypeEntity(animal), SchemaTypeEntity(cat), SchemaTypeEntity(dog)),
            (SchemaTypeAttribute(name), SchemaTypeAttribute(catname), SchemaTypeAttribute(dogname)),
            (SchemaTypeRelation(fears), SchemaTypeRole(has_fear), SchemaTypeRole(is_feared)),
        )
    }

    #[test]
    fn basic_binary_edges() {
        // Some version of `$a isa animal, has name $n;`
        let storage = setup_storage();
        let (type_manager, thing_manager) = managers();

        let ((type_animal, type_cat, type_dog), (type_name, type_catname, type_dogname), _) =
            setup_types(storage.clone().open_snapshot_write(), &type_manager);

        let all_animals = BTreeSet::from([type_animal.clone(), type_cat.clone(), type_dog.clone()]);
        let all_names = BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);

        {
            // Case 1: $a isa cat, has animal-name $n;
            let snapshot = storage.clone().open_snapshot_write();
            let mut conjunction = Conjunction::new_root();
            let (var_animal, var_name, var_animal_type, var_name_type) = ["animal", "name", "animal_type", "name_type"]
                .iter()
                .map(|name| conjunction.get_or_declare_variable(*name).unwrap())
                .collect_tuple()
                .unwrap();

            conjunction.constraints_mut().add_isa(var_animal, var_animal_type).unwrap();
            conjunction.constraints_mut().add_type(var_animal_type, LABEL_CAT).unwrap();
            conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
            conjunction.constraints_mut().add_type(var_name_type, LABEL_NAME).unwrap();
            conjunction.constraints_mut().add_has(var_animal, var_name).unwrap();
            let constraints = &conjunction.constraints().constraints;

            let mut tig = TypeSeeder::new(&snapshot, &type_manager).seed_types(&conjunction);
            run_type_inference(&mut tig);

            let expected_tig = TypeInferenceGraph {
                conjunction: &conjunction,
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone()])),
                    (var_animal_type, BTreeSet::from([type_cat.clone()])),
                    (var_name_type, BTreeSet::from([type_name.clone()])),
                ]),
                edges: vec![
                    expected_edge(
                        &constraints[0],
                        var_animal,
                        var_animal_type,
                        vec![(type_cat.clone(), type_cat.clone())],
                    ),
                    expected_edge(
                        &constraints[2],
                        var_name,
                        var_name_type,
                        vec![(type_catname.clone(), type_name.clone())],
                    ),
                    expected_edge(
                        &constraints[4],
                        var_animal,
                        var_name,
                        vec![(type_cat.clone(), type_catname.clone())],
                    ),
                ],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            };

            assert_eq!(expected_tig, tig);
        }

        {
            // Case 2: $a isa animal, has cat-name $n;
            let snapshot = storage.clone().open_snapshot_write();
            let mut conjunction = Conjunction::new_root();
            let (var_animal, var_name, var_animal_type, var_name_type) = ["animal", "name", "animal_type", "name_type"]
                .iter()
                .map(|name| conjunction.get_or_declare_variable(*name).unwrap())
                .collect_tuple()
                .unwrap();

            conjunction.constraints_mut().add_isa(var_animal, var_animal_type).unwrap();
            conjunction.constraints_mut().add_type(var_animal_type, LABEL_ANIMAL).unwrap();
            conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
            conjunction.constraints_mut().add_type(var_name_type, LABEL_CATNAME).unwrap();
            conjunction.constraints_mut().add_has(var_animal, var_name).unwrap();
            let constraints = &conjunction.constraints().constraints;
            let mut tig = TypeSeeder::new(&snapshot, &type_manager).seed_types(&conjunction);
            run_type_inference(&mut tig);

            let expected_tig = TypeInferenceGraph {
                conjunction: &conjunction,
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone()])),
                    (var_animal_type, BTreeSet::from([type_animal.clone()])),
                    (var_name_type, BTreeSet::from([type_catname.clone()])),
                ]),
                edges: vec![
                    expected_edge(
                        &constraints[0],
                        var_animal,
                        var_animal_type,
                        vec![(type_cat.clone(), type_animal.clone())],
                    ),
                    expected_edge(
                        &constraints[2],
                        var_name,
                        var_name_type,
                        vec![(type_catname.clone(), type_catname.clone())],
                    ),
                    expected_edge(
                        &constraints[4],
                        var_animal,
                        var_name,
                        vec![(type_cat.clone(), type_catname.clone())],
                    ),
                ],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            };
            assert_eq!(expected_tig, tig);
        }

        {
            // Case 3: $a isa cat, has dog-name $n;
            let snapshot = storage.clone().open_snapshot_write();
            let mut conjunction = Conjunction::new_root();
            let (var_animal, var_name, var_animal_type, var_name_type) = ["animal", "name", "animal_type", "name_type"]
                .iter()
                .map(|name| conjunction.get_or_declare_variable(*name).unwrap())
                .collect_tuple()
                .unwrap();

            conjunction.constraints_mut().add_isa(var_animal, var_animal_type).unwrap();
            conjunction.constraints_mut().add_type(var_animal_type, LABEL_CAT).unwrap();
            conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
            conjunction.constraints_mut().add_type(var_name_type, LABEL_DOGNAME).unwrap();
            conjunction.constraints_mut().add_has(var_animal, var_name).unwrap();

            let constraints = &conjunction.constraints().constraints;
            let mut tig = TypeSeeder::new(&snapshot, &type_manager).seed_types(&conjunction);
            run_type_inference(&mut tig);

            let expected_tig = TypeInferenceGraph {
                conjunction: &conjunction,
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::new()),
                    (var_name, BTreeSet::new()),
                    (var_animal_type, BTreeSet::new()),
                    (var_name_type, BTreeSet::new()),
                ]),
                edges: vec![
                    expected_edge(&constraints[0], var_animal, var_animal_type, vec![]),
                    expected_edge(&constraints[2], var_name, var_name_type, vec![]),
                    expected_edge(&constraints[4], var_animal, var_name, vec![]),
                ],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            };
            assert_eq!(expected_tig, tig);
        }

        {
            // Case 4: $a isa animal, has name $n; // Just to be sure
            let types_a = all_animals.clone();
            let types_n = all_names.clone();
            let snapshot = storage.clone().open_snapshot_write();
            let mut conjunction = Conjunction::new_root();
            let (var_animal, var_name, var_animal_type, var_name_type) = ["animal", "name", "animal_type", "name_type"]
                .iter()
                .map(|name| conjunction.get_or_declare_variable(*name).unwrap())
                .collect_tuple()
                .unwrap();

            conjunction.constraints_mut().add_isa(var_animal, var_animal_type).unwrap();
            conjunction.constraints_mut().add_type(var_animal_type, LABEL_ANIMAL).unwrap();
            conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
            conjunction.constraints_mut().add_type(var_name_type, LABEL_NAME).unwrap();
            conjunction.constraints_mut().add_has(var_animal, var_name).unwrap();
            let constraints = &conjunction.constraints().constraints;
            let mut tig = TypeSeeder::new(&snapshot, &type_manager).seed_types(&conjunction);
            run_type_inference(&mut tig);

            let expected_tig = TypeInferenceGraph {
                conjunction: &conjunction,
                vertices: BTreeMap::from([
                    (var_animal, types_a),
                    (var_name, types_n),
                    (var_animal_type, BTreeSet::from([type_animal.clone()])),
                    (var_name_type, BTreeSet::from([type_name.clone()])),
                ]),
                edges: vec![
                    expected_edge(
                        &constraints[0],
                        var_animal,
                        var_animal_type,
                        vec![
                            (type_cat.clone(), type_animal.clone()),
                            (type_dog.clone(), type_animal.clone()),
                            (type_animal.clone(), type_animal.clone()),
                        ],
                    ),
                    expected_edge(
                        &constraints[2],
                        var_name,
                        var_name_type,
                        vec![
                            (type_catname.clone(), type_name.clone()),
                            (type_dogname.clone(), type_name.clone()),
                            (type_name.clone(), type_name.clone()),
                        ],
                    ),
                    expected_edge(
                        &constraints[4],
                        var_animal,
                        var_name,
                        vec![
                            (type_cat.clone(), type_catname.clone()),
                            (type_dog.clone(), type_dogname.clone()),
                            (type_animal.clone(), type_name.clone()),
                        ],
                    ),
                ],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            };
            assert_eq!(expected_tig, tig);
        }
    }

    #[test]
    fn basic_nested_graphs() {
        // Some version of `$a isa animal, has name $n;`
        let storage = setup_storage();
        let (type_manager, thing_manager) = managers();

        let ((type_animal, type_cat, type_dog), (type_name, type_catname, type_dogname), _) =
            setup_types(storage.clone().open_snapshot_write(), &type_manager);

        let all_animals = BTreeSet::from([type_animal.clone(), type_cat.clone(), type_dog.clone()]);
        let all_names = BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);

        let mut root_conj = Conjunction::new_root();
        let (var_animal, var_name, var_name_type) = ["animal", "name", "name_type"]
            .iter()
            .map(|name| root_conj.get_or_declare_variable(*name).unwrap())
            .collect_tuple()
            .unwrap();
        {
            // Case 1: {$a isa cat;} or {$a isa dog;} $a has animal-name $n;

            let (b1_var_animal_type, b2_var_animal_type) = {
                let disj = root_conj.patterns_mut().add_disjunction();

                let mut branch1 = disj.add_conjunction();
                let b1_var_animal_type = branch1.get_or_declare_variable("b1_animal_type").unwrap();
                branch1.constraints_mut().add_isa(var_animal, b1_var_animal_type).unwrap();
                branch1.constraints_mut().add_type(b1_var_animal_type, LABEL_CAT).unwrap();

                let mut branch2 = disj.add_conjunction();
                let b2_var_animal_type = branch2.get_or_declare_variable("b2_animal_type").unwrap();
                branch2.constraints_mut().add_isa(var_animal, b2_var_animal_type).unwrap();
                branch2.constraints_mut().add_type(b2_var_animal_type, LABEL_DOG).unwrap();

                (b1_var_animal_type, b2_var_animal_type)
            };
            root_conj.constraints_mut().add_type(var_name_type, "name").unwrap();
            root_conj.constraints_mut().add_isa(var_name, var_name_type).unwrap();
            root_conj.constraints_mut().add_has(var_animal, var_name).unwrap();

            let snapshot = storage.clone().open_snapshot_write();
            let mut tig = TypeSeeder::new(&snapshot, &type_manager).seed_types(&root_conj);
            run_type_inference(&mut tig);

            let disj = root_conj.patterns().patterns.get(0).unwrap().as_disjunction().unwrap();
            let b1 = disj.conjunctions().get(0).unwrap();
            let b2 = disj.conjunctions().get(1).unwrap();
            let b1_isa = &b1.constraints().constraints[0];
            let b2_isa = &b2.constraints().constraints[0];
            let mut expected_nested_graphs: Vec<TypeInferenceGraph> = Vec::new();
            expected_nested_graphs.push(TypeInferenceGraph {
                conjunction: b1,
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone()])),
                    (b1_var_animal_type, BTreeSet::from([type_cat.clone()])),
                ]),
                edges: vec![expected_edge(
                    b1_isa,
                    var_animal,
                    b1_var_animal_type,
                    vec![(type_cat.clone(), type_cat.clone())],
                )],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            });
            expected_nested_graphs.push(TypeInferenceGraph {
                conjunction: b2,
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_dog.clone()])),
                    (b2_var_animal_type, BTreeSet::from([type_dog.clone()])),
                ]),
                edges: vec![expected_edge(
                    b2_isa,
                    var_animal,
                    b2_var_animal_type,
                    vec![(type_dog.clone(), type_dog.clone())],
                )],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            });
            let expected_graph = TypeInferenceGraph {
                conjunction: &root_conj,
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_cat.clone(), type_dog.clone()])),
                    (var_name, BTreeSet::from([type_catname.clone(), type_dogname.clone()])),
                    (var_name_type, BTreeSet::from([type_name.clone()])),
                ]),
                edges: vec![
                    expected_edge(
                        &root_conj.constraints().constraints[1],
                        var_name,
                        var_name_type,
                        vec![(type_catname.clone(), type_name.clone()), (type_dogname.clone(), type_name.clone())],
                    ),
                    expected_edge(
                        &root_conj.constraints().constraints[2],
                        var_animal,
                        var_name,
                        vec![(type_cat.clone(), type_catname.clone()), (type_dog.clone(), type_dogname.clone())],
                    ),
                ],
                nested_disjunctions: vec![NestedTypeInferenceGraphDisjunction {
                    disjunction: expected_nested_graphs,
                    shared_variables: BTreeSet::new(),
                    shared_vertex_annotations: BTreeMap::new(),
                }],
                nested_negations: vec![],
                nested_optionals: vec![],
            };

            assert_eq!(expected_graph, tig);
        }
    }

    #[test]
    fn no_type_constraints() {
        let storage = setup_storage();
        let (type_manager, thing_manager) = managers();

        let ((type_animal, type_cat, type_dog), (type_name, type_catname, type_dogname), _) =
            setup_types(storage.clone().open_snapshot_write(), &type_manager);

        let all_animals = BTreeSet::from([type_animal.clone(), type_cat.clone(), type_dog.clone()]);
        let all_names = BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);

        let mut root_conj = Conjunction::new_root();
        let (var_animal, var_name, var_name_type) = ["animal", "name", "name_type"]
            .iter()
            .map(|name| root_conj.get_or_declare_variable(*name).unwrap())
            .collect_tuple()
            .unwrap();

        {
            // Case 1: $a has $n;
            let snapshot = storage.clone().open_snapshot_write();
            let mut conjunction = Conjunction::new_root();
            let (var_animal, var_name) = ["animal", "name"]
                .iter()
                .map(|name| conjunction.get_or_declare_variable(*name).unwrap())
                .collect_tuple()
                .unwrap();

            conjunction.constraints_mut().add_has(var_animal, var_name).unwrap();

            let constraints = &conjunction.constraints().constraints;
            let mut tig = TypeSeeder::new(&snapshot, &type_manager).seed_types(&conjunction);
            run_type_inference(&mut tig);

            let expected_tig = TypeInferenceGraph {
                conjunction: &conjunction,
                vertices: BTreeMap::from([
                    (var_animal, BTreeSet::from([type_animal.clone(), type_cat.clone(), type_dog.clone()])),
                    (var_name, BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()])),
                ]),
                edges: vec![expected_edge(
                    &constraints[0],
                    var_animal,
                    var_name,
                    vec![
                        (type_animal.clone(), type_name.clone()),
                        (type_cat, type_catname.clone()),
                        (type_dog, type_dogname.clone()),
                    ],
                )],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            };

            assert_eq!(expected_tig, tig);
        }
    }

    #[test]
    fn role_players() {
        let storage = setup_storage();
        let (type_manager, thing_manager) = managers();

        let ((type_animal, type_cat, type_dog), _, (type_fears, type_has_fear, type_is_feared)) =
            setup_types(storage.clone().open_snapshot_write(), &type_manager);

        {
            // With roles specified
            let snapshot = storage.clone().open_snapshot_write();
            let mut conjunction = Conjunction::new_root();
            let (
                var_has_fear,
                var_is_feared,
                var_fears_type,
                var_fears,
                var_role_1,
                var_role_2,
                var_role_1_type,
                var_role_2_type,
            ) = ["has_fear", "is_feared", "fears_type", "fears", "role1", "role2", "role1_type", "role2_type"]
                .iter()
                .map(|name| conjunction.get_or_declare_variable(*name).unwrap())
                .collect_tuple()
                .unwrap();

            conjunction.constraints_mut().add_isa(var_fears, var_fears_type).unwrap();
            conjunction.constraints_mut().add_type(var_fears_type, LABEL_FEARS).unwrap();
            conjunction.constraints_mut().add_role_player(var_fears, var_has_fear, Some(var_role_1)).unwrap();
            conjunction.constraints_mut().add_role_player(var_fears, var_is_feared, Some(var_role_2)).unwrap();

            conjunction.constraints_mut().add_isa(var_role_1, var_role_1_type).unwrap();
            conjunction.constraints_mut().add_type(var_role_1_type, "fears:has-fear").unwrap();
            conjunction.constraints_mut().add_isa(var_role_2, var_role_2_type).unwrap();
            conjunction.constraints_mut().add_type(var_role_2_type, "fears:is-feared").unwrap();

            let constraints = &conjunction.constraints().constraints;

            let mut tig = TypeSeeder::new(&snapshot, &type_manager).seed_types(&conjunction);
            run_type_inference(&mut tig);

            let expected_graph = TypeInferenceGraph {
                conjunction: &conjunction,
                vertices: BTreeMap::from([
                    (var_has_fear, BTreeSet::from([type_cat.clone()])),
                    (var_is_feared, BTreeSet::from([type_dog.clone()])),
                    (var_fears_type, BTreeSet::from([type_fears.clone()])),
                    (var_fears, BTreeSet::from([type_fears.clone()])),
                    (var_role_1, BTreeSet::from([type_has_fear.clone()])),
                    (var_role_2, BTreeSet::from([type_is_feared.clone()])),
                    (var_role_1_type, BTreeSet::from([type_has_fear.clone()])),
                    (var_role_2_type, BTreeSet::from([type_is_feared.clone()])),
                ]),
                edges: vec![
                    // isa
                    expected_edge(
                        &conjunction.constraints().constraints[0],
                        var_fears,
                        var_fears_type,
                        vec![(type_fears.clone(), type_fears.clone())],
                    ),
                    // has-fear edge
                    expected_edge(
                        &conjunction.constraints().constraints[2],
                        var_fears,
                        var_role_1,
                        vec![(type_fears.clone(), type_has_fear.clone())],
                    ),
                    expected_edge(
                        &conjunction.constraints().constraints[2],
                        var_has_fear,
                        var_role_1,
                        vec![(type_cat.clone(), type_has_fear.clone())],
                    ),
                    // is-feared edge
                    expected_edge(
                        &conjunction.constraints().constraints[3],
                        var_fears,
                        var_role_2,
                        vec![(type_fears.clone(), type_is_feared.clone())],
                    ),
                    expected_edge(
                        &conjunction.constraints().constraints[3],
                        var_is_feared,
                        var_role_2,
                        vec![(type_dog.clone(), type_is_feared.clone())],
                    ),
                    expected_edge(
                        &conjunction.constraints().constraints[4],
                        var_role_1,
                        var_role_1_type,
                        vec![(type_has_fear.clone(), type_has_fear.clone())],
                    ),
                    expected_edge(
                        &conjunction.constraints().constraints[6],
                        var_role_2,
                        var_role_2_type,
                        vec![(type_is_feared.clone(), type_is_feared.clone())],
                    ),
                ],
                nested_disjunctions: vec![],
                nested_negations: vec![],
                nested_optionals: vec![],
            };

            assert_eq!(expected_graph, tig);
        }
    }
}
