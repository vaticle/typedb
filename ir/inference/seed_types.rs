/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BTreeMap, BTreeSet};
use itertools::Itertools;

use crate::pattern::constraint::{Constraint, Has, RolePlayer, Type};
use storage::snapshot::ReadableSnapshot;
use concept::type_::type_manager::TypeManager;
use concept::type_::{OwnerAPI, TypeAPI};
use concept::type_::object_type::ObjectType;
use encoding::value::label::Label;
use crate::inference::pattern_type_inference::{TypeInferenceEdge, TypeInferenceGraph};
use crate::inference::type_inference::TypeAnnotation;
use crate::pattern::variable::Variable;

fn seed_types<Snapshot: ReadableSnapshot>(constraints: &Vec<Constraint>, snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>) -> TypeInferenceGraph {
    // Seed unary types
    let unary_annotations= seed_types_for_unary_constraints(constraints, snapshot, type_manager);
    let edges = seed_types_for_binary_constraints(constraints, snapshot, type_manager, &unary_annotations);
    TypeInferenceGraph {
        vertices: unary_annotations,
        edges: edges,
        nested_graphs: Vec::new()
    }
}

fn seed_types_for_unary_constraints<Snapshot: ReadableSnapshot>(
    constraints: &Vec<Constraint>, snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>
) -> BTreeMap<Variable, BTreeSet<TypeAnnotation>> {
    // First we populate the type variables
    let mut unary_annotations = BTreeMap::new();
    for constraint in constraints {
        match constraint {
            Constraint::Type(type_constraint) => {
                let annotation = get_annotation_for_type_constraint(snapshot, type_manager, &type_constraint);
                merge_unary(&mut unary_annotations, type_constraint.var, BTreeSet::from([annotation]));
            },
            _ => {} // Ignore
        }
    }
    for constraint in constraints {
        match constraint {
            Constraint::Isa(isa_constraint) => {
                let annotations: BTreeSet<TypeAnnotation> = unary_annotations.get(&isa_constraint.type_).unwrap()  // TODO: Don't unwrap
                    .iter().flat_map(|type_annotation| {
                        let mut subtypes = get_subtypes_for_type_annotation(snapshot, type_manager, type_annotation);
                        subtypes.insert(type_annotation.clone());
                        subtypes
                    }).collect();
                merge_unary(&mut unary_annotations, isa_constraint.thing, annotations);
            },
            _ => {}
        }
    }
    for constraint in constraints {
        match constraint {
            Constraint::FunctionCallBinding(function_constraint) => todo!("Apply?"),
            Constraint::ExpressionBinding(_) => todo!("Apply?"), // For the lhs?

            Constraint::Isa(_) |
            Constraint::Type(_) |
            Constraint::RolePlayer(_) |
            Constraint::Has(_) |
            Constraint::Comparison(_) => {} // Do nothing
        }
    }
    unary_annotations
}


fn seed_types_for_binary_constraints<Snapshot: ReadableSnapshot>(
    constraints: &Vec<Constraint>, snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>,
    unary_annotations: &BTreeMap<Variable, BTreeSet<TypeAnnotation>>
) -> Vec<TypeInferenceEdge> {
    // First we populate the type variables
    let mut edges: Vec<TypeInferenceEdge> =  Vec::new();
    for constraint in constraints {
        match constraint {
            Constraint::RolePlayer(role_player) => edges.extend(seed_types_for_role_player(snapshot, type_manager, role_player, unary_annotations)),
            Constraint::Has(has_edge) => edges.push(seed_types_for_has(snapshot, type_manager, has_edge, unary_annotations)),
            Constraint::Comparison(_) => todo!("?"),

            Constraint::FunctionCallBinding(_) |
            Constraint::ExpressionBinding(_) |
            Constraint::Isa(_) |
            Constraint::Type(_) => {} // Do nothing
        }
    }
    edges
}

fn seed_types_for_role_player<Snapshot: ReadableSnapshot>(
    snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>,
    role_player: &RolePlayer, unary_constraints: &BTreeMap<Variable, BTreeSet<TypeAnnotation>>
) -> [TypeInferenceEdge; 2] {
    todo!("That filter is odd")
    // let vars = role_player.variables().collect(); // TODO: Refactor
    // let (left, right, filter) = (vars[0], vars[1], if vars.len() > 2  { Some(vars[2]) } else { None });
}

fn seed_types_for_has<Snapshot: ReadableSnapshot>(
    snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>,
    has: &Has, unary_constraints: &BTreeMap<Variable, BTreeSet<TypeAnnotation>>
) -> TypeInferenceEdge {
    let vars = has.variables().collect::<Vec<Variable>>(); // TODO: Refactor
    let (left, right) = (vars[0], vars[1]);
    let mut left_to_right = BTreeMap::new();
    // TODO: What if there were no unary constraints?
    for left_type in unary_constraints.get(&left).unwrap() {
        let owner = match left_type {
            TypeAnnotation::SchemaTypeEntity(entity) => ObjectType::Entity(entity.clone()),
            TypeAnnotation::SchemaTypeRelation(relation) => ObjectType::Relation(relation.clone()),
            _ => todo!("Legit error of using an attribute type here")
        };
        left_to_right.insert(
            left_type.clone(),
            owner.get_owns_transitive(snapshot, type_manager).unwrap().iter().map(|(attribute, _)| {
                TypeAnnotation::SchemaTypeAttribute(attribute.clone())
            })
            .collect()
        );
    }
    let mut right_to_left = BTreeMap::new();
    for right_type in unary_constraints.get(&right).unwrap() {
        let attribute = match right_type {
            TypeAnnotation::SchemaTypeAttribute(attribute) => attribute,
            _ => todo!("Return an error for using a non-attribute where an attribute was expected")
        };
        right_to_left.insert(
            right_type.clone(),
            attribute.get_owners_transitive(snapshot, type_manager).unwrap().iter().map(|(owner, _)| {
                match owner {
                    ObjectType::Entity(entity) => TypeAnnotation::SchemaTypeEntity(entity.clone()),
                    ObjectType::Relation(relation) => TypeAnnotation::SchemaTypeRelation(relation.clone()),
                }
            })
            .collect()
        );
    }
    TypeInferenceEdge::new(left, right, left_to_right, right_to_left)
}


fn merge_unary(unary_annotations: &mut BTreeMap<Variable, BTreeSet<TypeAnnotation>>, variable: Variable, new_annotations: BTreeSet<TypeAnnotation>) {
    if let Some(existing_annotations) = unary_annotations.get_mut(&variable) {
        existing_annotations.retain(|x| new_annotations.contains(x))
    } else {
        unary_annotations.insert(variable, new_annotations.into());
    }
}

fn get_annotation_for_type_constraint<Snapshot: ReadableSnapshot>(snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>, type_: &Type) -> TypeAnnotation {
    if let Some(attribute) = type_manager.get_attribute_type(snapshot, &Label::build(&type_.type_)).unwrap() {
        TypeAnnotation::SchemaTypeAttribute(attribute)
    } else if let Some(entity) = type_manager.get_entity_type(snapshot, &Label::build(&type_.type_)).unwrap() {
        TypeAnnotation::SchemaTypeEntity(entity)
    } else if let Some(relation) = type_manager.get_relation_type(snapshot, &Label::build(&type_.type_)).unwrap() {
        TypeAnnotation::SchemaTypeRelation(relation)
    } else if let Some(role) = type_manager.get_role_type(snapshot, &Label::build(&type_.type_)).unwrap() { // Or should we resolve or something?
        TypeAnnotation::SchemaTypeRole(role)
    } else {
        todo!("Was not one of the 4 vertex types")
    }
}

fn get_subtypes_for_type_annotation<Snapshot: ReadableSnapshot>(snapshot: &Snapshot, type_manager: &TypeManager<Snapshot>, type_: &TypeAnnotation) -> BTreeSet<TypeAnnotation> {
    match type_ {
        TypeAnnotation::SchemaTypeAttribute(attribute) => {
            attribute.get_subtypes_transitive(snapshot, type_manager).unwrap().iter()
                .map(|subtype| TypeAnnotation::SchemaTypeAttribute(subtype.clone().into_owned()))
                .collect()
        }
        TypeAnnotation::SchemaTypeEntity(entity) => {
            entity.get_subtypes_transitive(snapshot, type_manager).unwrap().iter()
                .map(|subtype| TypeAnnotation::SchemaTypeEntity(subtype.clone().into_owned()))
                .collect()
        }
        TypeAnnotation::SchemaTypeRelation(relation) => {
            relation.get_subtypes_transitive(snapshot, type_manager).unwrap().iter()
                .map(|subtype| TypeAnnotation::SchemaTypeRelation(subtype.clone().into_owned()))
                .collect()
        }
        TypeAnnotation::SchemaTypeRole(role_type) => {
            role_type.get_subtypes_transitive(snapshot, type_manager).unwrap().iter()
                .map(|subtype| TypeAnnotation::SchemaTypeRole(subtype.clone().into_owned()))
                .collect()
        }
    }
}


#[cfg(test)]
pub mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::Arc;
    use concept::thing::thing_manager::ThingManager;
    use concept::type_::{Ordering, OwnerAPI};
    use concept::type_::annotation::AnnotationAbstract;
    use concept::type_::attribute_type::AttributeTypeAnnotation;
    use concept::type_::type_manager::TypeManager;
    use durability::wal::WAL;
    use encoding::EncodingKeyspace;
    use encoding::graph::definition::definition_key_generator::DefinitionKeyGenerator;
    use encoding::graph::thing::vertex_generator::ThingVertexGenerator;
    use encoding::graph::type_::vertex_generator::TypeVertexGenerator;
    use encoding::value::label::Label;
    use storage::durability_client::WALClient;
    use storage::MVCCStorage;
    use storage::snapshot::{CommittableSnapshot, ReadableSnapshot, WriteSnapshot};
    use test_utils::{create_tmp_dir, init_logging};

    use crate::{
        inference::pattern_type_inference::{NestedTypeInferenceGraph, TypeInferenceEdge, TypeInferenceGraph},
        pattern::{variable::Variable},
    };
    use crate::inference::seed_types::{seed_types, seed_types_for_binary_constraints, seed_types_for_unary_constraints};
    use crate::inference::type_inference::TypeAnnotation::{SchemaTypeAttribute, SchemaTypeEntity};
    use crate::pattern::constraint::{Constraint, Has, Isa, Type};

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

    #[test]
    fn test_seeding() {
        // dog sub animal, owns dog-name; cat sub animal owns cat-name;
        // cat-name sub animal-name; dog-name sub animal-name;

        // Some version of `$a isa animal, has name $n;`
        let var_animal = Variable::new(0);
        let var_name = Variable::new(1);
        let var_animal_type = Variable::new(2);
        let var_name_type = Variable::new(3);

        let label_animal = "animal".to_owned();
        let label_cat = "cat".to_owned();
        let label_dog = "dog".to_owned();

        let label_name = "name".to_owned();
        let label_catname = "cat-name".to_owned();
        let label_dogname = "dog-name".to_owned();

        let storage = setup_storage();
        let (type_manager, thing_manager) = managers(storage.clone());


        let ((type_animal, type_cat, type_dog), (type_name, type_catname, type_dogname) ) = {
            let mut schema_snapshot = storage.clone().open_snapshot_write();

            let name = type_manager.create_attribute_type(&mut schema_snapshot, &Label::build(&label_name), false).unwrap();
            let catname = type_manager.create_attribute_type(&mut schema_snapshot, &Label::build(&label_catname), false).unwrap();
            let dogname = type_manager.create_attribute_type(&mut schema_snapshot, &Label::build(&label_dogname), false).unwrap();
            name.set_annotation(&mut schema_snapshot, &type_manager, AttributeTypeAnnotation::Abstract(AnnotationAbstract)).unwrap();
            catname.set_supertype(&mut schema_snapshot, &type_manager, name.clone()).unwrap();
            dogname.set_supertype(&mut schema_snapshot, &type_manager, name.clone()).unwrap();

            let animal = type_manager.create_entity_type(&mut schema_snapshot, &Label::build(&label_animal), false).unwrap();
            let cat = type_manager.create_entity_type(&mut schema_snapshot, &Label::build(&label_cat), false).unwrap();
            let dog = type_manager.create_entity_type(&mut schema_snapshot, &Label::build(&label_dog), false).unwrap();
            cat.set_supertype(&mut schema_snapshot, &type_manager, animal.clone()).unwrap();
            dog.set_supertype(&mut schema_snapshot, &type_manager, animal.clone()).unwrap();

            let animal_owns = animal.set_owns(&mut schema_snapshot, &type_manager, name.clone(), Ordering::Unordered).unwrap();
            let cat_owns = cat.set_owns(&mut schema_snapshot, &type_manager, catname.clone(), Ordering::Unordered).unwrap();
            let dog_owns = dog.set_owns(&mut schema_snapshot, &type_manager, dogname.clone(), Ordering::Unordered).unwrap();
            cat_owns.set_override(&mut schema_snapshot, &type_manager, animal_owns.clone()).unwrap();
            dog_owns.set_override(&mut schema_snapshot, &type_manager, animal_owns.clone()).unwrap();
            schema_snapshot.commit().unwrap();

            (
                (SchemaTypeEntity(animal), SchemaTypeEntity(cat), SchemaTypeEntity(dog)),
                (SchemaTypeAttribute(name), SchemaTypeAttribute(catname), SchemaTypeAttribute(dogname))
            )
        };

        {
            // // Case 1: $a isa cat, has animal-name $n;

            let expected_tig = {
                let types_ta =  BTreeSet::from([type_cat.clone()]);
                let types_a = BTreeSet::from([type_cat.clone()]);
                let types_tn =  BTreeSet::from([type_name.clone()]);
                let types_n = BTreeSet::from([type_name.clone(), type_catname.clone(), type_dogname.clone()]);

                let left_to_right = BTreeMap::from([(type_cat.clone(), BTreeSet::from([type_catname.clone()]))]);
                let right_to_left = BTreeMap::from([
                    (type_name.clone(), BTreeSet::from([type_animal.clone()])),
                    (type_catname.clone(), BTreeSet::from([type_cat.clone()])),
                    (type_dogname.clone(), BTreeSet::from([type_dog.clone()])),
                ]);

                TypeInferenceGraph {
                    vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n), (var_animal_type, types_ta), (var_name_type, types_tn)]),
                    edges: vec![TypeInferenceEdge::new(var_animal, var_name, left_to_right.clone(), right_to_left.clone())],
                    nested_graphs: vec![],
                }
            };

            // Try seeding
            let snapshot = storage.clone().open_snapshot_write();
            let constraints = vec![
                Constraint::Isa(Isa::new(var_animal, var_animal_type)),
                Constraint::Type(Type::new(var_animal_type, label_cat)),

                Constraint::Isa(Isa::new(var_name, var_name_type)),
                Constraint::Type(Type::new(var_name_type, label_name)),

                Constraint::Has(Has::new(var_animal, var_name)),
            ];
            let unary_annotations= seed_types_for_unary_constraints(&constraints, &snapshot, &type_manager);
            assert_eq!(expected_tig.vertices, unary_annotations);

            let edges = seed_types_for_binary_constraints(&constraints, &snapshot, &type_manager, &unary_annotations);
            assert_eq!(expected_tig.edges, edges);
        }
    }
}
