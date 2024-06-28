/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{BinaryHeap, BTreeMap, BTreeSet, HashMap};
use itertools::Itertools;

use answer::variable::Variable;
use crate::pattern::constraint::{Constraint, Has, Isa, RolePlayer, Type};
use storage::snapshot::ReadableSnapshot;
use concept::type_::type_manager::TypeManager;
use concept::type_::{OwnerAPI, TypeAPI};
use concept::type_::object_type::ObjectType;
use encoding::value::label::Label;
use crate::inference::pattern_type_inference::{NestedTypeInferenceGraph, TypeInferenceEdge, TypeInferenceGraph};
use crate::inference::type_inference::TypeAnnotation;
use crate::pattern::conjunction::Conjunction;
use crate::pattern::pattern::Pattern;
use crate::program::program::Program;


pub trait BinaryConstraintWrapper {
    fn left(&self) -> Variable;
    fn right(&self) -> Variable;

    fn try_annotate_left_to_right(&self, seeder: &TypeSeeder<impl ReadableSnapshot>, unary_annotations: &BTreeMap<Variable, BTreeSet<TypeAnnotation>>) -> Option<BTreeMap<TypeAnnotation,BTreeSet<TypeAnnotation>>> {
        if let Some(left_types) =unary_annotations.get(&self.left()) {
            let mut left_to_right = BTreeMap::new();
            for left_type in left_types {
                let mut right_annotations = BTreeSet::new();
                self.annotate_left_to_right_for_type(seeder, left_type, &mut right_annotations);
                left_to_right.insert(left_type.clone(), right_annotations);
            }
            Some(left_to_right)
        } else {
            None
        }
    }

    fn try_annotate_right_to_left(&self, seeder: &TypeSeeder<impl ReadableSnapshot>, unary_annotations: &BTreeMap<Variable, BTreeSet<TypeAnnotation>>) -> Option<BTreeMap<TypeAnnotation,BTreeSet<TypeAnnotation>>> {
        if let Some(right_types) = unary_annotations.get(&self.right()) {
            let mut right_to_left = BTreeMap::new();
            for right_type in right_types {
                let mut left_annotations = BTreeSet::new();
                self.annotate_right_to_left_for_type(seeder, right_type, &mut left_annotations);
                right_to_left.insert(right_type.clone(), left_annotations);
            }
            Some(right_to_left)
        } else {
            None
        }
    }

    fn annotate_left_to_right_for_type(&self, seeder:  &TypeSeeder<impl ReadableSnapshot>, left_type: &TypeAnnotation, collector: &mut BTreeSet<TypeAnnotation>);
    fn annotate_right_to_left_for_type(&self, seeder:  &TypeSeeder<impl ReadableSnapshot>, right_type: &TypeAnnotation, collector: &mut BTreeSet<TypeAnnotation>);
}


pub(crate) fn seed_types<'graph, Snapshot: ReadableSnapshot>(conjunction: &'graph Conjunction, snapshot: &'_ Snapshot, type_manager: &'_ TypeManager<Snapshot>) -> TypeInferenceGraph<'graph> {
    // Seed unary types
    let seeder = TypeSeeder { snapshot, type_manager };
    seeder.seed_types(&conjunction)
}

pub struct TypeSeeder<'this, Snapshot: ReadableSnapshot> {
    snapshot: &'this Snapshot,
    type_manager: &'this TypeManager<Snapshot>,
}
impl<'this, Snapshot: ReadableSnapshot> TypeSeeder<'this, Snapshot> {
    pub(crate) fn seed_types<'graph>(
        &'this self, conjunction: &'graph Conjunction) -> TypeInferenceGraph<'graph> {
        // Seed unary types
        let mut tig = self.recursively_allocate(conjunction);
        let (constraints, patterns) = (&conjunction.constraints().constraints, &conjunction.patterns().patterns);
        self.seed_types_for_unary_constraints(&mut tig, constraints, patterns);
        self.seed_types_for_binary_constraints(&mut tig, constraints, patterns);

        tig
    }


    fn seed_types_for_unary_constraints<'graph>(
        &self, tig: &mut TypeInferenceGraph<'graph>, constraints: &Vec<Constraint<Variable>>, nested: &Vec<Pattern>
    ) {
        // First we populate the type variables

        let mut vec1: Vec<&Constraint<Variable>> = Vec::with_capacity(constraints.len());
        let mut vec2: Vec<&Constraint<Variable>> = Vec::with_capacity(constraints.len());
        for constraint in constraints {
            match constraint {
                Constraint::Type(type_constraint) => {
                    let annotation = self.get_annotation_for_type_label(&type_constraint);
                    Self::intersect_unary(&mut tig.vertices, type_constraint.var, BTreeSet::from([annotation]));
                },
                Constraint::ExpressionBinding(_) => todo!("Apply"),
                Constraint::FunctionCallBinding(_) => todo!("Apply"),
                // Get any missing type annotations from the binary constraints
                c => vec1.push(c),// Do nothing
            }
        }

        for nested in &mut tig.nested_graphs {
            let mut nested_unary = BTreeMap::new();
            for nested_tig in &mut nested.nested_graph_disjunction {
                // TODO: parent annotations need to be passed down.
                self.seed_types_for_unary_constraints(nested_tig, &nested_tig.conjunction.constraints().constraints, &nested_tig.conjunction.patterns().patterns);
                for (variable, types) in &nested_tig.vertices {
                    if !nested_unary.contains_key(variable) {
                        nested_unary.insert(*variable, BTreeSet::new());
                    }
                    nested_unary.get_mut(variable).unwrap().extend(types.clone());
                }
            }
            for (variable, types) in nested_unary.into_iter() {
                println!("{:?} -> {:?}", variable, types);
                Self::intersect_unary(&mut tig.vertices, variable, types);
            }
        }
        // TODO: These patterns:
                // Pattern::Negation(negation) => {
                //     // Only for those local to the negation
                //     let nested_unary = self.seed_types_for_unary_constraints(&negation.conjunction.constraints().constraints, &negation.conjunction.patterns().patterns);
                //     for (variable, types) in nested_unary.into_iter() {
                //         if !unary_annotations.contains_key(&variable) {
                //             unary_annotations.insert(variable, types);
                //         }
                //     }
                // },
                // Pattern::Optional(opt) => {
                //     // Only for those local to the optional
                //     let nested_unary = self.seed_types_for_unary_constraints(&opt.conjunction.constraints().constraints, &opt.conjunction.patterns().patterns);
                //     for (variable, types) in nested_unary.into_iter() {
                //         if !unary_annotations.contains_key(&variable) {
                //             unary_annotations.insert(variable, types);
                //         }
                //     }
                // },

        let mut from_vec = &mut vec1;
        let mut to_vec = &mut vec2;
        let mut prev_size = from_vec.len() + 1;
        while from_vec.len() != prev_size {
            prev_size = from_vec.len();
            for c in &mut *from_vec {
                let both_variables_have_annotations = match c {
                    Constraint::Isa(isa) => self.try_infer_unary_annotations_from_binary_constraints(isa, &mut tig.vertices),
                    Constraint::RolePlayer(rp) => todo!("self.try_infer_unary_annotations_from_binary_constraints(rp, &mut unary_annotations)"),
                    Constraint::Has(has) => self.try_infer_unary_annotations_from_binary_constraints(has, &mut tig.vertices),
                    Constraint::Comparison(cmp) => todo!("self.try_infer_unary_annotations_from_binary_constraints(cmp, &mut unary_annotations)"), // I'm not thrilled about this.

                    Constraint::ExpressionBinding(_) | Constraint::FunctionCallBinding(_) | Constraint::Type(_) => unreachable!()
                };
                if !both_variables_have_annotations {
                    to_vec.push(*c);
                }
            }
            from_vec.clear(); // Clear & swap avoids re-allocation
            let t = from_vec;
            from_vec = to_vec;
            to_vec = t;
        }

        if !from_vec.is_empty() {
            println!("{:?}", &mut tig.vertices);
            println!("{:?}", from_vec);
            todo!("This is rare. Just fill in the remaining variables with all the types")
        }
    }

    fn try_infer_unary_annotations_from_binary_constraints(&self, constraint: &impl BinaryConstraintWrapper, unary_annotations: &mut BTreeMap<Variable, BTreeSet<TypeAnnotation>>) -> bool {
        if let Some(left_annotations) = unary_annotations.get(&constraint.left()) {
            if unary_annotations.contains_key(&constraint.right()) {
                true
            } else {
                // Infer right from left
                let mut right_types = BTreeSet::new();
                for left_type in left_annotations {
                    constraint.annotate_left_to_right_for_type(self, left_type, &mut right_types);
                }
                unary_annotations.insert(constraint.right(), right_types);
                true
            }
        } else if let Some(right_annotations) = unary_annotations.get(&constraint.right()) {
            // Infer left from right
            let mut left_types = BTreeSet::new();
            for right_type in right_annotations {
                constraint.annotate_right_to_left_for_type(self, right_type, &mut left_types);
            }
            unary_annotations.insert(constraint.left(), left_types);
            true
        } else {
            false
        }
    }

    fn seed_types_for_binary_constraints<'graph>(
        &self, tig: &mut TypeInferenceGraph<'graph>, constraints: &'graph Vec<Constraint<Variable>>, nested: &'graph Vec<Pattern>
    ) {
        // TODO: We should try to be clever about how we handle types without unary constraints
        // First we populate the type variables
        for constraint in constraints {
            match constraint {
                Constraint::RolePlayer(unwrapped) => todo!(),
                Constraint::Isa(unwrapped) => { // TODO: Do we need isa here?
                    let left_to_right = unwrapped.try_annotate_left_to_right(self, &mut tig.vertices).unwrap();
                    let right_to_left = unwrapped.try_annotate_right_to_left(self, &mut tig.vertices).unwrap();
                    tig.edges.push(TypeInferenceEdge::new(&constraint, unwrapped.left(), unwrapped.right(), left_to_right, right_to_left));
                },
                Constraint::Has(unwrapped) => {
                    let left_to_right = unwrapped.try_annotate_left_to_right(self, &mut tig.vertices).unwrap();
                    let right_to_left = unwrapped.try_annotate_right_to_left(self, &mut tig.vertices).unwrap();
                    tig.edges.push(TypeInferenceEdge::new(&constraint, unwrapped.left(), unwrapped.right(), left_to_right, right_to_left));
                }
                Constraint::Type(_) | Constraint::ExpressionBinding(_) | Constraint::FunctionCallBinding(_) | Constraint::Comparison(_) => {} // Do nothing
            }
        }
        for nested_graph in &mut tig.nested_graphs {
            for nested_tig in &mut nested_graph.nested_graph_disjunction {
                self.seed_types_for_binary_constraints(nested_tig, &nested_tig.conjunction.constraints().constraints, &nested_tig.conjunction.patterns().patterns)
            }
        }
    }

    fn get_annotation_for_type_label(&self, type_: &Type<Variable>) -> TypeAnnotation {
        if let Some(attribute) = self.type_manager.get_attribute_type(self.snapshot, &Label::build(&type_.type_)).unwrap() {
            TypeAnnotation::SchemaTypeAttribute(attribute)
        } else if let Some(entity) = self.type_manager.get_entity_type(self.snapshot, &Label::build(&type_.type_)).unwrap() {
            TypeAnnotation::SchemaTypeEntity(entity)
        } else if let Some(relation) = self.type_manager.get_relation_type(self.snapshot, &Label::build(&type_.type_)).unwrap() {
            TypeAnnotation::SchemaTypeRelation(relation)
        } else if let Some(role) = self.type_manager.get_role_type(self.snapshot, &Label::build(&type_.type_)).unwrap() {
            TypeAnnotation::SchemaTypeRole(role)
        } else {
            todo!("Was not one of the 4 vertex types")
        }
    }

    fn intersect_unary(unary_annotations: &mut BTreeMap<Variable, BTreeSet<TypeAnnotation>>, variable: Variable, new_annotations: BTreeSet<TypeAnnotation>) {
        if let Some(existing_annotations) = unary_annotations.get_mut(&variable) {
            existing_annotations.retain(|x| new_annotations.contains(x))
        } else {
            unary_annotations.insert(variable, new_annotations.into());
        }
    }


    fn recursively_allocate<'conj>(&self, conj: &'conj Conjunction) -> TypeInferenceGraph<'conj> {
        let mut nested = Vec::new();
        for pattern in &conj.patterns().patterns {
            match pattern {
                Pattern::Conjunction(_) => { todo!("ban?") }
                Pattern::Disjunction(disjunction) => {
                    nested.push(NestedTypeInferenceGraph { nested_graph_disjunction: (&disjunction.conjunctions).iter().map(|c| self.recursively_allocate(c)).collect() });
                },
                Pattern::Negation(_) => { todo!() }
                Pattern::Optional(_) => { todo!() }
            }
        }

        TypeInferenceGraph {
            conjunction: conj,
            vertices: BTreeMap::new(),
            edges: Vec::new(),
            nested_graphs: nested,
        }
    }
}

impl BinaryConstraintWrapper for Has<Variable> {
    fn left(&self) -> Variable {
        self.owner
    }

    fn right(&self) -> Variable {
        self.attribute
    }

    fn annotate_left_to_right_for_type(&self, seeder:  &TypeSeeder<impl ReadableSnapshot>, left_type: &TypeAnnotation, collector: &mut BTreeSet<TypeAnnotation>) {
        let owner = match left_type {
            TypeAnnotation::SchemaTypeEntity(entity) => ObjectType::Entity(entity.clone()),
            TypeAnnotation::SchemaTypeRelation(relation) => ObjectType::Relation(relation.clone()),
            _ => todo!("Return an error for using an attribute type here")
        };
        owner.get_owns_transitive(seeder.snapshot, seeder.type_manager).unwrap().iter().map(|(attribute, _)| {
            TypeAnnotation::SchemaTypeAttribute(attribute.clone())
        }).for_each(|type_| {collector.insert(type_);});
    }

    fn annotate_right_to_left_for_type(&self, seeder:  &TypeSeeder<impl ReadableSnapshot>, right_type: &TypeAnnotation, collector: &mut BTreeSet<TypeAnnotation>)
    {
        let attribute = match right_type {
            TypeAnnotation::SchemaTypeAttribute(attribute) => attribute,
            _ => todo!("Return an error for using a non-attribute where an attribute was expected")
        };
        attribute.get_owners_transitive(seeder.snapshot, seeder.type_manager).unwrap().iter().map(|(owner, _)| {
            match owner {
                ObjectType::Entity(entity) => TypeAnnotation::SchemaTypeEntity(entity.clone()),
                ObjectType::Relation(relation) => TypeAnnotation::SchemaTypeRelation(relation.clone()),
            }
        }).for_each(|type_| {collector.insert(type_);});
    }
}

impl BinaryConstraintWrapper for Isa<Variable> {
    fn left(&self) -> Variable {
        self.thing
    }

    fn right(&self) -> Variable {
        self.type_
    }

    fn annotate_left_to_right_for_type(&self, seeder: &TypeSeeder<impl ReadableSnapshot>, left_type: &TypeAnnotation, collector: &mut BTreeSet<TypeAnnotation>) {
        match left_type {
            TypeAnnotation::SchemaTypeAttribute(attribute) => {
                attribute.get_supertypes(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeAttribute(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
            TypeAnnotation::SchemaTypeEntity(entity) => {
                entity.get_supertypes(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeEntity(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
            TypeAnnotation::SchemaTypeRelation(relation) => {
                relation.get_supertypes(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeRelation(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
            TypeAnnotation::SchemaTypeRole(role_type) => {
                role_type.get_supertypes(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeRole(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
        }
        collector.insert(left_type.clone());
    }

    fn annotate_right_to_left_for_type(&self, seeder: &TypeSeeder<impl ReadableSnapshot>, right_type: &TypeAnnotation, collector: &mut BTreeSet<TypeAnnotation>) {
        match right_type {
            TypeAnnotation::SchemaTypeAttribute(attribute) => {
                attribute.get_subtypes_transitive(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeAttribute(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
            TypeAnnotation::SchemaTypeEntity(entity) => {
                entity.get_subtypes_transitive(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeEntity(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
            TypeAnnotation::SchemaTypeRelation(relation) => {
                relation.get_subtypes_transitive(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeRelation(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
            TypeAnnotation::SchemaTypeRole(role_type) => {
                role_type.get_subtypes_transitive(seeder.snapshot, seeder.type_manager).unwrap().iter()
                    .map(|subtype| TypeAnnotation::SchemaTypeRole(subtype.clone().into_owned()))
                    .for_each(|subtype| { collector.insert(subtype); });
            }
        }
        collector.insert(right_type.clone());
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
        inference::pattern_type_inference::{TypeInferenceEdge, TypeInferenceGraph},
    };
    use crate::inference::pattern_type_inference::tests::expected_edge;
    use crate::inference::seed_types::{seed_types, TypeSeeder};
    use crate::inference::type_inference::TypeAnnotation::{SchemaTypeAttribute, SchemaTypeEntity};
    use crate::pattern::conjunction::Conjunction;
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
            let mut conjunction = Conjunction::new_root();
            let var_animal = conjunction.get_or_declare_variable("animal").unwrap();
            let var_name = conjunction.get_or_declare_variable(&"name").unwrap();
            let var_animal_type = conjunction.get_or_declare_variable(&"animal_type").unwrap();
            let var_name_type =  conjunction.get_or_declare_variable(&"name_type").unwrap();

            // Try seeding
            {
                conjunction.constraints_mut().add_isa(var_animal, var_animal_type).unwrap();
                conjunction.constraints_mut().add_type(var_animal_type, &label_cat).unwrap();
                conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
                conjunction.constraints_mut().add_type(var_name_type, &label_name).unwrap();
                conjunction.constraints_mut().add_has(var_animal, var_name).unwrap();
            }

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

                let constraints = &conjunction.constraints().constraints;
                TypeInferenceGraph {
                    conjunction: &conjunction,
                    vertices: BTreeMap::from([(var_animal, types_a), (var_name, types_n), (var_animal_type, types_ta), (var_name_type, types_tn)]),
                    edges: vec![
                        expected_edge(&constraints[0], var_animal, var_animal_type, vec![(type_cat.clone(), type_cat.clone())]),
                        expected_edge(&constraints[2], var_name, var_name_type, vec![(type_catname.clone(), type_name.clone()), (type_dogname.clone(), type_name.clone()), (type_name.clone(), type_name.clone())]),
                        expected_edge(&constraints[4], var_animal, var_name, vec![(type_cat.clone(), type_catname.clone())])
                    ],
                    nested_graphs: vec![],
                }
            };

            let snapshot = storage.clone().open_snapshot_write();
            let seeder = TypeSeeder { snapshot: &snapshot, type_manager: &type_manager };
            let tig = seeder.seed_types(&conjunction);

            assert_eq!(expected_tig, tig);
        }
    }
}
