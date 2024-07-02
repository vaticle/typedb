/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, HashSet},
};

use answer::{variable::Variable, Type as TypeAnnotation};
use concept::{
    error::ConceptReadError,
    type_::{object_type::ObjectType, type_manager::TypeManager, OwnerAPI, PlayerAPI, TypeAPI},
};
use encoding::{
    graph::type_::Kind,
    value::{
        label::Label,
        value_type::{ValueType, ValueTypeCategory},
    },
};
use itertools::Itertools;
use storage::snapshot::ReadableSnapshot;

use crate::{
    inference::{
        pattern_type_inference::{NestedTypeInferenceGraphDisjunction, TypeInferenceEdge, TypeInferenceGraph},
        type_inference::VertexAnnotations,
        TypeInferenceError,
    },
    pattern::{
        conjunction::Conjunction,
        constraint::{Comparison, Constraint, Has, Isa, RolePlayer, Type},
        pattern::Pattern,
        variable_category::VariableCategory,
    },
};

pub struct TypeSeeder<'this, Snapshot: ReadableSnapshot> {
    snapshot: &'this Snapshot,
    type_manager: &'this TypeManager<Snapshot>,
}
impl<'this, Snapshot: ReadableSnapshot> TypeSeeder<'this, Snapshot> {
    pub(crate) fn new(snapshot: &'this Snapshot, type_manager: &'this TypeManager<Snapshot>) -> Self {
        TypeSeeder { snapshot, type_manager }
    }

    pub(crate) fn seed_types<'graph>(
        &'this self,
        conjunction: &'graph Conjunction,
    ) -> Result<TypeInferenceGraph<'graph>, TypeInferenceError> {
        let mut tig = self.recursively_allocate(conjunction);
        self.seed_types_impl(&mut tig, &BTreeMap::new())?;
        Ok(tig)
    }

    pub(crate) fn seed_types_impl<'graph>(
        &self,
        tig: &mut TypeInferenceGraph<'graph>,
        parent_vertices: &VertexAnnotations,
    ) -> Result<(), TypeInferenceError> {
        tig.conjunction.constraints().constraints.iter().flat_map(|constraint| constraint.ids()).dedup().for_each(
            |v| {
                if let Some(parent_annotations) = parent_vertices.get(&v) {
                    tig.vertices.insert(v, parent_annotations.clone());
                }
            },
        );

        self.seed_vertex_annotations_from_type_and_function_return(tig);
        let mut some_vertex_was_directly_annotated = true;
        while some_vertex_was_directly_annotated {
            let mut something_changed = true;
            while something_changed {
                something_changed = self
                    .propagate_vertex_annotations(tig)
                    .map_err(|source| TypeInferenceError::ConceptRead { source })?;
            }
            some_vertex_was_directly_annotated =
                self.annotate_unannotated_vertex(tig).map_err(|source| TypeInferenceError::ConceptRead { source })?;
        }
        self.seed_edges(tig);

        // Now we recurse into the nested negations & optionals
        let TypeInferenceGraph { vertices, nested_negations, nested_optionals, .. } = tig;
        for nested_tig in nested_negations {
            self.seed_types_impl(nested_tig, vertices);
        }
        for nested_tig in nested_optionals {
            self.seed_types_impl(nested_tig, vertices);
        }
        Ok(())
    }

    fn recursively_allocate<'conj>(&self, conjunction: &'conj Conjunction) -> TypeInferenceGraph<'conj> {
        let mut disjunctions = Vec::new();
        let mut optionals = Vec::new();
        let mut negations = Vec::new();
        for pattern in &conjunction.patterns().patterns {
            match pattern {
                Pattern::Conjunction(_) => {
                    todo!("ban?")
                }
                Pattern::Disjunction(disjunction) => {
                    let nested_tigs = disjunction.conjunctions().iter().map(|c| self.recursively_allocate(c)).collect();
                    let shared_variables: BTreeSet<Variable> = disjunction
                        .conjunctions()
                        .iter()
                        .flat_map(|nested_conj| {
                            nested_conj.constraints().constraints.iter().flat_map(|constraint| constraint.ids()).filter(
                                |variable| {
                                    conjunction.context().is_variable_available(conjunction.scope_id(), *variable)
                                },
                            )
                        })
                        .collect();
                    disjunctions.push(NestedTypeInferenceGraphDisjunction {
                        disjunction: nested_tigs,
                        shared_variables,
                        shared_vertex_annotations: BTreeMap::new(),
                    });
                }
                Pattern::Negation(negation) => {
                    negations.push(self.recursively_allocate(negation.conjunction()));
                }
                Pattern::Optional(optional) => {
                    optionals.push(self.recursively_allocate(optional.conjunction()));
                }
            }
        }

        TypeInferenceGraph {
            conjunction,
            vertices: BTreeMap::new(),
            edges: Vec::new(),
            nested_disjunctions: disjunctions,
            nested_negations: negations,
            nested_optionals: optionals,
        }
    }

    // Phase 1: Collect all type & function return annotations
    fn seed_vertex_annotations_from_type_and_function_return<'graph>(
        &self,
        tig: &mut TypeInferenceGraph<'graph>,
    ) -> Result<(), TypeInferenceError> {
        // Get vertex annotations from Type & Function returns
        for constraint in &tig.conjunction.constraints().constraints {
            match constraint {
                Constraint::Type(type_constraint) => {
                    let annotation_opt = self
                        .get_annotation_for_type_label(&type_constraint)
                        .map_err(|source| TypeInferenceError::ConceptRead { source })?;
                    if let Some(annotation) = annotation_opt {
                        Self::intersect_unary(
                            &mut tig.vertices,
                            type_constraint.left,
                            Cow::Owned(BTreeSet::from([annotation])),
                        );
                    } else {
                        return Err(TypeInferenceError::LabelNotResolved(type_constraint.type_.clone()));
                    }
                }
                Constraint::ExpressionBinding(_) => todo!("Apply"),
                Constraint::FunctionCallBinding(_) => todo!("Apply"),
                _ => {} // Do nothing
            }
        }
        for nested in &mut tig.nested_disjunctions {
            for nested_tig in &mut nested.disjunction {
                self.seed_vertex_annotations_from_type_and_function_return(nested_tig)?;
            }
        }
        Ok(())
    }

    fn annotate_unannotated_vertex<'graph>(
        &self,
        tig: &mut TypeInferenceGraph<'graph>,
    ) -> Result<bool, ConceptReadError> {
        let unannotated_vars: Vec<Variable> = tig
            .conjunction
            .constraints()
            .constraints
            .iter()
            .flat_map(|constraint| constraint.ids())
            .dedup()
            .filter(|v| !tig.vertices.contains_key(v))
            .collect();
        if let Some(v) = unannotated_vars.first() {
            let annotations = if let Some(variable_category) = tig.conjunction.context().get_variable_category(*v) {
                match variable_category {
                    VariableCategory::Type => self.get_unbounded_type_annotations(true, true, true, true)?,
                    VariableCategory::ThingType => self.get_unbounded_type_annotations(true, true, true, false)?,
                    VariableCategory::RoleType => self.get_unbounded_type_annotations(false, false, false, true)?,
                    VariableCategory::Thing => self.get_unbounded_type_annotations(true, true, true, false)?,
                    VariableCategory::Object => self.get_unbounded_type_annotations(true, true, false, false)?,
                    VariableCategory::Attribute => self.get_unbounded_type_annotations(false, false, true, false)?,
                    VariableCategory::Value
                    | VariableCategory::ObjectList
                    | VariableCategory::AttributeList
                    | VariableCategory::ValueList => todo!(),
                }
            } else {
                self.get_unbounded_type_annotations(true, true, true, true)?
            };
            tig.vertices.insert(*v, annotations);
            Ok(true)
        } else {
            let mut any = false;
            for disj in &mut tig.nested_disjunctions {
                for nested_tig in &mut disj.disjunction {
                    any = any || self.annotate_unannotated_vertex(nested_tig)?;
                }
            }
            Ok(any)
        }
    }

    fn get_unbounded_type_annotations(
        &self,
        include_entities: bool,
        include_relations: bool,
        include_attributes: bool,
        include_roles: bool,
    ) -> Result<BTreeSet<TypeAnnotation>, ConceptReadError> {
        let mut annotations = BTreeSet::new();

        if include_entities {
            annotations.extend(
                self.type_manager
                    .get_entity_type(self.snapshot, &Kind::Entity.root_label())?
                    .unwrap()
                    .get_subtypes_transitive(self.snapshot, self.type_manager)?
                    .iter()
                    .map(|entity| TypeAnnotation::Entity(entity.clone())),
            );
        }
        if include_relations {
            annotations.extend(
                self.type_manager
                    .get_relation_type(self.snapshot, &Kind::Relation.root_label())?
                    .unwrap()
                    .get_subtypes_transitive(self.snapshot, self.type_manager)?
                    .iter()
                    .map(|relation| TypeAnnotation::Relation(relation.clone())),
            );
        }
        if include_attributes {
            annotations.extend(
                self.type_manager
                    .get_attribute_type(self.snapshot, &Kind::Attribute.root_label())?
                    .unwrap()
                    .get_subtypes_transitive(self.snapshot, self.type_manager)?
                    .iter()
                    .map(|attribute| TypeAnnotation::Attribute(attribute.clone())),
            );
        }
        if include_roles {
            annotations.extend(
                self.type_manager
                    .get_role_type(self.snapshot, &Kind::Role.root_label())?
                    .unwrap()
                    .get_subtypes_transitive(self.snapshot, self.type_manager)?
                    .iter()
                    .map(|role| TypeAnnotation::RoleType(role.clone())),
            );
        }
        Ok(annotations)
    }

    fn get_annotation_for_type_label(
        &self,
        type_: &Type<Variable>,
    ) -> Result<Option<TypeAnnotation>, ConceptReadError> {
        if let Some(attribute) = self.type_manager.get_attribute_type(self.snapshot, &Label::build(&type_.type_))? {
            Ok(Some(TypeAnnotation::Attribute(attribute)))
        } else if let Some(entity) = self.type_manager.get_entity_type(self.snapshot, &Label::build(&type_.type_))? {
            Ok(Some(TypeAnnotation::Entity(entity)))
        } else if let Some(relation) =
            self.type_manager.get_relation_type(self.snapshot, &Label::build(&type_.type_))?
        {
            Ok(Some(TypeAnnotation::Relation(relation)))
        } else if let Some(role) = self.type_manager.get_role_type(self.snapshot, &Label::build(&type_.type_))? {
            Ok(Some(TypeAnnotation::RoleType(role)))
        } else {
            Ok(None)
        }
    }

    // Phase 2: Use constraints to infer annotations on other vertices
    fn propagate_vertex_annotations<'graph>(
        &self,
        tig: &mut TypeInferenceGraph<'graph>,
    ) -> Result<bool, ConceptReadError> {
        let mut is_modified = false;
        for c in &tig.conjunction.constraints().constraints {
            is_modified = is_modified | self.try_propagating_vertex_annotation(c, &mut tig.vertices)?;
        }

        // Propagate to & from nested disjunctions
        for nested in &mut tig.nested_disjunctions {
            is_modified = is_modified | self.reconcile_nested_disjunction(nested, &mut tig.vertices)?;
        }

        Ok(is_modified)
    }

    fn try_propagating_vertex_annotation<'conj>(
        &self,
        constraint: &'conj Constraint<Variable>,
        vertices: &mut BTreeMap<Variable, BTreeSet<TypeAnnotation>>,
    ) -> Result<bool, ConceptReadError> {
        let any_modified = match constraint {
            Constraint::Isa(isa) => self.try_propagating_vertex_annotation_impl(isa, vertices)?,
            Constraint::RolePlayer(role_player) => {
                if role_player.role_type.is_some() {
                    let relation_role = RelationRoleEdge { role_player };
                    let player_role = PlayerRoleEdge { role_player };
                    self.try_propagating_vertex_annotation_impl(&relation_role, vertices)?
                        || self.try_propagating_vertex_annotation_impl(&player_role, vertices)?
                } else {
                    todo!("Can we always have a role-player variable?")
                }
            }
            Constraint::Has(has) => self.try_propagating_vertex_annotation_impl(has, vertices)?,
            Constraint::Comparison(cmp) => self.try_propagating_vertex_annotation_impl(cmp, vertices)?,
            Constraint::ExpressionBinding(_) | Constraint::FunctionCallBinding(_) | Constraint::Type(_) => false,
        };
        Ok(any_modified)
    }

    fn try_propagating_vertex_annotation_impl<'conj>(
        &self,
        inner: &impl BinaryConstraintWrapper,
        vertices: &mut BTreeMap<Variable, BTreeSet<TypeAnnotation>>,
    ) -> Result<bool, ConceptReadError> {
        let (left, right) = (inner.left(), inner.right());
        let any_modified = match (vertices.get(&left), vertices.get(&right)) {
            (None, None) => false,
            (Some(_), Some(_)) => false,
            (Some(left_types), None) => {
                let left_to_right = inner.annotate_left_to_right(self, left_types)?;
                vertices.insert(right, left_to_right.values().flatten().map(|type_| type_.clone()).collect());
                true
            }
            (None, Some(right_types)) => {
                let right_to_left = inner.annotate_right_to_left(self, right_types)?;
                vertices.insert(left, right_to_left.values().flatten().map(|type_| type_.clone()).collect());
                true
            }
        };
        Ok(any_modified)
    }

    fn reconcile_nested_disjunction(
        &self,
        nested: &mut NestedTypeInferenceGraphDisjunction,
        parent_vertices: &mut VertexAnnotations,
    ) -> Result<bool, ConceptReadError> {
        let mut something_changed = false;
        // Apply annotations ot the parent on the nested
        for variable in nested.shared_variables.iter() {
            if let Some(parent_annotations) = parent_vertices.get_mut(variable) {
                for nested_tig in &mut nested.disjunction {
                    Self::intersect_unary(&mut nested_tig.vertices, *variable, Cow::Borrowed(parent_annotations));
                }
            }
        }

        // Propagate it within the child & recursively into nested
        for nested_tig in &mut nested.disjunction {
            something_changed = something_changed | self.propagate_vertex_annotations(nested_tig)?;
        }

        // Update shared variables of the disjunction
        let NestedTypeInferenceGraphDisjunction {
            shared_vertex_annotations,
            disjunction: nested_graph_disjunction,
            shared_variables,
        } = nested;
        for variable in shared_variables.iter() {
            if !shared_vertex_annotations.contains_key(variable) {
                if let Some(types_from_branches) =
                    self.try_union_annotations_across_all_branches(nested_graph_disjunction, *variable)
                {
                    shared_vertex_annotations.insert(*variable, types_from_branches);
                }
            }
        }

        // Update parent from the shared variables
        for (variable, types) in shared_vertex_annotations.iter() {
            if !parent_vertices.contains_key(variable) {
                parent_vertices.insert(*variable, types.clone());
                something_changed = true;
            }
        }
        Ok(something_changed)
    }

    fn try_union_annotations_across_all_branches(
        &self,
        disjunction: &Vec<TypeInferenceGraph<'_>>,
        variable: Variable,
    ) -> Option<BTreeSet<TypeAnnotation>> {
        if disjunction.iter().all(|nested_tig| nested_tig.vertices.contains_key(&variable)) {
            Some(
                disjunction
                    .iter()
                    .flat_map(|nested_tig| {
                        nested_tig.vertices.get(&variable).unwrap().iter().map(|type_| type_.clone())
                    })
                    .collect(),
            )
        } else {
            None
        }
    }

    fn intersect_unary(
        unary_annotations: &mut BTreeMap<Variable, BTreeSet<TypeAnnotation>>,
        variable: Variable,
        new_annotations: Cow<BTreeSet<TypeAnnotation>>,
    ) -> bool {
        if let Some(existing_annotations) = unary_annotations.get_mut(&variable) {
            let size_before = existing_annotations.len();
            existing_annotations.retain(|x| new_annotations.contains(x));
            existing_annotations.len() == size_before
        } else {
            unary_annotations.insert(variable, new_annotations.into_owned());
            true
        }
    }

    // Phase 3: seed edges
    fn seed_edges<'conj>(&self, tig: &mut TypeInferenceGraph<'conj>) -> Result<(), ConceptReadError> {
        let TypeInferenceGraph { conjunction, edges, vertices, .. } = tig;
        for constraint in &conjunction.constraints().constraints {
            match constraint {
                Constraint::Isa(isa) => edges.push(self.seed_edge(constraint, isa, vertices)?),
                Constraint::RolePlayer(role_player) => {
                    if role_player.role_type.is_some() {
                        let relation_role = RelationRoleEdge { role_player };
                        let player_role = PlayerRoleEdge { role_player };
                        edges.push(self.seed_edge(constraint, &relation_role, vertices)?);
                        edges.push(self.seed_edge(constraint, &player_role, vertices)?);
                    } else {
                        todo!("Can we always have a role-player variable?")
                    }
                }
                Constraint::Has(has) => edges.push(self.seed_edge(constraint, has, vertices)?),
                Constraint::Comparison(cmp) => todo!("self.seed_edge(cmp, &tig.vertices)"), // I'm not thrilled about this.
                Constraint::ExpressionBinding(_) | Constraint::FunctionCallBinding(_) | Constraint::Type(_) => {} // Do nothing
            }
        }
        for disj in &mut tig.nested_disjunctions {
            for nested_tig in &mut disj.disjunction {
                self.seed_edges(nested_tig)?;
            }
        }
        Ok(())
    }

    fn seed_edge<'conj>(
        &self,
        constraint: &'conj Constraint<Variable>,
        inner: &impl BinaryConstraintWrapper,
        vertices: &VertexAnnotations,
    ) -> Result<TypeInferenceEdge<'conj>, ConceptReadError> {
        let (left, right) = (inner.left(), inner.right());
        debug_assert!(vertices.contains_key(&left) && vertices.contains_key(&right));
        let left_to_right = inner.annotate_left_to_right(self, vertices.get(&left).unwrap())?;
        let right_to_left = inner.annotate_right_to_left(self, vertices.get(&right).unwrap())?;
        Ok(TypeInferenceEdge::build(constraint, left, right, left_to_right, right_to_left))
    }
}

pub trait BinaryConstraintWrapper {
    fn left(&self) -> Variable;
    fn right(&self) -> Variable;

    fn annotate_left_to_right(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        left_types: &BTreeSet<TypeAnnotation>,
    ) -> Result<BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>, ConceptReadError> {
        let mut left_to_right = BTreeMap::new();
        for left_type in left_types {
            let mut right_annotations = BTreeSet::new();
            self.annotate_left_to_right_for_type(seeder, left_type, &mut right_annotations)?;
            left_to_right.insert(left_type.clone(), right_annotations);
        }
        Ok(left_to_right)
    }

    fn annotate_right_to_left(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        right_types: &BTreeSet<TypeAnnotation>,
    ) -> Result<BTreeMap<TypeAnnotation, BTreeSet<TypeAnnotation>>, ConceptReadError> {
        let mut right_to_left = BTreeMap::new();
        for right_type in right_types {
            let mut left_annotations = BTreeSet::new();
            self.annotate_right_to_left_for_type(seeder, right_type, &mut left_annotations)?;
            right_to_left.insert(right_type.clone(), left_annotations);
        }
        Ok(right_to_left)
    }

    fn annotate_left_to_right_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        left_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError>;
    fn annotate_right_to_left_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        right_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError>;
}

impl BinaryConstraintWrapper for Has<Variable> {
    fn left(&self) -> Variable {
        self.owner()
    }

    fn right(&self) -> Variable {
        self.attribute()
    }

    fn annotate_left_to_right_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        left_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let owner = match left_type {
            TypeAnnotation::Entity(entity) => ObjectType::Entity(entity.clone()),
            TypeAnnotation::Relation(relation) => ObjectType::Relation(relation.clone()),
            _ => todo!("Return an error for using an attribute type here"),
        };
        owner
            .get_owns_transitive(seeder.snapshot, seeder.type_manager)?
            .iter()
            .map(|(attribute, _)| TypeAnnotation::Attribute(attribute.clone()))
            .for_each(|type_| {
                collector.insert(type_);
            });
        Ok(())
    }

    fn annotate_right_to_left_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        right_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let attribute = match right_type {
            TypeAnnotation::Attribute(attribute) => attribute,
            _ => todo!("Return an error for using a non-attribute where an attribute was expected"),
        };
        attribute
            .get_owners_transitive(seeder.snapshot, seeder.type_manager)?
            .iter()
            .map(|(owner, _)| match owner {
                ObjectType::Entity(entity) => TypeAnnotation::Entity(entity.clone()),
                ObjectType::Relation(relation) => TypeAnnotation::Relation(relation.clone()),
            })
            .for_each(|type_| {
                collector.insert(type_);
            });
        Ok(())
    }
}

impl BinaryConstraintWrapper for Isa<Variable> {
    fn left(&self) -> Variable {
        self.thing()
    }

    fn right(&self) -> Variable {
        self.type_()
    }

    fn annotate_left_to_right_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        left_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        match left_type {
            TypeAnnotation::Attribute(attribute) => {
                attribute
                    .get_supertypes(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::Attribute(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
            TypeAnnotation::Entity(entity) => {
                entity
                    .get_supertypes(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::Entity(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
            TypeAnnotation::Relation(relation) => {
                relation
                    .get_supertypes(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::Relation(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
            TypeAnnotation::RoleType(role_type) => {
                role_type
                    .get_supertypes(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::RoleType(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
        }
        collector.insert(left_type.clone());
        Ok(())
    }

    fn annotate_right_to_left_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        right_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        match right_type {
            TypeAnnotation::Attribute(attribute) => {
                attribute
                    .get_subtypes_transitive(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::Attribute(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
            TypeAnnotation::Entity(entity) => {
                entity
                    .get_subtypes_transitive(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::Entity(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
            TypeAnnotation::Relation(relation) => {
                relation
                    .get_subtypes_transitive(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::Relation(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
            TypeAnnotation::RoleType(role_type) => {
                role_type
                    .get_subtypes_transitive(seeder.snapshot, seeder.type_manager)?
                    .iter()
                    .map(|subtype| TypeAnnotation::RoleType(subtype.clone().into_owned()))
                    .for_each(|subtype| {
                        collector.insert(subtype);
                    });
            }
        }
        collector.insert(right_type.clone());
        Ok(())
    }
}

// TODO: This is very inefficient. If needed, We can replace uses by a specialised implementation which pre-computes attributes by value-type.
impl BinaryConstraintWrapper for Comparison<Variable> {
    fn left(&self) -> Variable {
        self.lhs()
    }

    fn right(&self) -> Variable {
        self.rhs()
    }

    fn annotate_left_to_right_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        left_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let left_value_type = match left_type {
            TypeAnnotation::Attribute(attribute) => attribute.get_value_type(seeder.snapshot, seeder.type_manager)?,
            _ => todo!("Error for expected attribute type"),
        };
        if let Some(value_type) = left_value_type {
            let comparable_types = TODO__comparable_value_types(value_type.category());
            let root_attribute =
                seeder.type_manager.get_attribute_type(seeder.snapshot, &Kind::Attribute.root_label())?.unwrap();
            for subattr in root_attribute.get_subtypes_transitive(seeder.snapshot, seeder.type_manager)?.iter() {
                if let Some(subvaluetype) = subattr.get_value_type(seeder.snapshot, seeder.type_manager)? {
                    if comparable_types.contains(&subvaluetype.category()) {
                        collector.insert(TypeAnnotation::Attribute(subattr.clone()));
                    }
                }
            }
        }
        Ok(())
    }

    fn annotate_right_to_left_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        right_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let right_value_type = match right_type {
            TypeAnnotation::Attribute(attribute) => attribute.get_value_type(seeder.snapshot, seeder.type_manager)?,
            _ => todo!("Error for expected attribute type"),
        };
        if let Some(value_type) = right_value_type {
            let comparable_types = TODO__comparable_value_types(value_type.category());
            let root_attribute =
                seeder.type_manager.get_attribute_type(seeder.snapshot, &Kind::Attribute.root_label())?.unwrap();
            for subattr in root_attribute.get_subtypes_transitive(seeder.snapshot, seeder.type_manager)?.iter() {
                if let Some(subvaluetype) = subattr.get_value_type(seeder.snapshot, seeder.type_manager)? {
                    if comparable_types.contains(&subvaluetype.category()) {
                        collector.insert(TypeAnnotation::Attribute(subattr.clone()));
                    }
                }
            }
        }
        Ok(())
    }
}

fn TODO__collect_value_types(
    seeder: &TypeSeeder<impl ReadableSnapshot>,
    types: &BTreeSet<TypeAnnotation>,
) -> Result<HashSet<ValueTypeCategory>, ConceptReadError> {
    let mut value_types = HashSet::new();
    for type_ in types {
        if let TypeAnnotation::Attribute(attr) = type_ {
            if let Some(value_type) = attr.get_value_type(seeder.snapshot, seeder.type_manager)? {
                value_types.insert(value_type.category());
            }
        }
    }
    Ok(value_types)
}

struct PlayerRoleEdge<'graph> {
    role_player: &'graph RolePlayer<Variable>,
}

struct RelationRoleEdge<'graph> {
    role_player: &'graph RolePlayer<Variable>,
}

impl<'graph> BinaryConstraintWrapper for PlayerRoleEdge<'graph> {
    fn left(&self) -> Variable {
        self.role_player.player
    }

    fn right(&self) -> Variable {
        self.role_player.role_type.unwrap()
    }

    fn annotate_left_to_right_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        left_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let player = match left_type {
            TypeAnnotation::Entity(entity) => ObjectType::Entity(entity.clone()),
            TypeAnnotation::Relation(relation) => ObjectType::Relation(relation.clone()),
            _ => todo!("Return an error for using an attribute type here"),
        };
        player
            .get_plays_transitive(seeder.snapshot, seeder.type_manager)?
            .iter()
            .map(|(role_type, _)| TypeAnnotation::RoleType(role_type.clone()))
            .for_each(|type_| {
                collector.insert(type_);
            });
        Ok(())
    }

    fn annotate_right_to_left_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        right_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let role_type = match right_type {
            TypeAnnotation::RoleType(role_type) => role_type,
            _ => todo!("Return an error for using a non-role where an role was expected"),
        };
        role_type
            .get_players_transitive(seeder.snapshot, seeder.type_manager)?
            .iter()
            .map(|(player, _)| match player {
                ObjectType::Entity(entity) => TypeAnnotation::Entity(entity.clone()),
                ObjectType::Relation(relation) => TypeAnnotation::Relation(relation.clone()),
            })
            .for_each(|type_| {
                collector.insert(type_);
            });
        Ok(())
    }
}

impl<'graph> BinaryConstraintWrapper for RelationRoleEdge<'graph> {
    fn left(&self) -> Variable {
        self.role_player.relation
    }

    fn right(&self) -> Variable {
        self.role_player.role_type.unwrap()
    }

    fn annotate_left_to_right_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        left_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let relation = match left_type {
            TypeAnnotation::Relation(relation) => relation.clone(),
            _ => todo!("Return an error for using a non-relation type here"),
        };
        relation
            .get_relates_transitive(seeder.snapshot, seeder.type_manager)?
            .iter()
            .map(|(role_type, _)| TypeAnnotation::RoleType(role_type.clone()))
            .for_each(|type_| {
                collector.insert(type_);
            });
        Ok(())
    }

    fn annotate_right_to_left_for_type(
        &self,
        seeder: &TypeSeeder<impl ReadableSnapshot>,
        right_type: &TypeAnnotation,
        collector: &mut BTreeSet<TypeAnnotation>,
    ) -> Result<(), ConceptReadError> {
        let role_type = match right_type {
            TypeAnnotation::RoleType(role_type) => role_type,
            _ => todo!("Return an error for using a non-role where an role was expected"),
        };
        role_type
            .get_relations_transitive(seeder.snapshot, seeder.type_manager)?
            .iter()
            .map(|relates| TypeAnnotation::Relation(relates.relation().clone()))
            .for_each(|type_| {
                collector.insert(type_);
            });
        Ok(())
    }
}

fn TODO__all_value_type_categories() -> [ValueTypeCategory; 9] {
    [
        ValueTypeCategory::Boolean,
        ValueTypeCategory::Long,
        ValueTypeCategory::Double,
        ValueTypeCategory::Decimal,
        ValueTypeCategory::DateTime,
        ValueTypeCategory::DateTimeTZ,
        ValueTypeCategory::Duration,
        ValueTypeCategory::String,
        ValueTypeCategory::Struct,
    ]
}

fn TODO__is_comparable(left: ValueTypeCategory, right: ValueTypeCategory) -> bool {
    match (left, right) {
        (ValueTypeCategory::Boolean, ValueTypeCategory::Boolean) => true,
        (ValueTypeCategory::Long, ValueTypeCategory::Long) => true,
        (ValueTypeCategory::Double, ValueTypeCategory::Double) => true,
        (ValueTypeCategory::Decimal, ValueTypeCategory::Decimal) => false,
        (ValueTypeCategory::String, ValueTypeCategory::String) => true,
        (ValueTypeCategory::DateTime, ValueTypeCategory::DateTime) => true,
        (ValueTypeCategory::DateTimeTZ, ValueTypeCategory::DateTimeTZ) => true,
        (ValueTypeCategory::Duration, ValueTypeCategory::Duration) => todo!(),
        (ValueTypeCategory::Struct, ValueTypeCategory::Struct) => false,

        (ValueTypeCategory::Double, ValueTypeCategory::Long) => true,
        (ValueTypeCategory::Long, ValueTypeCategory::Double) => true,

        (_, _) => false,
    }
}

fn TODO__comparable_value_types(with: ValueTypeCategory) -> HashSet<ValueTypeCategory> {
    TODO__all_value_type_categories().into_iter().filter(|other| TODO__is_comparable(with, *other)).collect()
}

#[cfg(test)]
pub mod tests {
    use std::{
        borrow::Borrow,
        collections::{BTreeMap, BTreeSet},
        sync::Arc,
    };

    use answer::Type as TypeAnnotation;
    use concept::{
        thing::thing_manager::ThingManager,
        type_::{
            annotation::AnnotationAbstract, attribute_type::AttributeTypeAnnotation, type_manager::TypeManager,
            Ordering, OwnerAPI,
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
    use storage::{
        durability_client::WALClient,
        snapshot::{CommittableSnapshot, ReadableSnapshot, WriteSnapshot},
        MVCCStorage,
    };
    use test_utils::{create_tmp_dir, init_logging};

    use crate::{
        inference::{
            pattern_type_inference::{infer_types_for_conjunction, tests::expected_edge, TypeInferenceGraph},
            seed_types::TypeSeeder,
        },
        pattern::conjunction::Conjunction,
    };

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

        let ((type_animal, type_cat, type_dog), (type_name, type_catname, type_dogname)) = {
            let mut schema_snapshot = storage.clone().open_snapshot_write();

            let name =
                type_manager.create_attribute_type(&mut schema_snapshot, &Label::build(&label_name), false).unwrap();
            let catname =
                type_manager.create_attribute_type(&mut schema_snapshot, &Label::build(&label_catname), false).unwrap();
            let dogname =
                type_manager.create_attribute_type(&mut schema_snapshot, &Label::build(&label_dogname), false).unwrap();
            name.set_annotation(
                &mut schema_snapshot,
                &type_manager,
                AttributeTypeAnnotation::Abstract(AnnotationAbstract),
            )
            .unwrap();
            catname.set_supertype(&mut schema_snapshot, &type_manager, name.clone()).unwrap();
            dogname.set_supertype(&mut schema_snapshot, &type_manager, name.clone()).unwrap();

            let animal =
                type_manager.create_entity_type(&mut schema_snapshot, &Label::build(&label_animal), false).unwrap();
            let cat = type_manager.create_entity_type(&mut schema_snapshot, &Label::build(&label_cat), false).unwrap();
            let dog = type_manager.create_entity_type(&mut schema_snapshot, &Label::build(&label_dog), false).unwrap();
            cat.set_supertype(&mut schema_snapshot, &type_manager, animal.clone()).unwrap();
            dog.set_supertype(&mut schema_snapshot, &type_manager, animal.clone()).unwrap();

            let animal_owns =
                animal.set_owns(&mut schema_snapshot, &type_manager, name.clone(), Ordering::Unordered).unwrap();
            let cat_owns =
                cat.set_owns(&mut schema_snapshot, &type_manager, catname.clone(), Ordering::Unordered).unwrap();
            let dog_owns =
                dog.set_owns(&mut schema_snapshot, &type_manager, dogname.clone(), Ordering::Unordered).unwrap();
            cat_owns.set_override(&mut schema_snapshot, &type_manager, animal_owns.clone()).unwrap();
            dog_owns.set_override(&mut schema_snapshot, &type_manager, animal_owns.clone()).unwrap();
            schema_snapshot.commit().unwrap();

            (
                (TypeAnnotation::Entity(animal), TypeAnnotation::Entity(cat), TypeAnnotation::Entity(dog)),
                (
                    TypeAnnotation::Attribute(name),
                    TypeAnnotation::Attribute(catname),
                    TypeAnnotation::Attribute(dogname),
                ),
            )
        };

        {
            // // Case 1: $a isa cat, has animal-name $n;
            let mut conjunction = Conjunction::new_root();
            let var_animal = conjunction.get_or_declare_variable("animal").unwrap();
            let var_name = conjunction.get_or_declare_variable(&"name").unwrap();
            let var_animal_type = conjunction.get_or_declare_variable(&"animal_type").unwrap();
            let var_name_type = conjunction.get_or_declare_variable(&"name_type").unwrap();

            // Try seeding
            {
                conjunction.constraints_mut().add_isa(var_animal, var_animal_type).unwrap();
                conjunction.constraints_mut().add_type(var_animal_type, &label_cat).unwrap();
                conjunction.constraints_mut().add_isa(var_name, var_name_type).unwrap();
                conjunction.constraints_mut().add_type(var_name_type, &label_name).unwrap();
                conjunction.constraints_mut().add_has(var_animal, var_name).unwrap();
            }

            let expected_tig = {
                let types_ta = BTreeSet::from([type_cat.clone()]);
                let types_a = BTreeSet::from([type_cat.clone()]);
                let types_tn = BTreeSet::from([type_name.clone()]);
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
                    vertices: BTreeMap::from([
                        (var_animal, types_a),
                        (var_name, types_n),
                        (var_animal_type, types_ta),
                        (var_name_type, types_tn),
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
                            vec![(type_cat.clone(), type_catname.clone())],
                        ),
                    ],
                    nested_disjunctions: vec![],
                    nested_negations: vec![],
                    nested_optionals: vec![],
                }
            };

            let snapshot = storage.clone().open_snapshot_write();
            let tig = infer_types_for_conjunction(&snapshot, type_manager.borrow(), &conjunction).unwrap();
            assert_eq!(expected_tig, tig);
        }
    }
}
