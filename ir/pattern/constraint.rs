/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    collections::HashMap,
    fmt::{Debug, Display, Formatter},
    iter::empty,
    sync::{Arc, Mutex},
};

use answer::variable::Variable;
use encoding::value::label::Label;
use itertools::Itertools;

use crate::{
    pattern::{
        context::PatternContext,
        expression::Expression,
        function_call::FunctionCall,
        variable_category::{VariableCategory, VariableOptionality},
        IrID, ScopeId,
    },
    PatternDefinitionError,
};

#[derive(Debug)]
pub struct Constraints {
    scope: ScopeId,
    context: Arc<Mutex<PatternContext>>,

    pub(crate) constraints: Vec<Constraint<Variable>>,

    // TODO: could also store indexes into the Constraints vec? Depends how expensive Constraints are and if we delete
    left_constrained_index: HashMap<Variable, Vec<Constraint<Variable>>>,
    right_constrained_index: HashMap<Variable, Vec<Constraint<Variable>>>,
    filter_constrained_index: HashMap<Variable, Vec<Constraint<Variable>>>,
}

impl Constraints {
    pub(crate) fn new(scope: ScopeId, context: Arc<Mutex<PatternContext>>) -> Self {
        Self {
            scope,
            context,
            constraints: Vec::new(),
            left_constrained_index: HashMap::new(),
            right_constrained_index: HashMap::new(),
            filter_constrained_index: HashMap::new(),
        }
    }

    fn add_constraint(&mut self, constraint: impl Into<Constraint<Variable>> + Clone) -> &Constraint<Variable> {
        let constraint = constraint.into();
        self.constraints.push(constraint.clone());
        constraint.ids_foreach(|var, side| match side {
            ConstraintIDSide::Left => {
                self.left_constrained_index.entry(var).or_insert_with(|| Vec::new()).push(constraint.clone());
            }
            ConstraintIDSide::Right => {
                self.right_constrained_index.entry(var).or_insert_with(|| Vec::new()).push(constraint.clone());
            }
            ConstraintIDSide::Filter => {
                self.filter_constrained_index.entry(var).or_insert_with(|| Vec::new()).push(constraint.clone());
            }
        });
        self.constraints.last().unwrap()
    }

    pub fn add_type(
        &mut self,
        variable: Variable,
        type_: &str,
    ) -> Result<&Constraint<Variable>, PatternDefinitionError> {
        debug_assert!(self.context.lock().unwrap().is_variable_available(self.scope, variable));
        let type_ = Type::new(variable, type_.to_string());
        self.context.lock().unwrap().set_variable_category(variable, VariableCategory::Type, type_.clone().into())?;
        Ok(self.add_constraint(type_))
    }

    pub fn add_isa(
        &mut self,
        thing: Variable,
        type_: Variable,
    ) -> Result<&Constraint<Variable>, PatternDefinitionError> {
        debug_assert!(
            self.context.lock().unwrap().is_variable_available(self.scope, thing)
                && self.context.lock().unwrap().is_variable_available(self.scope, type_),
        );
        let isa = Isa::new(thing, type_);
        self.context.lock().unwrap().set_variable_category(thing, VariableCategory::Thing, isa.clone().into())?;
        self.context.lock().unwrap().set_variable_category(type_, VariableCategory::Type, isa.clone().into())?;
        Ok(self.add_constraint(isa))
    }

    pub fn add_has(
        &mut self,
        owner: Variable,
        attribute: Variable,
    ) -> Result<&Constraint<Variable>, PatternDefinitionError> {
        debug_assert!(
            self.context.lock().unwrap().is_variable_available(self.scope, owner)
                && self.context.lock().unwrap().is_variable_available(self.scope, attribute)
        );
        let has = Has::new(owner, attribute);
        self.context.lock().unwrap().set_variable_category(owner, VariableCategory::Object, has.clone().into())?;
        self.context.lock().unwrap().set_variable_category(
            attribute,
            VariableCategory::Attribute,
            has.clone().into(),
        )?;
        self.add_constraint(has);
        Ok(self.constraints.last().unwrap())
    }

    pub fn add_role_player(
        &mut self,
        relation: Variable,
        player: Variable,
        role: Option<Variable>,
    ) -> Result<&Constraint<Variable>, PatternDefinitionError> {
        debug_assert!(
            self.context.lock().unwrap().is_variable_available(self.scope, relation)
                && self.context.lock().unwrap().is_variable_available(self.scope, player)
                && (role.is_none() || self.context.lock().unwrap().is_variable_available(self.scope, role.unwrap()))
        );
        let role_player = RolePlayer::new(relation, player, role);
        // TODO: Introduce relation category
        self.context.lock().unwrap().set_variable_category(
            relation,
            VariableCategory::Object,
            role_player.clone().into(),
        )?;
        self.context.lock().unwrap().set_variable_category(
            player,
            VariableCategory::Object,
            role_player.clone().into(),
        )?;
        if let Some(role_type) = role {
            self.context.lock().unwrap().set_variable_category(
                role_type,
                VariableCategory::RoleType,
                role_player.clone().into(),
            )?;
        }
        self.add_constraint(role_player);
        Ok(self.constraints.last().unwrap())
    }

    pub fn add_comparison(
        &mut self,
        lhs: Variable,
        rhs: Variable,
    ) -> Result<&Constraint<Variable>, PatternDefinitionError> {
        debug_assert!(
            self.context.lock().unwrap().is_variable_available(self.scope, lhs)
                && self.context.lock().unwrap().is_variable_available(self.scope, rhs)
        );
        let comparison = Comparison::new(lhs, rhs);
        // TODO: Introduce relation category
        self.context.lock().unwrap().set_variable_category(lhs, VariableCategory::Value, comparison.clone().into())?;
        self.context.lock().unwrap().set_variable_category(rhs, VariableCategory::Value, comparison.clone().into())?;
        self.add_constraint(comparison);
        Ok(self.constraints.last().unwrap())
    }

    pub fn add_function_call(
        &mut self,
        assigned: Vec<Variable>,
        function_call: FunctionCall<Variable>,
    ) -> Result<&Constraint<Variable>, PatternDefinitionError> {
        use PatternDefinitionError::FunctionCallReturnArgCountMismatch;
        debug_assert!(assigned.iter().all(|var| self.context.lock().unwrap().is_variable_available(self.scope, *var)));

        if assigned.len() != function_call.returns().len() {
            Err(FunctionCallReturnArgCountMismatch {
                assigned_var_count: assigned.len(),
                function_return_count: function_call.returns().len(),
            })?
        }

        let binding = FunctionCallBinding::new(assigned, function_call);

        for (index, var) in binding.ids().enumerate() {
            self.context.lock().unwrap().set_variable_category(
                var,
                binding.function_call().returns()[index].0,
                binding.clone().into(),
            )?;
            match binding.function_call.returns()[index].1 {
                VariableOptionality::Required => {}
                VariableOptionality::Optional => self.context.lock().unwrap().set_variable_is_optional(var),
            }
        }

        Ok(self.add_constraint(binding))
    }

    pub fn add_expression(
        &mut self,
        variable: Variable,
        expression: Expression<Variable>,
    ) -> Result<&Constraint<Variable>, PatternDefinitionError> {
        debug_assert!(self.context.lock().unwrap().is_variable_available(self.scope, variable));
        let binding = ExpressionBinding::new(variable, expression);
        self.context.lock().unwrap().set_variable_category(
            variable,
            VariableCategory::Value,
            binding.clone().into(),
        )?;
        Ok(self.add_constraint(binding))
    }
}

impl Display for Constraints {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for constraint in &self.constraints {
            let indent = (0..f.width().unwrap_or(0)).map(|_| " ").join("");
            writeln!(f, "{}{}", indent, constraint)?
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Constraint<ID: IrID> {
    Type(Type<ID>),
    Isa(Isa<ID>),
    RolePlayer(RolePlayer<ID>),
    Has(Has<ID>),
    ExpressionBinding(ExpressionBinding<ID>),
    FunctionCallBinding(FunctionCallBinding<ID>),
    Comparison(Comparison<ID>),
}

impl<ID: IrID> Constraint<ID> {
    pub fn ids(&self) -> Box<dyn Iterator<Item = ID> + '_> {
        match self {
            Constraint::Type(type_) => Box::new(type_.ids()),
            Constraint::Isa(isa) => Box::new(isa.ids()),
            Constraint::RolePlayer(rp) => Box::new(rp.ids()),
            Constraint::Has(has) => Box::new(has.ids()),
            Constraint::ExpressionBinding(binding) => todo!(),
            Constraint::FunctionCallBinding(binding) => Box::new(binding.ids()),
            Constraint::Comparison(comparison) => todo!(),
        }
    }

    pub fn ids_foreach<F>(&self, function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        match self {
            Constraint::Type(type_) => type_.ids_foreach(function),
            Constraint::Isa(isa) => isa.ids_foreach(function),
            Constraint::RolePlayer(rp) => rp.ids_foreach(function),
            Constraint::Has(has) => has.ids_foreach(function),
            Constraint::ExpressionBinding(binding) => todo!(),
            Constraint::FunctionCallBinding(binding) => binding.ids_foreach(function),
            Constraint::Comparison(comparison) => todo!(),
        }
    }

    fn as_type(&self) -> Option<&Type<ID>> {
        match self {
            Constraint::Type(type_) => Some(type_),
            _ => None,
        }
    }

    fn as_isa(&self) -> Option<&Isa<ID>> {
        match self {
            Constraint::Isa(isa) => Some(isa),
            _ => None,
        }
    }

    fn as_role_player(&self) -> Option<&RolePlayer<ID>> {
        match self {
            Constraint::RolePlayer(rp) => Some(rp),
            _ => None,
        }
    }

    fn as_has(&self) -> Option<&Has<ID>> {
        match self {
            Constraint::Has(has) => Some(has),
            _ => None,
        }
    }

    fn as_function_call_binding(&self) -> Option<&FunctionCallBinding<ID>> {
        match self {
            Constraint::FunctionCallBinding(binding) => Some(binding),
            _ => None,
        }
    }

    fn as_expression_binding(&self) -> Option<&ExpressionBinding<ID>> {
        match self {
            Constraint::ExpressionBinding(binding) => Some(binding),
            _ => None,
        }
    }
}

impl<ID: IrID> Display for Constraint<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Type(constraint) => Display::fmt(constraint, f),
            Constraint::Isa(constraint) => Display::fmt(constraint, f),
            Constraint::RolePlayer(constraint) => Display::fmt(constraint, f),
            Constraint::Has(constraint) => Display::fmt(constraint, f),
            Constraint::ExpressionBinding(constraint) => Display::fmt(constraint, f),
            Constraint::FunctionCallBinding(constraint) => Display::fmt(constraint, f),
            Constraint::Comparison(constraint) => Display::fmt(constraint, f),
        }
    }
}

enum ConstraintIDSide {
    Left,
    Right,
    Filter,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Type<ID: IrID> {
    pub(crate) left: ID,
    pub(crate) type_: String,
}

impl<ID: IrID> Type<ID> {
    fn new(identifier: ID, type_: String) -> Self {
        Self { left: identifier, type_ }
    }

    pub fn ids(&self) -> impl Iterator<Item = ID> + Sized {
        [self.left].into_iter()
    }

    pub fn ids_foreach<F>(&self, mut function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        function(self.left, ConstraintIDSide::Left)
    }
}

impl<ID: IrID> Into<Constraint<ID>> for Type<ID> {
    fn into(self) -> Constraint<ID> {
        Constraint::Type(self)
    }
}

impl<ID: IrID> Display for Type<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // TODO: implement indentation without rewriting it everywhere
        // write!(f, "{: >width$} {} type {}", "", self.left, self.type_, width=f.width().unwrap_or(0))
        write!(f, "{} type {}", self.left, self.type_)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Isa<ID: IrID> {
    thing: ID,
    type_: ID,
}

impl<ID: IrID> Isa<ID> {
    fn new(thing: ID, type_: ID) -> Self {
        Isa { thing, type_ }
    }

    pub fn ids(&self) -> impl Iterator<Item = ID> + Sized {
        [self.thing, self.type_].into_iter()
    }

    pub fn ids_foreach<F>(&self, mut function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        function(self.thing, ConstraintIDSide::Left);
        function(self.type_, ConstraintIDSide::Right)
    }

    pub(crate) fn thing(&self) -> ID {
        self.thing
    }

    pub(crate) fn type_(&self) -> ID {
        self.type_
    }
}

impl<ID: IrID> Into<Constraint<ID>> for Isa<ID> {
    fn into(self) -> Constraint<ID> {
        Constraint::Isa(self)
    }
}

impl<ID: IrID> Display for Isa<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} isa {}", self.thing, self.type_)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RolePlayer<ID: IrID> {
    pub(crate) relation: ID,
    pub(crate) player: ID,
    pub(crate) role_type: Option<ID>,
}

impl<ID: IrID> RolePlayer<ID> {
    pub fn new(relation: ID, player: ID, role_type: Option<ID>) -> Self {
        Self { relation, player, role_type }
    }

    pub fn relation(&self) -> ID {
        self.relation
    }

    pub fn player(&self) -> ID {
        self.player
    }

    pub fn ids(&self) -> impl Iterator<Item = ID> {
        [self.relation, self.player].into_iter().chain(self.role_type)
    }

    pub fn ids_foreach<F>(&self, mut function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        function(self.relation, ConstraintIDSide::Left);
        function(self.player, ConstraintIDSide::Right);
        match self.role_type.clone() {
            None => {}
            Some(role) => function(role, ConstraintIDSide::Filter),
        };
    }

    pub fn into_ids<T: IrID>(self, mapping: &HashMap<ID, T>) -> RolePlayer<T> {
        RolePlayer::new(
            *mapping.get(&self.relation).unwrap(),
            *mapping.get(&self.player).unwrap(),
            self.role_type.map(|rt| *mapping.get(&rt).unwrap()),
        )
    }
}

impl<ID: IrID> Into<Constraint<ID>> for RolePlayer<ID> {
    fn into(self) -> Constraint<ID> {
        Constraint::RolePlayer(self)
    }
}

impl<ID: IrID> Display for RolePlayer<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.role_type {
            None => {
                write!(f, "{} rp {} (role: )", self.relation, self.player)
            }
            Some(role) => {
                write!(f, "{} rp {} (role: {})", self.relation, self.player, role)
            }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Has<ID: IrID> {
    owner: ID,
    attribute: ID,
}

impl<ID: IrID> Has<ID> {
    fn new(owner: ID, attribute: ID) -> Self {
        Has { owner, attribute }
    }

    pub fn owner(&self) -> ID {
        self.owner
    }

    pub fn attribute(&self) -> ID {
        self.attribute
    }

    pub fn ids(&self) -> impl Iterator<Item = ID> {
        [self.owner, self.attribute].into_iter()
    }

    pub fn ids_foreach<F>(&self, mut function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        function(self.owner, ConstraintIDSide::Left);
        function(self.attribute, ConstraintIDSide::Right);
    }

    pub fn into_ids<T: IrID>(self, mapping: &HashMap<ID, T>) -> Has<T> {
        Has::new(*mapping.get(&self.owner).unwrap(), *mapping.get(&self.attribute).unwrap())
    }
}

impl<ID: IrID> Into<Constraint<ID>> for Has<ID> {
    fn into(self) -> Constraint<ID> {
        Constraint::Has(self)
    }
}

impl<ID: IrID> Display for Has<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} has {}", self.owner, self.attribute)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExpressionBinding<ID: IrID> {
    left: ID,
    expression: Expression<ID>,
}

impl<ID: IrID> ExpressionBinding<ID> {
    fn new(left: ID, expression: Expression<ID>) -> Self {
        Self { left, expression }
    }

    fn ids(&self) -> impl Iterator<Item = ID> {
        panic!("Unimplemented");
        empty()
    }

    pub fn ids_foreach<F>(&self, function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        todo!()
    }
}

impl<ID: IrID> Into<Constraint<ID>> for ExpressionBinding<ID> {
    fn into(self) -> Constraint<ID> {
        Constraint::ExpressionBinding(self)
    }
}

impl<ID: IrID> Display for ExpressionBinding<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.left, self.expression)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionCallBinding<ID: IrID> {
    left: Vec<ID>,
    function_call: FunctionCall<ID>,
}

impl<ID: IrID> FunctionCallBinding<ID> {
    fn new(left: Vec<ID>, function_call: FunctionCall<ID>) -> Self {
        Self { left, function_call }
    }

    pub(crate) fn function_call(&self) -> &FunctionCall<ID> {
        &self.function_call
    }

    pub fn ids(&self) -> impl Iterator<Item = ID> + '_ {
        self.left.iter().cloned()
    }

    pub fn ids_foreach<F>(&self, mut function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        for id in &self.left {
            function(*id, ConstraintIDSide::Left)
        }

        for id in self.function_call.call_id_mapping().keys() {
            function(*id, ConstraintIDSide::Right)
        }
    }
}

impl<ID: IrID> Into<Constraint<ID>> for FunctionCallBinding<ID> {
    fn into(self) -> Constraint<ID> {
        Constraint::FunctionCallBinding(self)
    }
}

impl<ID: IrID> Display for FunctionCallBinding<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.function_call.return_is_stream() {
            write!(f, "{} in {}", self.ids().map(|i| i.to_string()).join(", "), self.function_call())
        } else {
            write!(f, "{} = {}", self.ids().map(|i| i.to_string()).join(", "), self.function_call())
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Comparison<ID: IrID> {
    lhs: ID,
    rhs: ID,
    // comparator: Comparator,
}

impl<ID: IrID> Comparison<ID> {
    fn new(lhs: ID, rhs: ID) -> Self {
        Self { lhs, rhs }
    }

    pub fn lhs(&self) -> ID {
        self.lhs
    }

    pub fn rhs(&self) -> ID {
        self.rhs
    }

    pub fn ids(&self) -> impl Iterator<Item = ID> {
        [self.lhs, self.rhs].into_iter()
    }

    pub fn ids_foreach<F>(&self, mut function: F)
    where
        F: FnMut(ID, ConstraintIDSide) -> (),
    {
        function(self.lhs, ConstraintIDSide::Left);
        function(self.rhs, ConstraintIDSide::Right);
    }
}

impl<ID: IrID> Into<Constraint<ID>> for Comparison<ID> {
    fn into(self) -> Constraint<ID> {
        Constraint::Comparison(self)
    }
}

impl<ID: IrID> Display for Comparison<ID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
