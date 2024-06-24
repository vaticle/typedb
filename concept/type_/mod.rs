/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use bytes::{byte_reference::ByteReference, Bytes};
use encoding::{
    graph::type_::{
        edge::TypeEdgeEncoding,
        property::{TypeEdgePropertyEncoding, TypeVertexPropertyEncoding},
        vertex::{PrefixedTypeVertexEncoding, TypeVertex, TypeVertexEncoding},
        Kind,
    },
    layout::infix::Infix,
    value::label::Label,
    AsBytes,
};
use primitive::maybe_owns::MaybeOwns;
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use serde::{Deserialize, Serialize};
use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::Annotation, attribute_type::AttributeType, object_type::ObjectType, owns::Owns, plays::Plays,
        role_type::RoleType, type_manager::TypeManager,
    },
    ConceptAPI,
};

pub mod annotation;
pub mod attribute_type;
pub mod entity_type;
pub mod object_type;
pub mod owns;
mod plays;
mod relates;
pub mod relation_type;
pub mod role_type;
pub mod sub;
pub mod type_manager;

pub trait TypeAPI<'a>: ConceptAPI<'a> + TypeVertexEncoding<'a> + Sized + Clone + Hash + Eq + 'a {
    type SelfStatic: KindAPI<'static> + 'static;
    fn new(vertex: TypeVertex<'a>) -> Self;

    fn read_from(b: Bytes<'a, BUFFER_KEY_INLINE>) -> Self {
        Self::from_bytes(b).unwrap()
    }

    fn vertex(&self) -> TypeVertex<'_>;

    fn is_abstract(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
    ) -> Result<bool, ConceptReadError>;

    fn delete(self, snapshot: &mut impl WritableSnapshot, type_manager: &TypeManager) -> Result<(), ConceptWriteError>;

    fn get_label<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError>;
}

pub trait KindAPI<'a>: TypeAPI<'a> + PrefixedTypeVertexEncoding<'a> {
    type AnnotationType: Hash + Eq + From<Annotation>;
    const ROOT_KIND: Kind;
}

pub trait ObjectTypeAPI<'a>: TypeAPI<'a> + OwnerAPI<'a> {
    fn into_owned_object_type(self) -> ObjectType<'static>;
}

pub trait OwnerAPI<'a>: TypeAPI<'a> {
    fn set_owns(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Result<Owns<'static>, ConceptWriteError>;

    fn delete_owns(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError>;

    fn get_owns<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError>;

    fn get_owns_attribute(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError>;

    fn has_owns_attribute(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<bool, ConceptReadError> {
        Ok(self.get_owns_attribute(snapshot, type_manager, attribute_type)?.is_some())
    }

    fn get_owns_transitive<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError>;

    fn get_owns_attribute_transitive<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        Ok(self.get_owns_transitive(snapshot, type_manager)?.get(&attribute_type).map(|owns| owns.clone()))
    }

    fn has_owns_attribute_transitive(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<bool, ConceptReadError> {
        Ok(self.get_owns_attribute_transitive(snapshot, type_manager, attribute_type)?.is_some())
    }
}

pub trait PlayerAPI<'a>: TypeAPI<'a> {
    fn set_plays(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<Plays<'static>, ConceptWriteError>;

    fn delete_plays(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<(), ConceptWriteError>;

    fn get_plays<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError>;

    fn get_plays_role(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError>;

    fn has_plays_role(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<bool, ConceptReadError> {
        Ok(self.get_plays_role(snapshot, type_manager, role_type)?.is_some())
    }

    fn get_plays_transitive<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError>;

    fn get_plays_role_transitive(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        Ok(self.get_plays_transitive(snapshot, type_manager)?.get(&role_type).map(|plays| plays.clone()))
    }

    fn has_plays_role_transitive(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<bool, ConceptReadError> {
        Ok(self.get_plays_role_transitive(snapshot, type_manager, role_type)?.is_some())
    }
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Ordering {
    // ##########################################################################
    // ###### WARNING: any changes here may break backwards compatibility! ######
    // ##########################################################################
    Unordered,
    Ordered,
}

impl<'a> TypeVertexPropertyEncoding<'a> for Ordering {
    const INFIX: Infix = Infix::PropertyOrdering;

    fn from_value_bytes(value: ByteReference<'_>) -> Ordering {
        bincode::deserialize(value.bytes()).unwrap()
    }

    fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
        Some(Bytes::copy(bincode::serialize(&self).unwrap().as_slice()))
    }
}

impl<'a> TypeEdgePropertyEncoding<'a> for Ordering {
    const INFIX: Infix = Infix::PropertyOrdering;

    fn from_value_bytes(value: ByteReference<'_>) -> Ordering {
        bincode::deserialize(value.bytes()).unwrap()
    }

    fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
        Some(Bytes::copy(bincode::serialize(&self).unwrap().as_slice()))
    }
}

pub(crate) trait InterfaceImplementation<'a>:
    TypeEdgeEncoding<'a, From = Self::ObjectType, To = Self::InterfaceType> + Sized + Clone + Hash + Eq + 'a
{
    type AnnotationType;
    type ObjectType: TypeAPI<'a>;
    type InterfaceType: KindAPI<'a>;

    fn object(&self) -> Self::ObjectType;

    fn interface(&self) -> Self::InterfaceType;

    fn unwrap_annotation(annotation: Self::AnnotationType) -> Annotation;
}

pub struct EdgeOverride<EDGE: TypeEdgeEncoding<'static>> {
    overridden: EDGE, // TODO: Consider storing EDGE::To instead
}

impl<'a, EDGE: TypeEdgeEncoding<'static>> TypeEdgePropertyEncoding<'a> for EdgeOverride<EDGE> {
    const INFIX: Infix = Infix::PropertyOverride;

    fn from_value_bytes(value: ByteReference<'_>) -> Self {
        Self { overridden: EDGE::decode_canonical_edge(Bytes::Reference(value).into_owned()) }
    }

    fn to_value_bytes(self) -> Option<Bytes<'a, BUFFER_VALUE_INLINE>> {
        Some(Bytes::Reference(self.overridden.to_canonical_type_edge().bytes()).into_owned())
    }
}
