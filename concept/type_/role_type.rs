/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use encoding::{
    error::{EncodingError, EncodingError::UnexpectedPrefix},
    graph::type_::{
        vertex::{PrefixedTypeVertexEncoding, TypeVertex, TypeVertexEncoding},
        Kind,
    },
    layout::prefix::Prefix,
    value::label::Label,
    Prefixed,
};
use lending_iterator::higher_order::Hkt;
use primitive::maybe_owns::MaybeOwns;
use resource::constants::snapshot::BUFFER_KEY_INLINE;
use storage::{
    key_value::StorageKey,
    snapshot::{ReadableSnapshot, WritableSnapshot},
};

use super::Ordering;
use crate::{
    concept_iterator,
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{Annotation, AnnotationAbstract},
        object_type::ObjectType,
        plays::Plays,
        relates::Relates,
        type_manager::TypeManager,
        KindAPI, TypeAPI,
    },
    ConceptAPI,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RoleType<'a> {
    vertex: TypeVertex<'a>,
}

impl<'a> RoleType<'a> {
    pub fn get_players_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        type_manager.get_plays_for_role_type_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_players<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<ObjectType<'static>, Plays<'static>>>, ConceptReadError> {
        type_manager.get_plays_for_role_type(snapshot, self.clone().into_owned())
    }

    pub fn get_ordering<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<Ordering, ConceptReadError> {
        type_manager.get_role_ordering(snapshot, self.clone().into_owned())
    }

    pub fn set_ordering<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        ordering: Ordering,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_role_ordering(snapshot, self.clone(), ordering)
    }
}

impl Hkt for RoleType<'static> {
    type HktSelf<'a> = Self;
}

impl<'a> ConceptAPI<'a> for RoleType<'a> {}

impl<'a> PrefixedTypeVertexEncoding<'a> for RoleType<'a> {
    const PREFIX: Prefix = Prefix::VertexRoleType;
}

impl<'a> TypeVertexEncoding<'a> for RoleType<'a> {
    fn from_vertex(vertex: TypeVertex<'a>) -> Result<Self, EncodingError> {
        debug_assert!(Self::PREFIX == Prefix::VertexRoleType);
        if vertex.prefix() != Prefix::VertexRoleType {
            Err(UnexpectedPrefix { expected_prefix: Prefix::VertexRoleType, actual_prefix: vertex.prefix() })
        } else {
            Ok(RoleType { vertex })
        }
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        self.vertex
    }
}

impl<'a> TypeAPI<'a> for RoleType<'a> {
    type SelfStatic = RoleType<'static>;

    fn new(vertex: TypeVertex<'a>) -> RoleType<'_> {
        Self::from_vertex(vertex).unwrap()
    }
    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        self.vertex.as_reference()
    }
    fn is_abstract<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        let annotations = self.get_annotations(snapshot, type_manager)?;
        Ok(annotations.contains(&RoleTypeAnnotation::Abstract(AnnotationAbstract)))
    }

    fn delete<Snapshot: WritableSnapshot>(
        self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: validation (Or better it in type_manager)
        type_manager.delete_role_type(snapshot, self)
    }

    fn get_label<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        type_manager.get_role_type_label(snapshot, self.clone().into_owned())
    }
}

impl<'a> RoleType<'a> {
    pub fn is_root<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        type_manager.get_role_type_is_root(snapshot, self.clone().into_owned())
    }

    pub fn set_name<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        name: &str,
    ) -> Result<(), ConceptWriteError> {
        if self.is_root(snapshot, type_manager)? {
            Err(ConceptWriteError::RootModification) // TODO: Move into TypeManager?
        } else {
            type_manager.set_role_type_name(snapshot, self.clone().into_owned(), name)
        }
    }

    pub fn get_supertype<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<Option<RoleType<'_>>, ConceptReadError> {
        type_manager.get_role_type_supertype(snapshot, self.clone().into_owned())
    }

    pub fn set_supertype<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        supertype: RoleType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_role_type_supertype(snapshot, self.clone().into_owned(), supertype)
    }

    pub fn get_supertypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RoleType<'static>>>, ConceptReadError> {
        type_manager.get_role_type_supertypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RoleType<'static>>>, ConceptReadError> {
        type_manager.get_role_type_subtypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RoleType<'static>>>, ConceptReadError> {
        type_manager.get_role_type_subtypes_transitive(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<RoleTypeAnnotation>>, ConceptReadError> {
        type_manager.get_role_type_annotations(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<RoleTypeAnnotation>>, ConceptReadError> {
        type_manager.get_role_type_annotations_declared(snapshot, self.clone().into_owned())
    }

    pub fn set_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: RoleTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            RoleTypeAnnotation::Abstract(_) => {
                type_manager.set_annotation_abstract(snapshot, self.clone().into_owned())?
            }
        };
        Ok(())
    }

    pub fn unset_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: RoleTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            RoleTypeAnnotation::Abstract(_) => {
                type_manager.unset_annotation_abstract(snapshot, self.clone().into_owned())?
            }
        }
        Ok(())
    }

    pub(crate) fn get_relates<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>
    ) -> Result<MaybeOwns<'m, Relates<'static>>, ConceptReadError> {
        type_manager.get_role_type_relates(snapshot, self.clone().into_owned())
    }

    pub fn into_owned(self) -> RoleType<'static> {
        RoleType { vertex: self.vertex.into_owned() }
    }
}

impl<'a> KindAPI<'a> for RoleType<'a> {
    type AnnotationType = RoleTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Role;
}

// --- Played API ---
impl<'a> RoleType<'a> {
    pub fn get_plays_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        type_manager.get_plays_for_role_type_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_plays<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<ObjectType<'static>, Plays<'static>>>, ConceptReadError> {
        type_manager.get_plays_for_role_type(snapshot, self.clone().into_owned())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum RoleTypeAnnotation {
    Abstract(AnnotationAbstract),
}

impl From<Annotation> for RoleTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Abstract(annotation) => RoleTypeAnnotation::Abstract(annotation),

            Annotation::Independent(_) => unreachable!("Independent annotation not available for Role type."),
            Annotation::Distinct(_) => unreachable!("Distinct annotation not available for Role type."),
            Annotation::Cardinality(_) => unreachable!("Cardinality annotation not available for Role type."),
            Annotation::Unique(_) => unreachable!("Unique annotation not available for Role type."),
            Annotation::Key(_) => unreachable!("Key annotation not available for Role type."),
            Annotation::Regex(_) => unreachable!("Regex annotation not available for Role type."),
        }
    }
}

impl Into<Annotation> for RoleTypeAnnotation {
    fn into(self) -> Annotation {
        match self {
            RoleTypeAnnotation::Abstract(annotation) => Annotation::Abstract(annotation),
        }
    }
}

// impl<'a> IIDAPI<'a> for RoleType<'a> {
//     fn iid(&'a self) -> ByteReference<'a> {
//         self.vertex.bytes()
//     }
// }

// TODO: can we inline this into the macro invocation?
fn storage_key_to_role_type(storage_key: StorageKey<'_, BUFFER_KEY_INLINE>) -> RoleType<'_> {
    RoleType::read_from(storage_key.into_bytes())
}

concept_iterator!(RoleTypeIterator, RoleType, storage_key_to_role_type);
