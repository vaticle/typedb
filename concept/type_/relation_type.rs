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
    layout::prefix::{Prefix, Prefix::VertexRelationType},
    value::label::Label,
    Prefixed,
};
use primitive::maybe_owns::MaybeOwns;
use resource::constants::snapshot::BUFFER_KEY_INLINE;
use storage::{
    key_value::StorageKey,
    snapshot::{ReadableSnapshot, WritableSnapshot},
};

use crate::{
    concept_iterator,
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{Annotation, AnnotationAbstract},
        attribute_type::AttributeType,
        object_type::ObjectType,
        owns::Owns,
        plays::Plays,
        relates::Relates,
        role_type::RoleType,
        type_manager::TypeManager,
        KindAPI, ObjectTypeAPI, Ordering, OwnerAPI, PlayerAPI, TypeAPI,
    },
    ConceptAPI,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RelationType<'a> {
    vertex: TypeVertex<'a>,
}

impl<'a> RelationType<'a> {}

impl<'a> ConceptAPI<'a> for RelationType<'a> {}

impl<'a> TypeVertexEncoding<'a> for RelationType<'a> {
    fn from_vertex(vertex: TypeVertex<'a>) -> Result<Self, EncodingError> {
        debug_assert!(Self::PREFIX == VertexRelationType);
        if vertex.prefix() != Prefix::VertexRelationType {
            Err(UnexpectedPrefix { expected_prefix: Prefix::VertexRelationType, actual_prefix: vertex.prefix() })
        } else {
            Ok(RelationType { vertex })
        }
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        self.vertex
    }
}

impl<'a> PrefixedTypeVertexEncoding<'a> for RelationType<'a> {
    const PREFIX: Prefix = VertexRelationType;
}

impl<'a> TypeAPI<'a> for RelationType<'a> {
    type SelfStatic = RelationType<'static>;

    fn new(vertex: TypeVertex<'a>) -> RelationType<'_> {
        Self::from_vertex(vertex).unwrap()
    }

    fn vertex<'this>(&'this self) -> TypeVertex<'this> {
        self.vertex.as_reference()
    }

    fn is_abstract(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
    ) -> Result<bool, ConceptReadError> {
        let annotations = self.get_annotations(snapshot, type_manager)?;
        Ok(annotations.contains(&RelationTypeAnnotation::Abstract(AnnotationAbstract)))
    }

    fn delete(self, snapshot: &mut impl WritableSnapshot, type_manager: &TypeManager) -> Result<(), ConceptWriteError> {
        // TODO: validation (Or better, do it in type_manager)
        type_manager.delete_relation_type(snapshot, self)
    }

    fn get_label<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        type_manager.get_relation_type_label(snapshot, self.clone().into_owned())
    }
}

impl<'a> KindAPI<'a> for RelationType<'a> {
    type AnnotationType = RelationTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Relation;
}

impl<'a> ObjectTypeAPI<'a> for RelationType<'a> {
    fn into_owned_object_type(self) -> ObjectType<'static> {
        ObjectType::Relation(self.into_owned())
    }
}

impl<'a> RelationType<'a> {
    pub fn is_root(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
    ) -> Result<bool, ConceptReadError> {
        type_manager.get_relation_type_is_root(snapshot, self.clone().into_owned())
    }

    pub fn set_label(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        label: &Label<'_>,
    ) -> Result<(), ConceptWriteError> {
        if self.is_root(snapshot, type_manager)? {
            Err(ConceptWriteError::RootModification)
        } else {
            type_manager.set_label(snapshot, self.clone().into_owned(), label)
        }
    }

    pub fn get_supertype(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
    ) -> Result<Option<RelationType<'static>>, ConceptReadError> {
        type_manager.get_relation_type_supertype(snapshot, self.clone().into_owned())
    }

    pub fn set_supertype(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        supertype: RelationType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_relation_type_supertype(snapshot, self.clone().into_owned(), supertype)
    }

    pub fn get_supertypes<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_supertypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_subtypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_subtypes_transitive(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<RelationTypeAnnotation>>, ConceptReadError> {
        type_manager.get_relation_type_annotations(snapshot, self.clone().into_owned())
    }

    pub fn set_annotation(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        annotation: RelationTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.set_annotation_abstract(snapshot, self.clone().into_owned())
            }
        };
        Ok(())
    }

    fn delete_annotation(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        annotation: RelationTypeAnnotation,
    ) {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.delete_annotation_abstract(snapshot, self.clone().into_owned())
            }
        }
    }

    pub fn create_relates(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        name: &str,
        ordering: Ordering,
    ) -> Result<RoleType<'static>, ConceptWriteError> {
        let label = Label::build_scoped(name, self.get_label(snapshot, type_manager).unwrap().name().as_str());
        type_manager.create_role_type(snapshot, &label, self.clone().into_owned(), false, ordering)
    }

    pub fn get_relates<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<Relates<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_relates(snapshot, self.clone().into_owned())
    }

    pub fn get_relates_role(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        name: &str,
    ) -> Result<Option<Relates<'static>>, ConceptReadError> {
        let label = Label::build_scoped(name, self.get_label(snapshot, type_manager)?.name().as_str());
        Ok(type_manager
            .get_role_type(snapshot, &label)?
            .map(|role_type| Relates::new(self.clone().into_owned(), role_type)))
    }

    pub fn get_relates_transitive<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashMap<RoleType<'static>, Relates<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_relates_transitive(snapshot, self.clone().into_owned())
    }

    pub fn get_relates_role_transitive<'b>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'b>,
    ) -> Result<Option<Relates<'static>>, ConceptReadError> {
        Ok(self.get_relates_transitive(snapshot, type_manager)?.get(&role_type).cloned())
    }

    fn has_relates_role(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        name: &str,
    ) -> Result<bool, ConceptReadError> {
        Ok(self.get_relates_role(snapshot, type_manager, name)?.is_some())
    }

    pub fn into_owned(self) -> RelationType<'static> {
        RelationType { vertex: self.vertex.into_owned() }
    }
}

impl<'a> OwnerAPI<'a> for RelationType<'a> {
    fn set_owns(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Result<Owns<'static>, ConceptWriteError> {
        type_manager.set_owns(snapshot, self.clone().into_owned(), attribute_type.clone(), ordering);
        Ok(Owns::new(ObjectType::Relation(self.clone().into_owned()), attribute_type))
    }

    fn delete_owns(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: error if not owned?
        type_manager.delete_owns(snapshot, self.clone().into_owned(), attribute_type);
        Ok(())
    }

    fn get_owns<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_owns(snapshot, self.clone().into_owned())
    }

    fn get_owns_attribute(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        let expected_owns = Owns::new(ObjectType::Relation(self.clone().into_owned()), attribute_type);
        Ok(self.get_owns(snapshot, type_manager)?.contains(&expected_owns).then_some(expected_owns))
    }

    fn get_owns_transitive<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_owns_transitive(snapshot, self.clone().into_owned())
    }
}

impl<'a> PlayerAPI<'a> for RelationType<'a> {
    fn set_plays(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<Plays<'static>, ConceptWriteError> {
        // TODO: decide behaviour (ok or error) if already playing
        type_manager.set_plays(snapshot, self.clone().into_owned(), role_type.clone())
    }

    fn delete_plays(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: error if not playing?
        type_manager.delete_plays(snapshot, self.clone().into_owned(), role_type)
    }

    fn get_plays<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_plays(snapshot, self.clone().into_owned())
    }

    fn get_plays_role(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        let expected_plays = Plays::new(ObjectType::Relation(self.clone().into_owned()), role_type);
        Ok(self.get_plays(snapshot, type_manager)?.contains(&expected_plays).then_some(expected_plays))
    }

    fn get_plays_transitive<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_plays_transitive(snapshot, self.clone().into_owned())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum RelationTypeAnnotation {
    Abstract(AnnotationAbstract),
}

impl From<Annotation> for RelationTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Abstract(annotation) => RelationTypeAnnotation::Abstract(annotation),

            Annotation::Distinct(_) => unreachable!("Distinct annotation not available for Relation type."),
            Annotation::Independent(_) => unreachable!("Independent annotation not available for Relation type."),
            Annotation::Unique(_) => unreachable!("Unique annotation not available for Relation type."),
            Annotation::Key(_) => unreachable!("Key annotation not available for Relation type."),
            Annotation::Cardinality(_) => unreachable!("Cardinality annotation not available for Relation type."),
            Annotation::Regex(_) => unreachable!("Regex annotation not available for Relation type."),
        }
    }
}

// TODO: can we inline this into the macro invocation?
fn storage_key_to_relation_type(storage_key: StorageKey<'_, BUFFER_KEY_INLINE>) -> RelationType<'_> {
    RelationType::read_from(storage_key.into_bytes())
}

concept_iterator!(RelationTypeIterator, RelationType, storage_key_to_relation_type);
