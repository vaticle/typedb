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
        annotation::{Annotation, AnnotationAbstract, AnnotationCascade},
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

    fn is_abstract<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        let annotations = self.get_annotations(snapshot, type_manager)?;
        Ok(annotations.contains_key(&RelationTypeAnnotation::Abstract(AnnotationAbstract)))
    }

    fn delete<Snapshot: WritableSnapshot>(
        self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: validation (Or better, do it in type_manager)
        type_manager.delete_relation_type(snapshot, self)
    }

    fn get_label<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
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
    pub fn is_root<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        type_manager.get_relation_type_is_root(snapshot, self.clone().into_owned())
    }

    pub fn set_label<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        label: &Label<'_>,
    ) -> Result<(), ConceptWriteError> {
        if self.is_root(snapshot, type_manager)? {
            Err(ConceptWriteError::RootModification)
        } else {
            type_manager.set_label(snapshot, self.clone().into_owned(), label)
        }
    }

    pub fn get_supertype<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<Option<RelationType<'static>>, ConceptReadError> {
        type_manager.get_relation_type_supertype(snapshot, self.clone().into_owned())
    }

    pub fn set_supertype<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        supertype: RelationType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_relation_type_supertype(snapshot, self.clone().into_owned(), supertype)
    }

    pub fn get_supertypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_supertypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_subtypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_subtypes_transitive(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<RelationTypeAnnotation>>, ConceptReadError> {
        type_manager.get_relation_type_annotations_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<RelationTypeAnnotation, RelationType<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_annotations(snapshot, self.clone().into_owned())
    }

    pub fn set_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: RelationTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.set_annotation_abstract(snapshot, self.clone().into_owned())?
            },
            RelationTypeAnnotation::Cascade(_) => {
                type_manager.set_annotation_abstract(snapshot, self.clone().into_owned())?
            },
        };
        Ok(())
    }

    pub fn unset_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: RelationTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.unset_owner_annotation_abstract(snapshot, self.clone().into_owned())?
            },
            RelationTypeAnnotation::Cascade(_) => {
                type_manager.unset_annotation_abstract(snapshot, self.clone().into_owned())?
            },
        }
        Ok(()) // TODO
    }

    pub fn create_relates<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        name: &str,
        ordering: Ordering,
    ) -> Result<RoleType<'static>, ConceptWriteError> {
        let label = Label::build_scoped(name, self.get_label(snapshot, type_manager).unwrap().name().as_str());
        type_manager.create_role_type(snapshot, &label, self.clone().into_owned(), false, ordering)
    }

    pub fn get_relates_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Relates<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_relates_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_relates<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<RoleType<'static>, Relates<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_relates(snapshot, self.clone().into_owned())
    }

    // TODO: It looks like a hack to me right now..... Why don't we search it, but build a new one?
    pub fn get_relates_of_role<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_name: &str,
    ) -> Result<Option<Relates<'static>>, ConceptReadError> {
        let role_label = Label::build_scoped(role_name, self.get_label(snapshot, type_manager)?.name().as_str());
        Ok(type_manager
            .get_role_type(snapshot, &role_label)?
            .map(|role_type| Relates::new(self.clone().into_owned(), role_type)))
    }

    pub fn into_owned(self) -> RelationType<'static> {
        RelationType { vertex: self.vertex.into_owned() }
    }
}

impl<'a> OwnerAPI<'a> for RelationType<'a> {
    fn set_owns<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Result<Owns<'static>, ConceptWriteError> {
        type_manager.set_owns(snapshot, self.clone().into_owned(), attribute_type.clone(), ordering)?;
        Ok(Owns::new(ObjectType::Relation(self.clone().into_owned()), attribute_type))
    }

    fn delete_owns<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: error if not owned?
        type_manager.delete_owns(snapshot, self.clone().into_owned(), attribute_type)?;
        Ok(())
    }

    fn get_owns_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Owns<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_owns_declared(snapshot, self.clone().into_owned())
    }

    fn get_owns<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_owns(snapshot, self.clone().into_owned())
    }

    fn get_owns_attribute<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        let expected_owns = Owns::new(ObjectType::Relation(self.clone().into_owned()), attribute_type);
        Ok(self.get_owns_declared(snapshot, type_manager)?.contains(&expected_owns).then_some(expected_owns))
    }
}

impl<'a> PlayerAPI<'a> for RelationType<'a> {
    fn set_plays<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Plays<'static>, ConceptWriteError> {
        // TODO: decide behaviour (ok or error) if already playing
        type_manager.set_plays(snapshot, self.clone().into_owned(), role_type.clone())
    }

    fn delete_plays<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: error if not playing?
        type_manager.delete_plays(snapshot, self.clone().into_owned(), role_type)
    }

    fn get_plays_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_plays_declared(snapshot, self.clone().into_owned())
    }

    fn get_plays<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        type_manager.get_relation_type_plays(snapshot, self.clone().into_owned())
    }

    fn get_plays_role<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        let expected_plays = Plays::new(ObjectType::Relation(self.clone().into_owned()), role_type);
        Ok(self.get_plays_declared(snapshot, type_manager)?.contains(&expected_plays).then_some(expected_plays))
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum RelationTypeAnnotation {
    Abstract(AnnotationAbstract),
    Cascade(AnnotationCascade),
}

impl From<Annotation> for RelationTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        match annotation {
            Annotation::Abstract(annotation) => RelationTypeAnnotation::Abstract(annotation),
            Annotation::Cascade(annotation) => RelationTypeAnnotation::Cascade(annotation),

            Annotation::Distinct(_) => unreachable!("Distinct annotation not available for Relation type."),
            Annotation::Independent(_) => unreachable!("Independent annotation not available for Relation type."),
            Annotation::Unique(_) => unreachable!("Unique annotation not available for Relation type."),
            Annotation::Key(_) => unreachable!("Key annotation not available for Relation type."),
            Annotation::Cardinality(_) => unreachable!("Cardinality annotation not available for Relation type."),
            Annotation::Regex(_) => unreachable!("Regex annotation not available for Relation type."),
        }
    }
}

impl Into<Annotation> for RelationTypeAnnotation {
    fn into(self) -> Annotation {
        match self {
            RelationTypeAnnotation::Abstract(annotation) => Annotation::Abstract(annotation),
            RelationTypeAnnotation::Cascade(annotation) => Annotation::Cascade(annotation),
        }
    }
}

// TODO: can we inline this into the macro invocation?
fn storage_key_to_relation_type(storage_key: StorageKey<'_, BUFFER_KEY_INLINE>) -> RelationType<'_> {
    RelationType::read_from(storage_key.into_bytes())
}

concept_iterator!(RelationTypeIterator, RelationType, storage_key_to_relation_type);
