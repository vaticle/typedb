/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};
use itertools::Itertools;

use encoding::{
    error::{EncodingError, EncodingError::UnexpectedPrefix},
    graph::type_::{
        vertex::{PrefixedTypeVertexEncoding, TypeVertex, TypeVertexEncoding},
        Kind,
    },
    layout::prefix::{Prefix, Prefix::VertexEntityType},
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
        annotation::{Annotation, AnnotationCategory, AnnotationAbstract},
        attribute_type::AttributeType,
        object_type::ObjectType,
        owns::Owns,
        plays::Plays,
        role_type::RoleType,
        type_manager::TypeManager,
        KindAPI, ObjectTypeAPI, Ordering, OwnerAPI, PlayerAPI, TypeAPI,
    },
    ConceptAPI,
};
use crate::type_::attribute_type::AttributeTypeAnnotation;
use crate::type_::role_type::RoleTypeAnnotation;
use crate::type_::type_manager::validation::SchemaValidationError;
use crate::type_::type_manager::validation::SchemaValidationError::UnsupportedAnnotationForType;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct EntityType<'a> {
    vertex: TypeVertex<'a>,
}

impl<'a> EntityType<'a> {}

impl<'a> ConceptAPI<'a> for EntityType<'a> {}

impl<'a> PrefixedTypeVertexEncoding<'a> for EntityType<'a> {
    const PREFIX: Prefix = VertexEntityType;
}
impl<'a> TypeVertexEncoding<'a> for EntityType<'a> {
    fn from_vertex(vertex: TypeVertex<'a>) -> Result<Self, EncodingError> {
        debug_assert!(Self::PREFIX == VertexEntityType);
        if vertex.prefix() != Prefix::VertexEntityType {
            Err(UnexpectedPrefix { expected_prefix: Prefix::VertexEntityType, actual_prefix: vertex.prefix() })
        } else {
            Ok(EntityType { vertex })
        }
    }

    fn into_vertex(self) -> TypeVertex<'a> {
        self.vertex
    }
}

impl<'a> TypeAPI<'a> for EntityType<'a> {
    type SelfStatic = EntityType<'static>;
    fn new(vertex: TypeVertex<'a>) -> EntityType<'a> {
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
        Ok(annotations.contains_key(&EntityTypeAnnotation::Abstract(AnnotationAbstract)))
    }

    fn delete<Snapshot: WritableSnapshot>(
        self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<(), ConceptWriteError> {
        // todo!("Validation");
        type_manager.delete_entity_type(snapshot, self)
    }

    fn get_label<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Label<'static>>, ConceptReadError> {
        type_manager.get_entity_type_label(snapshot, self.clone().into_owned())
    }
}

impl<'a> ObjectTypeAPI<'a> for EntityType<'a> {
    fn into_owned_object_type(self) -> ObjectType<'static> {
        ObjectType::Entity(self.into_owned())
    }
}

impl<'a> KindAPI<'a> for EntityType<'a> {
    type AnnotationType = EntityTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Entity;
}

impl<'a> EntityType<'a> {
    pub fn is_root<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
    ) -> Result<bool, ConceptReadError> {
        type_manager.get_entity_type_is_root(snapshot, self.clone().into_owned())
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
    ) -> Result<Option<EntityType<'_>>, ConceptReadError> {
        type_manager.get_entity_type_supertype(snapshot, self.clone().into_owned())
    }

    pub fn set_supertype<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        supertype: EntityType<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_entity_type_supertype(snapshot, self.clone().into_owned(), supertype)
    }

    pub fn get_supertypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<EntityType<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_supertypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<EntityType<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_subtypes(snapshot, self.clone().into_owned())
    }

    pub fn get_subtypes_transitive<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, Vec<EntityType<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_subtypes_transitive(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<EntityTypeAnnotation>>, ConceptReadError> {
        type_manager.get_entity_type_annotations_declared(snapshot, self.clone().into_owned())
    }

    pub fn get_annotations<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<EntityTypeAnnotation, EntityType<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_annotations(snapshot, self.clone().into_owned())
    }

    // pub fn get_annotation_categories<'m, Snapshot: ReadableSnapshot>(
    //     &self,
    //     snapshot: &Snapshot,
    //     type_manager: &'m TypeManager<Snapshot>,
    // ) -> Result<MaybeOwns<'m, HashMap<AnnotationCategory, EntityType<'static>>>, ConceptReadError> {
    //     type_manager.get_entity_type_annotation_categories(snapshot, self.clone().into_owned())
    // }
    //
    // pub fn get_annotation_of_category_if_exists<'m, Snapshot: ReadableSnapshot>(
    //     &self,
    //     snapshot: &Snapshot,
    //     type_manager: &'m TypeManager<Snapshot>,
    //     annotation_category: AnnotationCategory,
    // ) -> Result<EntityTypeAnnotation, ConceptReadError> {
    //     self.get_annotations(snapshot, type_manager).map(|annotations| {
    //         annotations.into_iter().filter(|(annotation, _)| annotation.).next
    //     })
    //
    // }

    pub fn set_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation: EntityTypeAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            EntityTypeAnnotation::Abstract(_) => {
                type_manager.set_annotation_abstract(snapshot, self.clone().into_owned())?
            }
        };
        Ok(())
    }

    pub fn unset_annotation<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        annotation_category: AnnotationCategory,
    ) -> Result<(), ConceptWriteError> {
        let entity_annotation = EntityTypeAnnotation::try_getting_default(annotation_category)
            .map_err(|source| ConceptWriteError::Operation {source})?;
        match entity_annotation {
            EntityTypeAnnotation::Abstract(_) => {
                type_manager.unset_owner_annotation_abstract(snapshot, self.clone().into_owned())?
            }
        }

        Ok(())
    }

    pub fn into_owned(self) -> EntityType<'static> {
        EntityType { vertex: self.vertex.into_owned() }
    }
}

impl<'a> OwnerAPI<'a> for EntityType<'a> {
    fn set_owns<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
        ordering: Ordering,
    ) -> Result<Owns<'static>, ConceptWriteError> {
        type_manager.set_owns(snapshot, self.clone().into_owned(), attribute_type.clone(), ordering)?;
        Ok(Owns::new(ObjectType::Entity(self.clone().into_owned()), attribute_type))
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
        type_manager.get_entity_type_owns_declared(snapshot, self.clone().into_owned())
    }

    fn get_owns<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_owns(snapshot, self.clone().into_owned())
    }

    fn get_owns_attribute<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<Owns<'static>>, ConceptReadError> {
        Ok(self.get_owns(snapshot, type_manager)?
            .iter()
            .map(|(_, owns)| owns)
            .find(|owns| owns.attribute() == attribute_type)
            .cloned()
        )
    }
}

impl<'a> PlayerAPI<'a> for EntityType<'a> {
    fn set_plays<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Plays<'static>, ConceptWriteError> {
        type_manager.set_plays(snapshot, self.clone().into_owned(), role_type.clone())
    }

    fn delete_plays<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: error if not playing
        type_manager.delete_plays(snapshot, self.clone().into_owned(), role_type)
    }

    fn get_plays_declared<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashSet<Plays<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_plays_declared(snapshot, self.clone().into_owned())
    }

    fn get_plays<'m, Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &'m TypeManager<Snapshot>,
    ) -> Result<MaybeOwns<'m, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        type_manager.get_entity_type_plays(snapshot, self.clone().into_owned())
    }

    fn get_plays_role<Snapshot: ReadableSnapshot>(
        &self,
        snapshot: &Snapshot,
        type_manager: &TypeManager<Snapshot>,
        role_type: RoleType<'static>,
    ) -> Result<Option<Plays<'static>>, ConceptReadError> {
        Ok(self.get_plays(snapshot, type_manager)?
            .iter()
            .map(|(_, plays)| plays)
            .find(|plays| plays.role() == role_type)
            .cloned()
        )
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum EntityTypeAnnotation {
    Abstract(AnnotationAbstract),
}

impl EntityTypeAnnotation {
    pub fn try_getting_default(annotation_category: AnnotationCategory) -> Result<EntityTypeAnnotation, SchemaValidationError> {
        annotation_category.to_default_annotation().into()
    }
}

impl From<Annotation> for Result<EntityTypeAnnotation, SchemaValidationError> {
    fn from(annotation: Annotation) -> Result<EntityTypeAnnotation, SchemaValidationError> {
        match annotation {
            Annotation::Abstract(annotation) => Ok(EntityTypeAnnotation::Abstract(annotation)),

            Annotation::Distinct(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Independent(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Unique(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Key(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Cardinality(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Regex(_) => Err(UnsupportedAnnotationForType(annotation.category())),
            Annotation::Cascade(_) => Err(UnsupportedAnnotationForType(annotation.category())),
        }
    }
}

impl From<Annotation> for EntityTypeAnnotation {
    fn from(annotation: Annotation) -> Self {
        let into_annotation: Result<EntityTypeAnnotation, SchemaValidationError> = annotation.into();
        match into_annotation {
            Ok(into_annotation) => into_annotation,
            Err(_) => unreachable!("Do not call this conversion from user-exposed code!"),
        }
    }
}

impl Into<Annotation> for EntityTypeAnnotation {
    fn into(self) -> Annotation {
        match self {
            EntityTypeAnnotation::Abstract(annotation) => Annotation::Abstract(annotation),
        }
    }
}

// impl<'a> IIDAPI<'a> for EntityType<'a> {
//     fn iid(&'a self) -> ByteReference<'a> {
//         self.vertex.bytes()
//     }
// }

// TODO: can we inline this into the macro invocation?
fn storage_key_to_entity_type(storage_key: StorageKey<'_, BUFFER_KEY_INLINE>) -> EntityType<'_> {
    EntityType::read_from(storage_key.into_bytes())
}

concept_iterator!(EntityTypeIterator, EntityType, storage_key_to_entity_type);
