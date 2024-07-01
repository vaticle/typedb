/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
    sync::Arc,
};

use encoding::{
    error::EncodingError,
    graph::{
        definition::{
            definition_key::DefinitionKey,
            definition_key_generator::DefinitionKeyGenerator,
            r#struct::{StructDefinition, StructDefinitionField},
        },
        type_::{
            edge::TypeEdgeEncoding,
            property::TypeEdgePropertyEncoding,
            vertex::{PrefixedTypeVertexEncoding, TypeVertexEncoding},
            vertex_generator::TypeVertexGenerator,
            Kind,
        },
    },
    value::{label::Label, value_type::ValueType},
    AsBytes, Keyable,
};
use primitive::maybe_owns::MaybeOwns;
use resource::constants::encoding::StructFieldIDUInt;
use storage::{
    durability_client::DurabilityClient,
    snapshot::{CommittableSnapshot, ReadableSnapshot, WritableSnapshot, WriteSnapshot},
    MVCCStorage,
};
use type_cache::TypeCache;
use type_writer::TypeWriter;
use validation::{commit_time_validation::CommitTimeValidation, operation_time_validation::OperationTimeValidation};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{AnnotationCategory, AnnotationDistinct, AnnotationIndependent, AnnotationKey, AnnotationRegex, AnnotationUnique, AnnotationAbstract, AnnotationCardinality, AnnotationCascade},
        attribute_type::{AttributeType, AttributeTypeAnnotation},
        entity_type::{EntityType, EntityTypeAnnotation},
        object_type::ObjectType,
        owns::{Owns, OwnsAnnotation},
        plays::{Plays, PlaysAnnotation},
        relates::{Relates, RelatesAnnotation},
        relation_type::{RelationType, RelationTypeAnnotation},
        role_type::{RoleType, RoleTypeAnnotation},
        type_manager::type_reader::TypeReader,
        InterfaceImplementation, ObjectTypeAPI, Ordering, OwnerAPI, PlayerAPI, KindAPI, TypeAPI,
    },
};
use crate::type_::annotation::Annotation;

pub mod type_cache;
pub mod type_reader;
mod type_writer;
pub mod validation;

// TODO: this should be parametrised into the database options? Would be great to have it be changable at runtime!
pub(crate) const RELATION_INDEX_THRESHOLD: u64 = 8;

pub struct TypeManager<Snapshot> {
    vertex_generator: Arc<TypeVertexGenerator>,
    definition_key_generator: Arc<DefinitionKeyGenerator>,
    type_cache: Option<Arc<TypeCache>>,
    snapshot: PhantomData<Snapshot>,
}

impl<Snapshot> TypeManager<Snapshot> {
    pub fn initialise_types<D: DurabilityClient>(
        storage: Arc<MVCCStorage<D>>,
        definition_key_generator: Arc<DefinitionKeyGenerator>,
        vertex_generator: Arc<TypeVertexGenerator>,
    ) -> Result<(), ConceptWriteError> {
        let mut snapshot = storage.clone().open_snapshot_write();
        {
            let type_manager =
                TypeManager::<WriteSnapshot<D>>::new(definition_key_generator, vertex_generator.clone(), None);
            let root_entity = type_manager.create_entity_type(&mut snapshot, &Kind::Entity.root_label(), true)?;
            root_entity.set_annotation(
                &mut snapshot,
                &type_manager,
                EntityTypeAnnotation::Abstract(AnnotationAbstract),
            )?;
            let root_relation = type_manager.create_relation_type(&mut snapshot, &Kind::Relation.root_label(), true)?;
            root_relation.set_annotation(
                &mut snapshot,
                &type_manager,
                RelationTypeAnnotation::Abstract(AnnotationAbstract),
            )?;
            let root_role = type_manager.create_role_type(
                &mut snapshot,
                &Kind::Role.root_label(),
                root_relation.clone(), // TODO: Do we need to clone here????
                true,
                Ordering::Unordered,
            )?;
            root_role.set_annotation(&mut snapshot, &type_manager, RoleTypeAnnotation::Abstract(AnnotationAbstract))?;
            let root_attribute =
                type_manager.create_attribute_type(&mut snapshot, &Kind::Attribute.root_label(), true)?;
            root_attribute.set_annotation(
                &mut snapshot,
                &type_manager,
                AttributeTypeAnnotation::Abstract(AnnotationAbstract),
            )?;
        }
        // TODO: pass error up
        snapshot.commit().unwrap();
        Ok(())
    }
}

macro_rules! get_type_methods {
    ($(
        fn $method_name:ident() -> $output_type:ident = $cache_method:ident;
    )*) => {
        $(
            pub fn $method_name(
                &self, snapshot: &Snapshot, label: &Label<'_>
            ) -> Result<Option<$output_type<'static>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(cache.$cache_method(label))
                } else {
                    TypeReader::get_labelled_type::<$output_type<'static>>(snapshot, label)
                }
            }
        )*
    }
}

macro_rules! get_supertype_methods {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<Option<$type_<'static>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(cache.$cache_method(type_))
                } else {
                    TypeReader::get_supertype(snapshot, type_)
                }
            }
        )*
    }
}

macro_rules! get_supertypes_methods {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident;
    )*) => {
        $(
            // WARN: supertypes currently do NOT include themselves
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, Vec<$type_<'static>>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let supertypes = TypeReader::get_supertypes(snapshot, type_)?;
                    Ok(MaybeOwns::Owned(supertypes))
                }
            }
        )*
    }
}

macro_rules! get_subtypes_methods {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, Vec<$type_<'static>>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let subtypes = TypeReader::get_subtypes(snapshot, type_)?;
                    Ok(MaybeOwns::Owned(subtypes))
                }
            }
        )*
    }
}

macro_rules! get_subtypes_transitive_methods {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident;
    )*) => {
        $(
            // WARN: supertypes currently do NOT include themselves
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, Vec<$type_<'static>>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let subtypes = TypeReader::get_subtypes_transitive(snapshot, type_)?;
                    Ok(MaybeOwns::Owned(subtypes))
                }
            }
        )*
    }
}

macro_rules! get_type_is_root_methods {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<bool, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(cache.$cache_method(type_))
                } else {
                    let type_label = TypeReader::get_label(snapshot, type_)?.unwrap();
                    Ok(TypeReader::check_type_is_root(&type_label, $type_::ROOT_KIND))
                }
            }
        )*
    }
}

macro_rules! get_type_label_methods {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, Label<'static>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    Ok(MaybeOwns::Owned(TypeReader::get_label(snapshot, type_)?.unwrap()))
                }
            }
        )*
    }
}

macro_rules! get_type_annotations {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident | $annotation_type:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, HashSet<$annotation_type>>, ConceptReadError> {
                 if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let annotations = TypeReader::get_type_annotations(snapshot, type_)?;
                    Ok(MaybeOwns::Owned(annotations))
                }
            }
        )*
    }
}

macro_rules! get_type_annotations_declared {
    ($(
        fn $method_name:ident() -> $type_:ident = $reader_method:ident | $cache_method:ident | $annotation_type:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, HashSet<$annotation_type>>, ConceptReadError> {
                 if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let annotations = TypeReader::$reader_method(snapshot, type_)?;
                    Ok(MaybeOwns::Owned(annotations))
                }
            }
        )*
    }
}

macro_rules! get_type_annotations {
    ($(
        fn $method_name:ident() -> $type_:ident = $reader_method:ident | $cache_method:ident | $annotation_type:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(
                &self, snapshot: &Snapshot, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, HashMap<$annotation_type, $type_<'static>>>, ConceptReadError> {
                 if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let annotations = TypeReader::$reader_method(snapshot, type_)?;
                    Ok(MaybeOwns::Owned(annotations))
                }
            }
        )*
    }
}

impl<Snapshot: ReadableSnapshot> TypeManager<Snapshot> {
    pub fn new(
        definition_key_generator: Arc<DefinitionKeyGenerator>,
        vertex_generator: Arc<TypeVertexGenerator>,
        schema_cache: Option<Arc<TypeCache>>,
    ) -> Self {
        TypeManager { definition_key_generator, vertex_generator, type_cache: schema_cache, snapshot: PhantomData }
    }

    pub fn resolve_relates(
        &self,
        snapshot: &Snapshot,
        relation: RelationType<'static>,
        role_name: &str,
    ) -> Result<Option<Relates<'static>>, ConceptReadError> {
        // TODO: Efficiency. We could build an index in TypeCache.
        Ok(self.get_relation_type_relates(snapshot, relation)?.iter().find_map(|(_role, relates)| {
            if self.get_role_type_label(snapshot, relates.role()).unwrap().name.as_str() == role_name {
                Some(relates.clone())
            } else {
                None
            }
        }))
    }

    pub fn get_struct_definition_key(
        &self,
        snapshot: &Snapshot,
        name: &str,
    ) -> Result<Option<DefinitionKey<'static>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(cache.get_struct_definition_key(name))
        } else {
            TypeReader::get_struct_definition_key(snapshot, name)
        }
    }

    pub fn get_struct_definition(
        &self,
        snapshot: &Snapshot,
        definition_key: DefinitionKey<'static>,
    ) -> Result<MaybeOwns<'_, StructDefinition>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_struct_definition(definition_key.clone())))
        } else {
            Ok(MaybeOwns::Owned(TypeReader::get_struct_definition(snapshot, definition_key.clone())?))
        }
    }

    pub fn resolve_struct_field(
        &self,
        snapshot: &Snapshot,
        fields_path: &Vec<&str>,
        definition: StructDefinition,
    ) -> Result<Vec<StructFieldIDUInt>, ConceptReadError> {
        let mut resolved: Vec<StructFieldIDUInt> = Vec::with_capacity(fields_path.len());
        let maybe_owns_definition = MaybeOwns::Borrowed(&definition);
        let mut at = maybe_owns_definition;
        for (i, f) in fields_path.iter().enumerate() {
            let field_idx_opt = at.field_names.get(*f);
            if let Some(field_idx) = field_idx_opt {
                resolved.push(*field_idx);
                let next_def: &StructDefinitionField = at.fields.get(&field_idx).unwrap();
                match &next_def.value_type {
                    ValueType::Struct(definition_key) => {
                        at = self.get_struct_definition(snapshot, definition_key.clone())?;
                    }
                    _ => {
                        if (i + 1) == fields_path.len() {
                            return Ok(resolved);
                        } else {
                            return Err(ConceptReadError::Encoding {
                                source: EncodingError::IndexingIntoNonStructField {
                                    struct_name: definition.name,
                                    field_path: fields_path.clone().into_iter().map(|str| str.to_owned()).collect(),
                                },
                            });
                        }
                    }
                }
            } else {
                return Err(ConceptReadError::Encoding {
                    source: EncodingError::StructFieldUnresolvable {
                        struct_name: definition.name,
                        field_path: fields_path.clone().into_iter().map(|str| str.to_owned()).collect(),
                    },
                });
            }
        }

        Err(ConceptReadError::Encoding {
            source: EncodingError::StructPathIncomplete {
                struct_name: definition.name,
                field_path: fields_path.clone().into_iter().map(|str| str.to_owned()).collect(),
            },
        })
    }

    get_type_methods! {
        fn get_object_type() -> ObjectType = get_object_type;
        fn get_entity_type() -> EntityType = get_entity_type;
        fn get_relation_type() -> RelationType = get_relation_type;
        fn get_role_type() -> RoleType = get_role_type;
        fn get_attribute_type() -> AttributeType = get_attribute_type;
    }

    get_supertype_methods! {
        fn get_entity_type_supertype() -> EntityType = get_supertype;
        fn get_relation_type_supertype() -> RelationType = get_supertype;
        fn get_role_type_supertype() -> RoleType = get_supertype;
        fn get_attribute_type_supertype() -> AttributeType = get_supertype;
    }

    get_supertypes_methods! {
        fn get_entity_type_supertypes() -> EntityType = get_supertypes;
        fn get_relation_type_supertypes() -> RelationType = get_supertypes;
        fn get_role_type_supertypes() -> RoleType = get_supertypes;
        fn get_attribute_type_supertypes() -> AttributeType = get_supertypes;
    }

    get_subtypes_methods! {
        fn get_entity_type_subtypes() -> EntityType = get_subtypes;
        fn get_relation_type_subtypes() -> RelationType = get_subtypes;
        fn get_role_type_subtypes() -> RoleType = get_subtypes;
        fn get_attribute_type_subtypes() -> AttributeType = get_subtypes;
    }

    get_subtypes_transitive_methods! {
        fn get_entity_type_subtypes_transitive() -> EntityType = get_subtypes_transitive;
        fn get_relation_type_subtypes_transitive() -> RelationType = get_subtypes_transitive;
        fn get_role_type_subtypes_transitive() -> RoleType = get_subtypes_transitive;
        fn get_attribute_type_subtypes_transitive() -> AttributeType = get_subtypes_transitive;
    }

    get_type_is_root_methods! {
        fn get_entity_type_is_root() -> EntityType = is_root;
        fn get_relation_type_is_root() -> RelationType = is_root;
        fn get_role_type_is_root() -> RoleType = is_root;
        fn get_attribute_type_is_root() -> AttributeType = is_root;
    }

    get_type_label_methods! {
        fn get_entity_type_label() -> EntityType = get_label;
        fn get_relation_type_label() -> RelationType = get_label;
        fn get_role_type_label() -> RoleType = get_label;
        fn get_attribute_type_label() -> AttributeType = get_label;
    }

    pub(crate) fn get_entity_type_owns_declared(
        &self,
        snapshot: &Snapshot,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_declared(entity_type)))
        } else {
            let owns = TypeReader::get_implemented_interfaces_declared(snapshot, entity_type.clone())?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_relation_type_owns_declared(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_declared(relation_type)))
        } else {
            let owns = TypeReader::get_implemented_interfaces_declared(snapshot, relation_type.clone())?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_owns_for_attribute_declared(
        &self,
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_for_attribute_type_declared(attribute_type.clone())))
        } else {
            let plays =
                TypeReader::get_implementations_for_interface_declared::<Owns<'static>>(snapshot, attribute_type.clone())?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_owns_for_attribute(
        &self,
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<ObjectType<'static>, Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_for_attribute_type(attribute_type.clone())))
        } else {
            let owns = TypeReader::get_implementations_for_interface::<Owns<'static>>(
                snapshot,
                attribute_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_relation_type_relates_declared(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Relates<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_relation_type_relates_declared(relation_type)))
        } else {
            let relates = TypeReader::get_relates_declared(snapshot, relation_type.clone())?;
            Ok(MaybeOwns::Owned(relates))
        }
    }

    pub(crate) fn get_relation_type_relates(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<RoleType<'static>, Relates<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_relation_type_relates(relation_type)))
        } else {
            let relates = TypeReader::get_relates(snapshot, relation_type.clone())?;
            Ok(MaybeOwns::Owned(relates))
        }
    }

    pub(crate) fn get_plays_for_role_type_declared(
        &self,
        snapshot: &Snapshot,
        role_type: RoleType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays_for_role_type_declared(role_type.clone())))
        } else {
            let plays = TypeReader::get_implementations_for_interface_declared::<Plays<'static>>(snapshot, role_type.clone())?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_plays_for_role_type(
        &self,
        snapshot: &Snapshot,
        role_type: RoleType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<ObjectType<'static>, Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays_for_role_type(role_type.clone())))
        } else {
            let plays = TypeReader::get_implementations_for_interface::<Plays<'static>>(
                snapshot,
                role_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_entity_type_owns(
        &self,
        snapshot: &Snapshot,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns(entity_type)))
        } else {
            let owns = TypeReader::get_implemented_interfaces::<Owns<'static>, EntityType<'static>>(
                snapshot,
                entity_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_relation_type_owns(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns(relation_type)))
        } else {
            let owns = TypeReader::get_implemented_interfaces::<Owns<'static>, RelationType<'static>>(
                snapshot,
                relation_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_entity_type_overridden_owns(
        &self,
        snapshot: &Snapshot,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_overridden_owns(entity_type)))
        } else {
            let owns = TypeReader::get_overridden_interfaces::<Owns<'static>, EntityType<'static>>(
                snapshot,
                entity_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_relation_type_overridden_owns(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<AttributeType<'static>, Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_overridden_owns(relation_type)))
        } else {
            let owns = TypeReader::get_overridden_interfaces::<Owns<'static>, RelationType<'static>>(
                snapshot,
                relation_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn relation_index_available(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'_>,
    ) -> Result<bool, ConceptReadError> {
        // TODO: it would be good if this doesn't require recomputation
        let mut max_card = 0;
        let relates = relation_type.get_relates_declared(snapshot, self)?;
        for relates in relates.iter() {
            let card = relates.get_cardinality(snapshot, self)?;
            match card.end() {
                None => return Ok(false),
                Some(end) => max_card += end,
            }
        }
        Ok(max_card <= RELATION_INDEX_THRESHOLD)
    }

    pub(crate) fn get_entity_type_plays_declared<'this>(
        &'this self,
        snapshot: &Snapshot,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'this, HashSet<Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays_declared(entity_type)))
        } else {
            let plays = TypeReader::get_implemented_interfaces_declared(snapshot, entity_type.clone())?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_entity_type_plays(
        &self,
        snapshot: &Snapshot,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays(entity_type)))
        } else {
            let plays = TypeReader::get_implemented_interfaces::<Plays<'static>, EntityType<'static>>(
                snapshot,
                entity_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_entity_type_overridden_plays(
        &self,
        snapshot: &Snapshot,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_overridden_plays(entity_type)))
        } else {
            let plays = TypeReader::get_overridden_interfaces::<Plays<'static>, EntityType<'static>>(
                snapshot,
                entity_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_relation_type_plays_declared<'this>(
        &'this self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'this, HashSet<Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays_declared(relation_type)))
        } else {
            let plays = TypeReader::get_implemented_interfaces_declared(snapshot, relation_type.clone())?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_relation_type_plays(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays(relation_type)))
        } else {
            let plays = TypeReader::get_implemented_interfaces::<Plays<'static>, RelationType<'static>>(
                snapshot,
                relation_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_relation_type_overridden_plays(
        &self,
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashMap<RoleType<'static>, Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_overridden_plays(relation_type)))
        } else {
            let plays = TypeReader::get_overridden_interfaces::<Plays<'static>, RelationType<'static>>(
                snapshot,
                relation_type.clone(),
            )?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_plays_overridde(
        &self,
        snapshot: &Snapshot,
        plays: Plays<'static>,
    ) -> Result<MaybeOwns<'_, Option<Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays_override(plays)))
        } else {
            Ok(MaybeOwns::Owned(TypeReader::get_implementation_override(snapshot, plays)?))
        }
    }

    pub(crate) fn get_attribute_type_value_type(
        &self,
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<(ValueType, AttributeType<'static>)>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(cache.get_attribute_type_value_type(attribute_type).clone())
        } else {
            Ok(TypeReader::get_value_type(snapshot, attribute_type)?)
        }
    }

    get_type_annotations_declared! {
        fn get_entity_type_annotations_declared() -> EntityType = get_type_annotations_declared | get_annotations_declared | EntityTypeAnnotation;
        fn get_relation_type_annotations_declared() -> RelationType = get_type_annotations_declared | get_annotations_declared | RelationTypeAnnotation;
        fn get_role_type_annotations_declared() -> RoleType = get_type_annotations_declared | get_annotations_declared | RoleTypeAnnotation;
        fn get_attribute_type_annotations_declared() -> AttributeType = get_type_annotations_declared | get_annotations_declared | AttributeTypeAnnotation;
    }

    get_type_annotations! {
        fn get_entity_type_annotations() -> EntityType = get_type_annotations | get_annotations | EntityTypeAnnotation;
        fn get_relation_type_annotations() -> RelationType = get_type_annotations | get_annotations | RelationTypeAnnotation;
        fn get_role_type_annotations() -> RoleType = get_type_annotations | get_annotations | RoleTypeAnnotation;
        fn get_attribute_type_annotations() -> AttributeType = get_type_annotations | get_annotations | AttributeTypeAnnotation;
    }

    pub(crate) fn get_owns_overridden(
        &self,
        snapshot: &Snapshot,
        owns: Owns<'static>,
    ) -> Result<MaybeOwns<'_, Option<Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_override(owns)))
        } else {
            Ok(MaybeOwns::Owned(TypeReader::get_implementation_override(snapshot, owns)?))
        }
    }

    pub(crate) fn get_owns_ordering(
        &self,
        snapshot: &Snapshot,
        owns: Owns<'static>,
    ) -> Result<Ordering, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(cache.get_owns_ordering(owns))
        } else {
            Ok(TypeReader::get_type_edge_property::<Ordering>(snapshot, owns)?.unwrap())
        }
    }

    pub(crate) fn get_role_ordering(
        &self,
        snapshot: &Snapshot,
        role_type: RoleType<'static>,
    ) -> Result<Ordering, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(cache.get_role_type_ordering(role_type))
        } else {
            Ok(TypeReader::get_type_ordering(snapshot, role_type)?)
        }
    }

    pub(crate) fn get_role_type_relates(
        &self,
        snapshot: &Snapshot,
        role_type: RoleType<'static>,
    ) -> Result<MaybeOwns<'_, Relates<'static>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_role_type_relates(role_type)))
        } else {
            let relates = TypeReader::get_role_type_relates(snapshot, role_type.clone())?;
            Ok(MaybeOwns::Owned(relates))
        }
    }

    pub(crate) fn get_relates_overridden(
        &self,
        snapshot: &Snapshot,
        relates: Relates<'static>,
    ) -> Result<MaybeOwns<'_, Option<Relates<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_relates_override(relates)))
        } else {
            Ok(MaybeOwns::Owned(TypeReader::get_implementation_override(snapshot, relates)?))
        }
    }

    pub(crate) const fn role_default_cardinality(&self, ordering: Ordering) -> AnnotationCardinality {
        // TODO: read from database properties the default role cardinality the db was created with
        match ordering {
            Ordering::Unordered => AnnotationCardinality::new(1, Some(1)),
            Ordering::Ordered => AnnotationCardinality::new(0, None),
        }
    }

    pub(crate) fn get_owns_annotations_declared<'this>(
        &'this self,
        snapshot: &Snapshot,
        owns: Owns<'static>,
    ) -> Result<MaybeOwns<'this, HashSet<OwnsAnnotation>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_annotations_declared(owns)))
        } else {
            let annotations: HashSet<OwnsAnnotation> =
                TypeReader::get_type_edge_annotations_declared(snapshot, owns)?
                    .into_iter()
                    .map(|annotation| OwnsAnnotation::from(annotation))
                    .collect();
            Ok(MaybeOwns::Owned(annotations))
        }
    }

    pub(crate) fn get_owns_annotations<'this>(
        &'this self,
        snapshot: &Snapshot,
        owns: Owns<'static>,
    ) -> Result<MaybeOwns<'this, HashMap<OwnsAnnotation, Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_annotations(owns)))
        } else {
            let annotations: HashMap<OwnsAnnotation, Owns<'static>> =
                TypeReader::get_type_edge_annotations(snapshot, owns)?
                    .into_iter()
                    .map(|(annotation, owns)| (OwnsAnnotation::from(annotation), owns))
                    .collect();
            Ok(MaybeOwns::Owned(annotations))
        }
    }

    pub(crate) fn get_plays_annotations_declared<'this>(
        &'this self,
        snapshot: &Snapshot,
        plays: Plays<'static>,
    ) -> Result<MaybeOwns<'this, HashSet<PlaysAnnotation>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays_annotations_declared(plays)))
        } else {
            let annotations: HashSet<PlaysAnnotation> =
                TypeReader::get_type_edge_annotations_declared(snapshot, plays)?
                    .into_iter()
                    .map(|annotation| PlaysAnnotation::from(annotation))
                    .collect();
            Ok(MaybeOwns::Owned(annotations))
        }
    }

    pub(crate) fn get_plays_annotations<'this>(
        &'this self,
        snapshot: &Snapshot,
        plays: Plays<'static>,
    ) -> Result<MaybeOwns<'this, HashMap<PlaysAnnotation, Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_plays_annotations(plays)))
        } else {
            let annotations: HashMap<PlaysAnnotation, Plays<'static>> =
                TypeReader::get_type_edge_annotations(snapshot, plays)?
                    .into_iter()
                    .map(|(annotation, plays)| (PlaysAnnotation::from(annotation), plays))
                    .collect();
            Ok(MaybeOwns::Owned(annotations))
        }
    }

    pub(crate) fn get_relates_annotations_declared<'this>(
        &'this self,
        snapshot: &Snapshot,
        relates: Relates<'static>,
    ) -> Result<MaybeOwns<'this, HashSet<RelatesAnnotation>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_relates_annotations_declared(relates)))
        } else {
            // TODO: Move these calls to a common place so it could be called from both cache init and here?
            let annotations: HashSet<RelatesAnnotation> =
                TypeReader::get_type_edge_annotations_declared(snapshot, relates)?
                    .into_iter()
                    .map(|annotation| RelatesAnnotation::from(annotation))
                    .collect();
            Ok(MaybeOwns::Owned(annotations))
        }
    }

    pub(crate) fn get_relates_annotations<'this>(
        &'this self,
        snapshot: &Snapshot,
        relates: Relates<'static>,
    ) -> Result<MaybeOwns<'this, HashMap<RelatesAnnotation, Relates<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_relates_annotations(relates)))
        } else {
            let annotations: HashMap<RelatesAnnotation, Relates<'static>> =
                TypeReader::get_type_edge_annotations(snapshot, relates)?
                    .into_iter()
                    .map(|(annotation, relates)| (RelatesAnnotation::from(annotation), relates))
                    .collect();
            Ok(MaybeOwns::Owned(annotations))
        }
    }
}

// TODO: Remove this set of comments
// DO: Do all validation, and call TypeWriter methods.
//  All validation must occur before any writes.  All writes must be done through TypeWriter
//      (If this feels like unnecessary indirection, feel free to refactor. I just need structure)
//  Avoid cross-calling methods if it violates the above.
impl<Snapshot: WritableSnapshot> TypeManager<Snapshot> {
    pub fn create_struct(
        &self,
        snapshot: &mut Snapshot,
        name: String,
    ) -> Result<DefinitionKey<'static>, ConceptWriteError> {
        // TODO: Validation
        OperationTimeValidation::validate_struct_name_uniqueness(snapshot, &name)
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        let definition_key = self
            .definition_key_generator
            .create_struct(snapshot)
            .map_err(|source| ConceptWriteError::Encoding { source })?;
        TypeWriter::storage_put_struct(snapshot, definition_key.clone(), StructDefinition::new(name));
        Ok(definition_key)
    }

    pub fn create_struct_field(
        &self,
        snapshot: &mut Snapshot,
        definition_key: DefinitionKey<'static>,
        field_name: String,
        value_type: ValueType,
        is_optional: bool,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        let mut struct_definition = TypeReader::get_struct_definition(snapshot, definition_key.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?;
        struct_definition
            .add_field(field_name, value_type, is_optional)
            .map_err(|source| ConceptWriteError::Encoding { source })?;
        TypeWriter::storage_put_struct(snapshot, definition_key.clone(), struct_definition);
        Ok(())
    }

    pub fn delete_struct_field(
        &self,
        snapshot: &mut Snapshot,
        definition_key: DefinitionKey<'static>,
        field_name: String,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        let mut struct_definition = TypeReader::get_struct_definition(snapshot, definition_key.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?;
        struct_definition.delete_field(field_name).map_err(|source| ConceptWriteError::Encoding { source })?;
        TypeWriter::storage_put_struct(snapshot, definition_key.clone(), struct_definition);
        Ok(())
    }

    pub fn delete_struct(
        &self,
        snapshot: &mut Snapshot,
        definition_key: &DefinitionKey<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Check inside attributes and structs!
        // OperationTimeValidation::validate_not_used(snapshot, entity_type.clone().into_owned())
        //     .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_struct(snapshot, definition_key);
        Ok(())
    }

    pub fn finalise(self, snapshot: &Snapshot) -> Result<(), Vec<ConceptWriteError>> {
        let type_errors = CommitTimeValidation::validate(snapshot);
        match type_errors {
            Ok(errors) => {
                if errors.is_empty() {
                    Ok(())
                } else {
                    Err(errors.into_iter().map(|error| ConceptWriteError::SchemaValidation { source: error }).collect())
                }
            }
            Err(error) => Err(vec![ConceptWriteError::ConceptRead { source: error }]),
        }
    }

    pub fn create_entity_type(
        &self,
        snapshot: &mut Snapshot,
        label: &Label<'_>,
        is_root: bool,
    ) -> Result<EntityType<'static>, ConceptWriteError> {
        OperationTimeValidation::validate_label_uniqueness(snapshot, &label.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        let type_vertex = self
            .vertex_generator
            .create_entity_type(snapshot)
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let entity = EntityType::new(type_vertex);

        TypeWriter::storage_put_label(snapshot, entity.clone(), label);
        if !is_root {
            TypeWriter::storage_put_supertype(
                snapshot,
                entity.clone(),
                self.get_entity_type(snapshot, &Kind::Entity.root_label()).unwrap().unwrap(),
            );
        }
        Ok(entity)
    }

    pub fn create_relation_type(
        &self,
        snapshot: &mut Snapshot,
        label: &Label<'_>,
        is_root: bool,
    ) -> Result<RelationType<'static>, ConceptWriteError> {
        OperationTimeValidation::validate_label_uniqueness(snapshot, &label.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        let type_vertex = self
            .vertex_generator
            .create_relation_type(snapshot)
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let relation = RelationType::new(type_vertex);

        TypeWriter::storage_put_label(snapshot, relation.clone(), label);
        if !is_root {
            TypeWriter::storage_put_supertype(
                snapshot,
                relation.clone(),
                self.get_relation_type(snapshot, &Kind::Relation.root_label()).unwrap().unwrap(),
            );
        }
        Ok(relation)
    }

    pub(crate) fn create_role_type(
        &self,
        snapshot: &mut Snapshot,
        label: &Label<'_>,
        relation_type: RelationType<'static>,
        is_root: bool,
        ordering: Ordering,
    ) -> Result<RoleType<'static>, ConceptWriteError> {
        OperationTimeValidation::validate_role_name_uniqueness(snapshot, relation_type.clone().into_owned(), &label.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        let type_vertex = self
            .vertex_generator
            .create_role_type(snapshot)
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let role = RoleType::new(type_vertex);
        TypeWriter::storage_put_label(snapshot, role.clone(), label);
        TypeWriter::storage_put_relates(snapshot, relation_type, role.clone());
        self.set_role_ordering_unconditional(snapshot, role.clone(), ordering)?;
        if !is_root {
            self.set_role_type_root_supertype(snapshot, role.clone());
        }
        Ok(role)
    }

    fn set_role_type_root_supertype(
        &self,
        snapshot: &mut Snapshot,
        role: RoleType<'static>,
    ) {
        TypeWriter::storage_put_supertype(
            snapshot,
            role,
            self.get_role_type(snapshot, &Kind::Role.root_label()).unwrap().unwrap(),
        );
    }

    pub fn create_attribute_type(
        &self,
        snapshot: &mut Snapshot,
        label: &Label<'_>,
        is_root: bool,
    ) -> Result<AttributeType<'static>, ConceptWriteError> {
        OperationTimeValidation::validate_label_uniqueness(snapshot, &label.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        let type_vertex = self
            .vertex_generator
            .create_attribute_type(snapshot)
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let attribute_type = AttributeType::new(type_vertex);
        TypeWriter::storage_put_label(snapshot, attribute_type.clone(), label);
        if !is_root {
            TypeWriter::storage_put_supertype(
                snapshot,
                attribute_type.clone(),
                self.get_attribute_type(snapshot, &Kind::Attribute.root_label()).unwrap().unwrap(),
            );
        }
        Ok(attribute_type)
    }

    pub(crate) fn delete_entity_type(
        &self,
        snapshot: &mut Snapshot,
        entity_type: EntityType<'_>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_type_is_not_root(snapshot, entity_type.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_no_subtypes(snapshot, entity_type.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        // TODO: Re-enable when we get the thing_manager
        // OperationTimeValidation::validate_exact_type_no_instances_entity(snapshot, entity_type.clone().into_owned())
        //     .map_err(|source| ConceptWriteError::SchemaValidation {source})?;

        TypeWriter::storage_delete_label(snapshot, entity_type.clone().into_owned());
        TypeWriter::storage_delete_supertype(snapshot, entity_type.clone().into_owned());
        Ok(())
    }

    pub(crate) fn delete_relation_type(
        &self,
        snapshot: &mut Snapshot,
        relation_type: RelationType<'_>,
    ) -> Result<(), ConceptWriteError> {
        // Sufficient to guarantee the roles have no subtypes or instances either
        OperationTimeValidation::validate_type_is_not_root(snapshot, relation_type.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_no_subtypes(snapshot, relation_type.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        // TODO: Re-enable when we get the thing_manager
        // OperationTimeValidation::validate_exact_type_no_instances_relation(snapshot, relation_type.clone().into_owned())
        //     .map_err(|source| ConceptWriteError::SchemaValidation {source})?;

        let declared_relates =
            TypeReader::get_relates(snapshot, relation_type.clone().into_owned()).unwrap();
        for (_role_type, relates) in declared_relates.iter() {
            self.delete_role_type(snapshot, relates.role().clone())?; // TODO: Should we replace it with individual calls?
        }
        TypeWriter::storage_delete_label(snapshot, relation_type.clone().into_owned());
        TypeWriter::storage_delete_supertype(snapshot, relation_type.clone().into_owned());
        Ok(())
    }

    pub(crate) fn delete_attribute_type(
        &self,
        snapshot: &mut Snapshot,
        attribute_type: AttributeType<'_>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_type_is_not_root(snapshot, attribute_type.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_no_subtypes(snapshot, attribute_type.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        // TODO: Re-enable when we get the thing_manager
        // OperationTimeValidation::validate_exact_type_no_instances_attribute(snapshot, self, attribute.clone())
        //     .map_err(|source| ConceptWriteError::SchemaValidation {  source } )?;

        TypeWriter::storage_delete_label(snapshot, attribute_type.clone().into_owned());
        TypeWriter::storage_delete_supertype(snapshot, attribute_type.clone().into_owned());
        Ok(())
    }

    pub(crate) fn delete_role_type(
        &self,
        snapshot: &mut Snapshot,
        role_type: RoleType<'_>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_type_is_not_root(snapshot, role_type.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        // TODO: More validation
        // TODO: Re-enable when we get the thing_manager
        // OperationTimeValidation::validate_exact_type_no_instances_role(snapshot, role_type.clone().into_owned())
        //     .map_err(|source| ConceptWriteError::SchemaValidation {source})?;

        let relates = TypeReader::get_role_type_relates(snapshot, role_type.clone().into_owned()).unwrap(); // Unwrap -> error?
        let relation = relates.relation();
        let role = relates.role();
        TypeWriter::storage_delete_relates(snapshot, relation.clone(), role.clone());
        TypeWriter::storage_delete_label(snapshot, role.clone().into_owned());
        TypeWriter::storage_delete_supertype(snapshot, role.clone().into_owned());
        Ok(())
    }

    pub(crate) fn set_label<T: KindAPI<'static>>(
        &self,
        snapshot: &mut Snapshot,
        type_: T,
        label: &Label<'_>,
    ) -> Result<(), ConceptWriteError> {
        debug_assert!(OperationTimeValidation::validate_type_exists(snapshot, type_.clone()).is_ok());
        match T::ROOT_KIND {
            Kind::Entity | Kind::Attribute => {
                OperationTimeValidation::validate_label_uniqueness(snapshot, &label.clone().into_owned())
                    .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
            }
            Kind::Relation => unreachable!("Use set_relation_type_label instead"),
            Kind::Role => unreachable!("Use set_name instead")
        }

        TypeWriter::storage_delete_label(snapshot, type_.clone());
        TypeWriter::storage_put_label(snapshot, type_, &label);
        Ok(())
    }

    pub(crate) fn set_relation_type_label(
        &self,
        snapshot: &mut Snapshot,
        type_: RelationType<'static>,
        label: &Label<'_>,
    ) -> Result<(), ConceptWriteError> {
        debug_assert!(OperationTimeValidation::validate_type_exists(snapshot, type_.clone()).is_ok());

        OperationTimeValidation::validate_label_uniqueness(snapshot, &label.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })
            .unwrap(); // TODO: Propagate error instead

        TypeWriter::storage_delete_label(snapshot, type_.clone());
        TypeWriter::storage_put_label(snapshot, type_.clone(), &label);

        let relates = self.get_relation_type_relates_declared(snapshot, type_)?;
        for relate in &relates {
            self.set_role_type_scope(snapshot, relate.role(), label.clone().name().as_str())?;
        }

        Ok(())
    }

    pub(crate) fn set_role_type_name(
        &self,
        snapshot: &mut Snapshot,
        role_type: RoleType<'static>,
        name: &str,
    ) -> Result<(), ConceptWriteError> {
        debug_assert!(OperationTimeValidation::validate_type_exists(snapshot, role_type.clone()).is_ok());

        let old_label = TypeReader::get_label(snapshot, role_type.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?
            .unwrap();
        debug_assert!(old_label.scope().is_some());
        let new_label = Label::build_scoped(name, old_label.scope().unwrap().as_str());

        let relation_type = TypeReader::get_role_type_relates(snapshot, role_type.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?
            .relation();
        OperationTimeValidation::validate_role_name_uniqueness(snapshot, relation_type, &new_label.clone().into_owned())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_label(snapshot, role_type.clone());
        TypeWriter::storage_put_label(snapshot, role_type, &new_label);
        Ok(())
    }

    fn set_role_type_scope(
        &self,
        snapshot: &mut Snapshot,
        role_type: RoleType<'static>,
        scope: &str,
    ) -> Result<(), ConceptWriteError> {
        debug_assert!(OperationTimeValidation::validate_type_exists(snapshot, role_type.clone()).is_ok());

        let old_label = TypeReader::get_label(snapshot, role_type.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?
            .unwrap();
        debug_assert!(old_label.scope().is_some());
        let new_label = Label::build_scoped(old_label.name().as_str(), scope);

        TypeWriter::storage_delete_label(snapshot, role_type.clone());
        TypeWriter::storage_put_label(snapshot, role_type, &new_label);
        Ok(())
    }

    pub(crate) fn set_value_type(
        &self,
        snapshot: &mut Snapshot,
        attribute: AttributeType<'static>,
        value_type: ValueType,
    ) -> Result<(), ConceptWriteError> {
        debug_assert!(OperationTimeValidation::validate_type_exists(snapshot, attribute.clone()).is_ok());

        let existing_value_type_with_source = TypeReader::get_value_type(snapshot, attribute.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?;

        OperationTimeValidation::validate_value_type_compatible_with_existing_value_type(
            snapshot, attribute.clone(), value_type.clone(), existing_value_type_with_source.clone()
        ).map_err(|source| ConceptWriteError::SchemaValidation {  source } )?;

        // TODO: Maybe it should be schema validation!
        OperationTimeValidation::validate_value_type_compatible_with_subtypes_value_types(
            snapshot, attribute.clone(), value_type.clone()
        ).map_err(|source| ConceptWriteError::SchemaValidation {  source } )?;

        OperationTimeValidation::validate_value_type_keyable_for_all_owns_annotations(
            snapshot, attribute.clone(), Some(value_type.clone())
        ).map_err(|source| ConceptWriteError::SchemaValidation {  source } )?;

        // TODO: Can't change value type now!
        // if let Some((existing_value_type, _)) = existing_value_type_with_source
        // {
        //     if value_type != existing_value_type {
        // TODO: Re-enable when we get the thing_manager
        // OperationTimeValidation::validate_exact_type_no_instances_attribute(snapshot, self, attribute.clone())
        //     .map_err(|source| ConceptWriteError::SchemaValidation {  source } )?;
        //     }
        // }

        TypeWriter::storage_set_value_type(snapshot, attribute, value_type);
        Ok(())
    }

    pub(crate) fn unset_value_type(
        &self,
        snapshot: &mut Snapshot,
        attribute: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        let declared_value_type = TypeReader::get_value_type_declared(snapshot, attribute.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?;

        // TODO: Maybe we want to return Error if we want to unset an inherited value type just like with annotations?
        // Just ignoring this case for now for simplicity...
        match declared_value_type {
            Some(_) => {
                OperationTimeValidation::validate_value_type_can_be_unset(snapshot, attribute.clone(), declared_value_type)
                    .map_err(|source| ConceptWriteError::SchemaValidation {  source } )?;

                TypeWriter::storage_unset_value_type(snapshot, attribute);
                Ok(())
            },
            None => Ok(()),
        }
    }

    fn set_supertype<K>(&self, snapshot: &mut Snapshot, subtype: K, supertype: K) -> Result<(), ConceptWriteError>
        where
            K: KindAPI<'static>,
    {
        debug_assert! {
            OperationTimeValidation::validate_type_exists(snapshot, subtype.clone()).is_ok() &&
                OperationTimeValidation::validate_type_exists(snapshot, supertype.clone()).is_ok()
        };

        OperationTimeValidation::validate_sub_does_not_create_cycle(snapshot, subtype.clone(), supertype.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        OperationTimeValidation::validate_type_supertype_abstractness(snapshot, subtype.clone(), supertype.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_supertype(snapshot, subtype.clone());
        TypeWriter::storage_put_supertype(snapshot, subtype.clone(), supertype.clone());
        Ok(())
    }

    pub(crate) fn set_attribute_type_supertype(
        &self,
        snapshot: &mut Snapshot,
        subtype: AttributeType<'static>,
        supertype: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_value_type_is_compatible_with_new_supertypes_value_type(
            snapshot,
            subtype.clone(),
            supertype.clone(),
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        OperationTimeValidation::validate_type_is_abstract(snapshot, supertype.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        Self::set_supertype(self, snapshot, subtype, supertype)
    }

    pub(crate) fn set_entity_type_supertype(
        &self,
        snapshot: &mut Snapshot,
        subtype: EntityType<'static>,
        supertype: EntityType<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: EntityType specific validation (probably nothing)
        Self::set_supertype(self, snapshot, subtype, supertype)
    }

    pub(crate) fn set_relation_type_supertype(
        &self,
        snapshot: &mut Snapshot,
        subtype: RelationType<'static>,
        supertype: RelationType<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: RelationType specific validation
        Self::set_supertype(self, snapshot, subtype, supertype)
    }

    // TODO: If the validation for owns and plays can be made generic, we should see if we can make these functions generic as well.
    pub(crate) fn set_owns(
        &self,
        snapshot: &mut Snapshot,
        owner: impl ObjectTypeAPI<'static> + KindAPI<'static>,
        attribute: AttributeType<'static>,
        ordering: Ordering,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        OperationTimeValidation::validate_ownership_abstractness(snapshot, owner.clone(), attribute.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_attribute_type_owns_not_overridden(snapshot, owner.clone(), attribute.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        let owns = Owns::new(ObjectType::new(owner.clone().into_vertex()), attribute.clone());
        TypeWriter::storage_put_interface_impl(snapshot, owns.clone());
        TypeWriter::storage_put_type_edge_property(snapshot, owns, Some(ordering));
        Ok(())
    }

    pub(crate) fn unset_owns(
        &self,
        snapshot: &mut Snapshot,
        owner: ObjectType<'static>,
        attribute: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unsetted_owns_is_not_inherited(snapshot, owner.clone(), attribute.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        let owns = Owns::new(ObjectType::new(owner.clone().into_vertex()), attribute.clone());
        TypeWriter::storage_delete_type_edge_property::<Ordering>(snapshot, owns.clone());
        TypeWriter::storage_delete_interface_impl(snapshot, owns.clone());
        Ok(())
    }

    pub(crate) fn set_owns_overridden(
        &self,
        snapshot: &mut Snapshot,
        owns: Owns<'static>,
        overridden: Owns<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: More validation - instances exist.
        OperationTimeValidation::validate_owns_is_inherited(snapshot, owns.owner(), overridden.attribute())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_overridden_is_supertype(snapshot, owns.attribute(), overridden.attribute())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_owns_override_ordering_match(snapshot, owns.clone(), overridden.clone(), None)
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_set_type_edge_overridden(snapshot, owns, overridden); // .attribute().clone());
        Ok(())
    }

    pub(crate) fn unset_owns_overridden(
        &self,
        snapshot: &mut Snapshot,
        owns: Owns<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: validation
        TypeWriter::storage_delete_type_edge_overridden(snapshot, owns.clone()); // .attribute().clone());
        Ok(())
    }

    pub(crate) fn set_plays(
        &self,
        snapshot: &mut Snapshot,
        player: impl KindAPI<'static> + ObjectTypeAPI<'static> + PlayerAPI<'static>,
        role: RoleType<'static>,
    ) -> Result<Plays<'static>, ConceptWriteError> {
        // TODO: Validation
        OperationTimeValidation::validate_role_plays_not_overridden(snapshot, player.clone(), role.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        let plays = Plays::new(ObjectType::new(player.into_vertex()), role);
        TypeWriter::storage_put_interface_impl(snapshot, plays.clone());
        Ok(plays)
    }

    pub(crate) fn unset_plays(
        &self,
        snapshot: &mut Snapshot,
        player: ObjectType<'static>,
        role: RoleType<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unsetted_plays_is_not_inherited(snapshot, player.clone(), role.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        let plays = Plays::new(ObjectType::new(player.into_vertex()), role);
        TypeWriter::storage_delete_interface_impl(snapshot, plays);
        Ok(())
    }

    pub(crate) fn set_plays_overridden(
        &self,
        snapshot: &mut Snapshot,
        plays: Plays<'static>,
        overridden: Plays<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_plays_is_inherited(snapshot, plays.player(), overridden.role())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_overridden_is_supertype(snapshot, plays.role(), overridden.role())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_set_type_edge_overridden(snapshot, plays, overridden); //.role());
        Ok(())
    }

    pub(crate) fn unset_plays_overridden(
        &self,
        snapshot: &mut Snapshot,
        plays: Plays<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        TypeWriter::storage_delete_type_edge_overridden(snapshot, plays);
        Ok(())
    }

    pub(crate) fn set_owns_ordering(
        &self, snapshot: &mut Snapshot, owns: Owns<'static>, ordering: Ordering,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        OperationTimeValidation::validate_owns_distinct_annotation_ordering(snapshot, owns.clone(), Some(ordering), None)
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        // TODO: subtype ordering match should be on commit time, not operation time!
        let owns_override_opt = TypeReader::get_implementation_override(snapshot, owns.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?;
        match owns_override_opt {
            Some(owns_override) => {
                OperationTimeValidation::validate_owns_override_ordering_match(
                    snapshot, owns.clone(), owns_override.clone(), Some(ordering)
                ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
            }
            None => {}
        }

        TypeWriter::storage_set_owns_ordering(snapshot, owns, ordering);
        Ok(())
    }

    pub(crate) fn set_role_ordering(
        &self, snapshot: &mut Snapshot, role: RoleType<'_>, ordering: Ordering,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        let relates = self.get_role_type_relates(snapshot, role.clone().into_owned())?;
        OperationTimeValidation::validate_relates_distinct_annotation_ordering(snapshot, relates.clone(), Some(ordering), None)
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        // TODO: subtype ordering match should be on commit time, not operation time!
        let relates_override_opt = TypeReader::get_implementation_override(snapshot, relates.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })?;
        match relates_override_opt {
            Some(relates_override) => {
                OperationTimeValidation::validate_role_supertype_ordering_match(
                    snapshot, relates.role().clone(), relates_override.role().clone(), Some(ordering)
                ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
            }
            None => {}
        }

        self.set_role_ordering_unconditional(snapshot, role, ordering)
    }

    fn set_role_ordering_unconditional(
        &self, snapshot: &mut Snapshot, role: RoleType<'_>, ordering: Ordering,
    ) -> Result<(), ConceptWriteError> {
        TypeWriter::storage_put_type_vertex_property(snapshot, role, Some(ordering));
        Ok(())
    }

    pub(crate) fn set_annotation_abstract(
        &self, snapshot: &mut Snapshot, type_: impl KindAPI<'static>,
    ) -> Result<(), ConceptWriteError> {

        OperationTimeValidation::validate_set_annotation_is_compatible_with_declared_annotations(
            snapshot, type_.clone(), AnnotationCategory::Abstract
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_annotation_is_compatible_with_inherited_annotations(
            snapshot, type_.clone(), AnnotationCategory::Abstract
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        // TODO: Validation: existing instances (or data validation?)

        TypeWriter::storage_put_type_vertex_property::<AnnotationAbstract>(snapshot, type_, None);
        Ok(())
    }

    pub(crate) fn unset_annotation_abstract(
        &self, snapshot: &mut Snapshot, type_: impl KindAPI<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_annotation_is_not_inherited(
            snapshot, type_.clone(), AnnotationCategory::Abstract,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_type_vertex_property::<AnnotationAbstract>(snapshot, type_);
        Ok(())
    }

    pub(crate) fn unset_owner_annotation_abstract(
        &self, snapshot: &mut Snapshot, type_: impl ObjectTypeAPI<'static> + KindAPI<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_no_abstract_attribute_types_owned(snapshot, type_.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        Self::unset_annotation_abstract(self, snapshot, type_)
    }

    pub(crate) fn unset_attribute_type_annotation_abstract(
        &self,
        snapshot: &mut Snapshot,
        type_: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_no_subtypes(snapshot, type_.clone())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_value_type_compatible_with_abstractness(
            snapshot,
            type_.clone(),
            TypeReader::get_value_type_without_source(snapshot, type_.clone())?,
            Some(false),
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        Self::unset_annotation_abstract(self, snapshot, type_)
    }

    pub(crate) fn set_annotation_independent(&self, snapshot: &mut Snapshot, type_: impl KindAPI<'static>) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_set_annotation_is_compatible_with_declared_annotations(
            snapshot, type_.clone(), AnnotationCategory::Independent
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_annotation_is_compatible_with_inherited_annotations(
            snapshot, type_.clone(), AnnotationCategory::Independent
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_put_type_vertex_property::<AnnotationIndependent>(snapshot, type_, None);
        Ok(())
    }

    pub(crate) fn unset_annotation_independent(
        &self, snapshot: &mut Snapshot, type_: impl KindAPI<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_annotation_is_not_inherited(
            snapshot, type_.clone(), AnnotationCategory::Independent,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        // TODO: Validation
        TypeWriter::storage_delete_type_vertex_property::<AnnotationIndependent>(snapshot, type_);
        Ok(())
    }

    pub(crate) fn set_annotation_regex(
        &self,
        snapshot: &mut Snapshot,
        type_: AttributeType<'static>,
        regex: AnnotationRegex,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_annotation_regex_compatible_value_type(
            snapshot,
            type_.clone(),
            TypeReader::get_value_type_without_source(snapshot, type_.clone())?
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        OperationTimeValidation::validate_set_annotation_is_compatible_with_declared_annotations(
            snapshot, type_.clone(), AnnotationCategory::Regex
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_annotation_is_compatible_with_inherited_annotations(
            snapshot, type_.clone(), AnnotationCategory::Regex
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        if let Some(supertype) = TypeReader::get_supertype(snapshot, type_.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })? {
            OperationTimeValidation::validate_type_regex_narrows_annotation(snapshot, supertype, regex.clone())
                .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        }

        // TODO: Validate that regex value is correct
        // TODO: Verify that there is no regex on owns
        // TODO: Verify that there is no regex on supertypes
        // TODO: Verify that there is no regex on subtypes (only for schema validation!)

        TypeWriter::storage_insert_type_vertex_property::<AnnotationRegex>(snapshot, type_, Some(regex));
        Ok(())
    }

    pub(crate) fn unset_annotation_regex(
        &self, snapshot: &mut Snapshot, type_: AttributeType<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_annotation_is_not_inherited(
            snapshot, type_.clone(), AnnotationCategory::Regex,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_annotation_set_only_for_interface::<Owns<'static>, Snapshot>(
            snapshot, type_.clone(), AnnotationCategory::Regex,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        // TODO debug assert that stored regex matches
        TypeWriter::storage_delete_type_vertex_property::<AnnotationRegex>(snapshot, type_);
        Ok(())
    }

    pub(crate) fn set_owns_annotation_distinct(
        &self, snapshot: &mut Snapshot, edge: Owns<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_owns_distinct_annotation_ordering(snapshot, edge.clone(), None, Some(true))
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_put_type_edge_property::<AnnotationDistinct>(snapshot, edge, None);
        Ok(())
    }

    pub(crate) fn set_relates_overridden(
        &self,
        snapshot: &mut Snapshot,
        relates: Relates<'static>,
        overridden: Relates<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: More validation - instances exist.
        OperationTimeValidation::validate_relates_is_inherited(snapshot, relates.relation(), overridden.role())
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_role_supertype_ordering_match(
            snapshot, relates.role().clone(), overridden.role().clone(), None
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        Self::set_supertype(self, snapshot, relates.role(), overridden.role())?;
        TypeWriter::storage_set_type_edge_overridden(snapshot, relates.clone(), overridden.clone()); // .attribute().clone());
        Ok(())
    }

    pub(crate) fn unset_relates_overridden(
        &self,
        snapshot: &mut Snapshot,
        relates: Relates<'static>,
    ) -> Result<(), ConceptWriteError> {
        // TODO: Validation
        // TODO: More validation - instances exist.

        self.set_role_type_root_supertype(snapshot, relates.role());
        TypeWriter::storage_delete_type_edge_overridden(snapshot, relates);
        Ok(())
    }

    pub(crate) fn set_relates_annotation_distinct(
        &self, snapshot: &mut Snapshot, edge: Relates<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_relates_distinct_annotation_ordering(snapshot, edge.clone(), None, Some(true))
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_put_type_edge_property::<AnnotationDistinct>(snapshot, edge, None);
        Ok(())
    }

    pub(crate) fn unset_edge_annotation_distinct<EDGE>(
        &self,
        snapshot: &mut Snapshot,
        edge: EDGE,
    ) -> Result<(), ConceptWriteError>
        where
            EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone
    {
        OperationTimeValidation::validate_unset_edge_annotation_is_not_inherited(
            snapshot, edge.clone(), AnnotationCategory::Distinct,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        // TODO: Validation
        TypeWriter::storage_delete_type_edge_property::<AnnotationDistinct>(snapshot, edge);
        Ok(())
    }

    pub(crate) fn set_edge_annotation_unique(
        &self, snapshot: &mut Snapshot, owns: Owns<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_owns_value_type_keyable(
            snapshot, owns.clone()
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_declared_annotations(
            snapshot, owns.clone(), AnnotationCategory::Unique
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_inherited_annotations(
            snapshot, owns.clone(), AnnotationCategory::Unique
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_put_type_edge_property::<AnnotationUnique>(snapshot, owns, None);
        Ok(())
    }

    pub(crate) fn unset_edge_annotation_unique(
        &self,
        snapshot: &mut Snapshot,
        owns: Owns<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_edge_annotation_is_not_inherited(
            snapshot, owns.clone(), AnnotationCategory::Unique,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_type_edge_property::<AnnotationUnique>(snapshot, owns);
        Ok(())
    }

    pub(crate) fn set_edge_annotation_key(
        &self, snapshot: &mut Snapshot, owns: Owns<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_owns_value_type_keyable(
            snapshot, owns.clone()
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_declared_annotations(
            snapshot, owns.clone(), AnnotationCategory::Key
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_inherited_annotations(
            snapshot, owns.clone(), AnnotationCategory::Key
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_put_type_edge_property::<AnnotationKey>(snapshot, owns, None);
        Ok(())
    }

    pub(crate) fn unset_edge_annotation_key<T: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone>(
        &self,
        snapshot: &mut Snapshot,
        edge: T,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_edge_annotation_is_not_inherited(
            snapshot, edge.clone(), AnnotationCategory::Key,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_type_edge_property::<AnnotationKey>(snapshot, edge);
        Ok(())
    }

    pub(crate) fn set_edge_annotation_cardinality<EDGE>(
        &self,
        snapshot: &mut Snapshot,
        edge: EDGE,
        cardinality: AnnotationCardinality,
    ) -> Result<(), ConceptWriteError>
        where
            EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone + Hash + Eq
    {
        OperationTimeValidation::validate_cardinality_arguments(cardinality)
            .map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_declared_annotations(
            snapshot, edge.clone(), AnnotationCategory::Cardinality
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_inherited_annotations(
            snapshot, edge.clone(), AnnotationCategory::Cardinality
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        if let Some(override_edge) = TypeReader::get_implementation_override(snapshot, edge.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })? {
            OperationTimeValidation::validate_cardinality_narrows_annotation(snapshot, override_edge, cardinality)
                .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        }

        TypeWriter::storage_insert_type_edge_property::<AnnotationCardinality>(snapshot, edge, Some(cardinality));
        Ok(())
    }

    pub(crate) fn unset_edge_annotation_cardinality<T: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone>(
        &self,
        snapshot: &mut Snapshot,
        edge: T,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_edge_annotation_is_not_inherited(
            snapshot, edge.clone(), AnnotationCategory::Cardinality,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_type_edge_property::<AnnotationCardinality>(snapshot, edge);
        Ok(())
    }

    pub(crate) fn set_edge_annotation_regex(
        &self,
        snapshot: &mut Snapshot,
        owns: Owns<'static>,
        regex: AnnotationRegex,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_annotation_regex_compatible_value_type(
            snapshot,
            owns.attribute(),
            TypeReader::get_value_type_without_source(snapshot, owns.attribute().clone())?
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_declared_annotations(
            snapshot, owns.clone(), AnnotationCategory::Regex
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_edge_annotation_is_compatible_with_inherited_annotations(
            snapshot, owns.clone(), AnnotationCategory::Regex
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        OperationTimeValidation::validate_annotation_set_only_for_interface_implementation(
            snapshot, owns.clone(), AnnotationCategory::Regex,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        // TODO: Maybe delete?
        // OperationTimeValidation::validate_owns_attribute_type_does_not_have_annotation_category_when_setting_owns_annotation(
        //     snapshot, owns.clone(), AnnotationCategory::Regex,
        // ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        if let Some(override_edge) = TypeReader::get_implementation_override(snapshot, owns.clone())
            .map_err(|source| ConceptWriteError::ConceptRead { source })? {
            OperationTimeValidation::validate_edge_regex_narrows_annotation(snapshot, override_edge, regex.clone())
                .map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        }

        // TODO: Validate that regex value is correct
        // TODO: Verify that there is no regex on supertypes
        // TODO: Verify that there is no regex on subtypes (schema validation only)

        TypeWriter::storage_put_type_edge_property::<AnnotationRegex>(snapshot, owns, Some(regex));
        Ok(())
    }

    pub(crate) fn unset_edge_annotation_regex<T: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone>(
        &self,
        snapshot: &mut Snapshot,
        edge: T,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_edge_annotation_is_not_inherited(
            snapshot, edge.clone(), AnnotationCategory::Regex,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_type_edge_property::<AnnotationRegex>(snapshot, edge);
        Ok(())
    }

    pub(crate) fn set_annotation_cascade(
        &self, snapshot: &mut Snapshot, type_: impl KindAPI<'static>,
    ) -> Result<(), ConceptWriteError> {

        OperationTimeValidation::validate_set_annotation_is_compatible_with_declared_annotations(
            snapshot, type_.clone(), AnnotationCategory::Cascade
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;
        OperationTimeValidation::validate_set_annotation_is_compatible_with_inherited_annotations(
            snapshot, type_.clone(), AnnotationCategory::Cascade
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_put_type_vertex_property::<AnnotationCascade>(snapshot, type_, None);
        Ok(())
    }

    pub(crate) fn unset_annotation_cascade(
        &self, snapshot: &mut Snapshot, type_: impl KindAPI<'static>,
    ) -> Result<(), ConceptWriteError> {
        OperationTimeValidation::validate_unset_annotation_is_not_inherited(
            snapshot, type_.clone(), AnnotationCategory::Cascade,
        ).map_err(|source| ConceptWriteError::SchemaValidation { source })?;

        TypeWriter::storage_delete_type_vertex_property::<AnnotationCascade>(snapshot, type_);
        Ok(())
    }
}
