/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{collections::HashSet, hash::Hash, sync::Arc};

use bytes::{byte_array::ByteArray, Bytes};
use durability::DurabilityService;
use encoding::{
    graph::type_::{
        edge::{
            build_edge_owns, build_edge_owns_reverse, build_edge_plays, build_edge_plays_reverse, build_edge_relates,
            build_edge_relates_reverse, build_edge_sub, build_edge_sub_reverse, TypeEdge,
        },
        index::LabelToTypeVertexIndex,
        property::{
            build_property_type_annotation_abstract, build_property_type_annotation_cardinality,
            build_property_type_annotation_distinct, build_property_type_annotation_independent,
            build_property_type_edge_annotation_cardinality, build_property_type_edge_annotation_distinct,
            build_property_type_edge_ordering, build_property_type_label, build_property_type_ordering,
            build_property_type_value_type,
        },
        vertex::{new_vertex_attribute_type, new_vertex_entity_type, new_vertex_relation_type, new_vertex_role_type},
        vertex_generator::TypeVertexGenerator,
        Kind,
    },
    layout::prefix::Prefix,
    value::{label::Label, value_type::ValueType},
    AsBytes, Keyable,
};
use primitive::maybe_owns::MaybeOwns;
use resource::constants::snapshot::BUFFER_KEY_INLINE;
use storage::{
    snapshot::{ReadableSnapshot, WriteSnapshot},
    MVCCStorage,
};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    type_::{
        annotation::{Annotation, AnnotationAbstract, AnnotationCardinality},
        attribute_type::{AttributeType, AttributeTypeAnnotation},
        entity_type::{EntityType, EntityTypeAnnotation},
        owns::{Owns, OwnsAnnotation},
        plays::Plays,
        relates::Relates,
        relation_type::{RelationType, RelationTypeAnnotation},
        role_type::{RoleType, RoleTypeAnnotation},
        serialise_annotation_cardinality, serialise_ordering,
        type_cache::TypeCache,
        type_reader::TypeReader,
        IntoCanonicalTypeEdge, ObjectTypeAPI, Ordering, TypeAPI,
    },
};

// TODO: this should be parametrised into the database options? Would be great to have it be changable at runtime!
pub(crate) const RELATION_INDEX_THRESHOLD: u64 = 8;

pub struct TypeManager<Snapshot> {
    snapshot: Arc<Snapshot>,
    vertex_generator: Arc<TypeVertexGenerator>,
    type_cache: Option<Arc<TypeCache>>,
}

impl<Snapshot> TypeManager<Snapshot> {
    pub fn initialise_types<D: DurabilityService>(
        storage: Arc<MVCCStorage<D>>,
        vertex_generator: Arc<TypeVertexGenerator>,
    ) -> Result<(), ConceptWriteError> {
        let snapshot = Arc::new(storage.clone().open_snapshot_write());
        {
            let type_manager = TypeManager::new(snapshot.clone(), vertex_generator.clone(), None);
            let root_entity = type_manager.create_entity_type(&Kind::Entity.root_label(), true)?;
            root_entity.set_annotation(&type_manager, EntityTypeAnnotation::Abstract(AnnotationAbstract::new()))?;
            let root_relation = type_manager.create_relation_type(&Kind::Relation.root_label(), true)?;
            root_relation.set_annotation(&type_manager, RelationTypeAnnotation::Abstract(AnnotationAbstract::new()))?;
            let root_role = type_manager.create_role_type(
                &Kind::Role.root_label(),
                root_relation.clone(),
                true,
                Ordering::Unordered,
            )?;
            root_role.set_annotation(&type_manager, RoleTypeAnnotation::Abstract(AnnotationAbstract::new()))?;
            let root_attribute = type_manager.create_attribute_type(&Kind::Attribute.root_label(), true)?;
            root_attribute
                .set_annotation(&type_manager, AttributeTypeAnnotation::Abstract(AnnotationAbstract::new()))?;
        }
        Arc::into_inner(snapshot).unwrap().commit().unwrap();
        Ok(())
    }

    pub fn finalise(self) -> Result<(), Vec<ConceptWriteError>> {
        todo!("Do we need to finalise anything here?");
        Ok(())
    }
}

// TODO:
//   if we drop/close without committing, then we need to release all the IDs taken back to the IDGenerator
//   this is only applicable for type manager where we can only have 1 concurrent txn and IDs are precious

macro_rules! get_type_methods {
    ($(
        fn $method_name:ident() -> $output_type:ident = $cache_method:ident | $new_vertex_method:ident;
    )*) => {
        $(
            pub fn $method_name(&self, label: &Label<'_>) -> Result<Option<$output_type<'static>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(cache.$cache_method(label))
                } else {
                    TypeReader::get_labelled_type::<$output_type<'static>>(self.snapshot.as_ref(), label)
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
            pub(crate) fn $method_name(&self, type_: $type_<'static>) -> Result<Option<$type_<'static>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(cache.$cache_method(type_))
                } else {
                    TypeReader::get_supertype(self.snapshot.as_ref(), type_)
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
            pub(crate) fn $method_name(&self, type_: $type_<'static>) -> Result<MaybeOwns<'_, Vec<$type_<'static>>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let supertypes = TypeReader::get_supertypes_transitive(self.snapshot.as_ref(), type_)?;
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
            pub(crate) fn $method_name(&self, type_: $type_<'static>) -> Result<MaybeOwns<'_, Vec<$type_<'static>>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let subtypes = TypeReader::get_subtypes(self.snapshot.as_ref(), type_)?;
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
            pub(crate) fn $method_name(&self, type_: $type_<'static>) -> Result<MaybeOwns<'_, Vec<$type_<'static>>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let subtypes = TypeReader::get_subtypes_transitive(self.snapshot.as_ref(), type_)?;
                    Ok(MaybeOwns::Owned(subtypes))
                }
            }
        )*
    }
}

macro_rules! get_type_is_root_methods {
    ($(
        fn $method_name:ident() -> $type_:ident = $cache_method:ident | $base_variant:expr;
    )*) => {
        $(
            pub(crate) fn $method_name(&self, type_: $type_<'static>) -> Result<bool, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(cache.$cache_method(type_))
                } else {
                    let type_label = TypeReader::get_label(self.snapshot.as_ref(), type_)?.unwrap();
                    Ok(Self::check_type_is_root(&type_label, $base_variant))
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
            pub(crate) fn $method_name(&self, type_: $type_<'static>) -> Result<MaybeOwns<'_, Label<'static>>, ConceptReadError> {
                if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    Ok(MaybeOwns::Owned(TypeReader::get_label(self.snapshot.as_ref(), type_)?.unwrap()))
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
                &self, type_: $type_<'static>
            ) -> Result<MaybeOwns<'_, HashSet<$annotation_type>>, ConceptReadError> {
                 if let Some(cache) = &self.type_cache {
                    Ok(MaybeOwns::Borrowed(cache.$cache_method(type_)))
                } else {
                    let mut annotations: HashSet<$annotation_type> = HashSet::new();
                    let annotations = TypeReader::get_type_annotations(self.snapshot.as_ref(), type_)?
                        .into_iter()
                        .map(|annotation| $annotation_type::from(annotation))
                        .collect();
                    Ok(MaybeOwns::Owned(annotations))
                }
            }
        )*
    }
}

// TODO: The '_s is only here for the enforcement of pass-by-value of types. If we drop that, we can move it to the function signatures
impl<'_s, Snapshot: ReadableSnapshot> TypeManager<Snapshot>
where
    '_s: 'static,
{
    pub fn new(
        snapshot: Arc<Snapshot>,
        vertex_generator: Arc<TypeVertexGenerator>,
        schema_cache: Option<Arc<TypeCache>>,
    ) -> Self {
        TypeManager { snapshot, vertex_generator, type_cache: schema_cache }
    }
    pub(crate) fn check_type_is_root(type_label: &Label<'_>, kind: Kind) -> bool {
        type_label == &kind.root_label()
    }

    get_type_methods! {
        fn get_entity_type() -> EntityType = get_entity_type | new_vertex_entity_type;
        fn get_relation_type() -> RelationType = get_relation_type | new_vertex_relation_type;
        fn get_role_type() -> RoleType = get_role_type | new_vertex_role_type;
        fn get_attribute_type() -> AttributeType = get_attribute_type | new_vertex_attribute_type;
    }

    get_supertype_methods! {
        fn get_entity_type_supertype() -> EntityType = get_entity_type_supertype;
        fn get_relation_type_supertype() -> RelationType = get_relation_type_supertype;
        fn get_role_type_supertype() -> RoleType = get_role_type_supertype;
        fn get_attribute_type_supertype() -> AttributeType = get_attribute_type_supertype;
    }

    get_supertypes_methods! {
        fn get_entity_type_supertypes() -> EntityType = get_entity_type_supertypes;
        fn get_relation_type_supertypes() -> RelationType = get_relation_type_supertypes;
        fn get_role_type_supertypes() -> RoleType = get_role_type_supertypes;
        fn get_attribute_type_supertypes() -> AttributeType = get_attribute_type_supertypes;
    }

    get_subtypes_methods! {
        fn get_entity_type_subtypes() -> EntityType = get_entity_type_subtypes;
        fn get_relation_type_subtypes() -> RelationType = get_relation_type_subtypes;
        fn get_role_type_subtypes() -> RoleType = get_role_type_subtypes;
        fn get_attribute_type_subtypes() -> AttributeType = get_attribute_type_subtypes;
    }

    get_subtypes_transitive_methods! {
        fn get_entity_type_subtypes_transitive() -> EntityType = get_entity_type_subtypes_transitive;
        fn get_relation_type_subtypes_transitive() -> RelationType = get_relation_type_subtypes_transitive;
        fn get_role_type_subtypes_transitive() -> RoleType = get_role_type_subtypes_transitive;
        fn get_attribute_type_subtypes_transitive() -> AttributeType = get_attribute_type_subtypes_transitive;
    }

    get_type_is_root_methods! {
        fn get_entity_type_is_root() -> EntityType = get_entity_type_is_root | Kind::Entity;
        fn get_relation_type_is_root() -> RelationType = get_relation_type_is_root | Kind::Relation;
        fn get_role_type_is_root() -> RoleType = get_role_type_is_root | Kind::Role;
        fn get_attribute_type_is_root() -> AttributeType = get_attribute_type_is_root | Kind::Attribute;
    }

    get_type_label_methods! {
        fn get_entity_type_label() -> EntityType = get_entity_type_label;
        fn get_relation_type_label() -> RelationType = get_relation_type_label;
        fn get_role_type_label() -> RoleType = get_role_type_label;
        fn get_attribute_type_label() -> AttributeType = get_attribute_type_label;
    }

    pub(crate) fn get_entity_type_owns(
        &self,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_entity_type_owns(entity_type)))
        } else {
            let owns = TypeReader::get_owns(self.snapshot.as_ref(), entity_type.clone())?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_relation_type_owns(
        &self,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Owns<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_relation_type_owns(relation_type)))
        } else {
            let owns = TypeReader::get_owns(self.snapshot.as_ref(), relation_type.clone())?;
            Ok(MaybeOwns::Owned(owns))
        }
    }

    pub(crate) fn get_relation_type_relates(
        &self,
        relation_type: RelationType<'static>,
    ) -> Result<MaybeOwns<'_, HashSet<Relates<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_relation_type_relates(relation_type)))
        } else {
            let relates = TypeReader::get_relates(self.snapshot.as_ref(), relation_type.clone())?;
            Ok(MaybeOwns::Owned(relates))
        }
    }

    pub(crate) fn relation_index_available(&self, relation_type: RelationType<'_>) -> Result<bool, ConceptReadError> {
        // TODO: it would be good if this doesn't require recomputation
        let mut max_card = 0;
        let relates = relation_type.get_relates(self)?;
        for relates in relates.iter() {
            let card = relates.role().get_cardinality(self)?;
            match card.end() {
                None => return Ok(false),
                Some(end) => max_card += end,
            }
        }
        Ok(max_card <= RELATION_INDEX_THRESHOLD)
    }

    pub(crate) fn get_entity_type_plays<'this>(
        &'this self,
        entity_type: EntityType<'static>,
    ) -> Result<MaybeOwns<'this, HashSet<Plays<'static>>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_entity_type_plays(entity_type)))
        } else {
            let plays = TypeReader::get_plays(self.snapshot.as_ref(), entity_type.clone())?;
            Ok(MaybeOwns::Owned(plays))
        }
    }

    pub(crate) fn get_attribute_type_value_type(
        &self,
        attribute_type: AttributeType<'static>,
    ) -> Result<Option<ValueType>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(cache.get_attribute_type_value_type(attribute_type))
        } else {
            TypeReader::get_value_type(self.snapshot.as_ref(), attribute_type)
        }
    }

    get_type_annotations! {
        fn get_entity_type_annotations() -> EntityType = get_entity_type_annotations | EntityTypeAnnotation;
        fn get_relation_type_annotations() -> RelationType = get_relation_type_annotations | RelationTypeAnnotation;
        fn get_role_type_annotations() -> RoleType = get_role_type_annotations | RoleTypeAnnotation;
        fn get_attribute_type_annotations() -> AttributeType = get_attribute_type_annotations | AttributeTypeAnnotation;
    }

    pub(crate) fn get_owns_annotations<'this>(
        &'this self,
        owns: Owns<'this>,
    ) -> Result<MaybeOwns<'this, HashSet<OwnsAnnotation>>, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(MaybeOwns::Borrowed(cache.get_owns_annotations(owns)))
        } else {
            let annotations: HashSet<OwnsAnnotation> =
                TypeReader::get_type_edge_annotations(self.snapshot.as_ref(), owns)?
                    .into_iter()
                    .map(|annotation| OwnsAnnotation::from(annotation))
                    .collect();
            Ok(MaybeOwns::Owned(annotations))
        }
    }

    pub(crate) fn get_owns_ordering(&self, owns: Owns<'_s>) -> Result<Ordering, ConceptReadError> {
        if let Some(cache) = &self.type_cache {
            Ok(cache.get_owns_ordering(owns))
        } else {
            TypeReader::get_type_edge_ordering(self.snapshot.as_ref(), owns)
        }
    }

    pub(crate) const fn role_default_cardinality(&self) -> AnnotationCardinality {
        // TODO: read from database properties the default role cardinality the db was created with
        AnnotationCardinality::new(1, Some(1))
    }
}

// TODO: Move this somewhere too?
impl<D> TypeManager<WriteSnapshot<D>> {
    pub fn create_entity_type(
        &self,
        label: &Label<'_>,
        is_root: bool,
    ) -> Result<EntityType<'static>, ConceptWriteError> {
        // TODO: validate type doesn't exist already
        let type_vertex = self
            .vertex_generator
            .create_entity_type(self.snapshot.as_ref())
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let entity = EntityType::new(type_vertex);
        self.storage_set_label(entity.clone(), label);
        if !is_root {
            self.storage_set_supertype(
                entity.clone(),
                self.get_entity_type(&Kind::Entity.root_label()).unwrap().unwrap(),
            );
        }
        Ok(entity)
    }

    pub fn create_relation_type(
        &self,
        label: &Label<'_>,
        is_root: bool,
    ) -> Result<RelationType<'static>, ConceptWriteError> {
        // TODO: validate type doesn't exist already
        let type_vertex = self
            .vertex_generator
            .create_relation_type(self.snapshot.as_ref())
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let relation = RelationType::new(type_vertex);
        self.storage_set_label(relation.clone(), label);
        if !is_root {
            self.storage_set_supertype(
                relation.clone(),
                self.get_relation_type(&Kind::Relation.root_label()).unwrap().unwrap(),
            );
        }
        Ok(relation)
    }

    pub(crate) fn create_role_type(
        &self,
        label: &Label<'_>,
        relation_type: RelationType<'static>,
        is_root: bool,
        ordering: Ordering,
    ) -> Result<RoleType<'static>, ConceptWriteError> {
        // TODO: validate type doesn't exist already
        let type_vertex = self
            .vertex_generator
            .create_role_type(self.snapshot.as_ref())
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let role = RoleType::new(type_vertex);
        self.storage_set_label(role.clone(), label);
        self.storage_set_relates(relation_type, role.clone());
        self.storage_set_role_ordering(role.clone(), ordering);
        if !is_root {
            self.storage_set_supertype(role.clone(), self.get_role_type(&Kind::Role.root_label()).unwrap().unwrap());
        }
        Ok(role)
    }

    pub fn create_attribute_type(
        &self,
        label: &Label<'_>,
        is_root: bool,
    ) -> Result<AttributeType<'static>, ConceptWriteError> {
        // TODO: validate type doesn't exist already
        let type_vertex = self
            .vertex_generator
            .create_attribute_type(self.snapshot.as_ref())
            .map_err(|err| ConceptWriteError::Encoding { source: err })?;
        let attribute_type = AttributeType::new(type_vertex);
        self.storage_set_label(attribute_type.clone(), label);
        if !is_root {
            self.storage_set_supertype(
                attribute_type.clone(),
                self.get_attribute_type(&Kind::Attribute.root_label()).unwrap().unwrap(),
            );
        }
        Ok(attribute_type)
    }

    pub(crate) fn delete_entity_type(&self, entity_type: EntityType<'_>) {
        let key = entity_type.into_vertex().into_storage_key().into_owned_array();
        todo!("Do we need to lock?");
        self.snapshot.delete(key)
    }

    pub(crate) fn delete_relation_type(&self, relation_type: RelationType<'_>) {
        let key = relation_type.into_vertex().into_storage_key().into_owned_array();
        todo!("Do we need to lock?");
        self.snapshot.delete(key)
    }

    pub(crate) fn delete_attribute_type(&self, attribute_type: AttributeType<'_>) {
        let key = attribute_type.into_vertex().into_storage_key().into_owned_array();
        todo!("Do we need to lock?");
        self.snapshot.delete(key);
    }

    pub(crate) fn delete_role_type(&self, role_type: RoleType<'_>) {
        let key = role_type.into_vertex().into_storage_key().into_owned_array();
        todo!("Do we need to lock?");
        self.snapshot.delete(key);
    }

    pub(crate) fn storage_set_label(&self, owner: impl TypeAPI<'static>, label: &Label<'_>) {
        self.storage_may_delete_label(owner.clone());

        let vertex_to_label_key = build_property_type_label(owner.clone().into_vertex());
        let label_value = ByteArray::from(label.scoped_name().bytes());
        self.snapshot.as_ref().put_val(vertex_to_label_key.into_storage_key().into_owned_array(), label_value);

        let label_to_vertex_key = LabelToTypeVertexIndex::build(label);
        let vertex_value = ByteArray::from(owner.into_vertex().bytes());
        self.snapshot.as_ref().put_val(label_to_vertex_key.into_storage_key().into_owned_array(), vertex_value);
    }

    fn storage_may_delete_label(&self, owner: impl TypeAPI<'static>) {
        let existing_label = TypeReader::get_label(self.snapshot.as_ref(), owner.clone()).unwrap();
        if let Some(label) = existing_label {
            let vertex_to_label_key = build_property_type_label(owner.into_vertex());
            self.snapshot.as_ref().delete(vertex_to_label_key.into_storage_key().into_owned_array());
            let label_to_vertex_key = LabelToTypeVertexIndex::build(&label);
            self.snapshot.as_ref().delete(label_to_vertex_key.into_storage_key().into_owned_array());
        }
    }

    fn storage_set_role_ordering(&self, role: RoleType<'_>, ordering: Ordering) {
        self.snapshot.as_ref().put_val(
            build_property_type_ordering(role.into_vertex()).into_storage_key().into_owned_array(),
            ByteArray::boxed(serialise_ordering(ordering)),
        )
    }

    pub(crate) fn storage_set_supertype<K: TypeAPI<'static>>(&self, subtype: K, supertype: K) {
        self.storage_may_delete_supertype(subtype.clone());
        let sub = build_edge_sub(subtype.clone().into_vertex(), supertype.clone().into_vertex());
        self.snapshot.as_ref().put(sub.into_storage_key().into_owned_array());
        let sub_reverse = build_edge_sub_reverse(supertype.into_vertex(), subtype.into_vertex());
        self.snapshot.as_ref().put(sub_reverse.into_storage_key().into_owned_array());
    }

    fn storage_may_delete_supertype(&self, subtype: impl TypeAPI<'static>) {
        let supertype_vertex =
            TypeReader::get_supertype_vertex(self.snapshot.as_ref(), subtype.clone().into_vertex()).unwrap();
        if let Some(supertype) = supertype_vertex {
            let sub = build_edge_sub(subtype.clone().into_vertex(), supertype.clone());
            self.snapshot.as_ref().delete(sub.into_storage_key().into_owned_array());
            let sub_reverse = build_edge_sub_reverse(supertype, subtype.into_vertex());
            self.snapshot.as_ref().delete(sub_reverse.into_storage_key().into_owned_array());
        }
    }

    pub(crate) fn storage_set_owns(
        &self,
        owner: impl ObjectTypeAPI<'static>,
        attribute: AttributeType<'static>,
        ordering: Ordering,
    ) {
        let owns = build_edge_owns(owner.clone().into_vertex(), attribute.clone().into_vertex());
        self.snapshot.as_ref().put(owns.clone().into_storage_key().into_owned_array());
        let owns_reverse = build_edge_owns_reverse(attribute.into_vertex(), owner.into_vertex());
        self.snapshot.as_ref().put(owns_reverse.into_storage_key().into_owned_array());
        self.storage_set_owns_ordering(owns, ordering);
    }

    pub(crate) fn storage_set_owns_ordering(&self, owns_edge: TypeEdge<'_>, ordering: Ordering) {
        debug_assert_eq!(owns_edge.prefix(), Prefix::EdgeOwns);
        self.snapshot.as_ref().put_val(
            build_property_type_edge_ordering(owns_edge).into_storage_key().into_owned_array(),
            ByteArray::boxed(serialise_ordering(ordering)),
        )
    }

    pub(crate) fn storage_delete_owns(&self, owner: impl ObjectTypeAPI<'static>, attribute: AttributeType<'static>) {
        let owns_edge = build_edge_owns(owner.clone().into_vertex(), attribute.clone().into_vertex());
        self.snapshot.as_ref().delete(owns_edge.as_storage_key().into_owned_array());
        let owns_reverse = build_edge_owns_reverse(attribute.into_vertex(), owner.into_vertex());
        self.snapshot.as_ref().delete(owns_reverse.into_storage_key().into_owned_array());
        self.storage_delete_owns_ordering(owns_edge);
    }

    pub(crate) fn storage_delete_owns_ordering(&self, owns_edge: TypeEdge<'_>) {
        debug_assert_eq!(owns_edge.prefix(), Prefix::EdgeOwns);
        self.snapshot
            .as_ref()
            .delete(build_property_type_edge_ordering(owns_edge).into_storage_key().into_owned_array())
    }
    pub(crate) fn storage_set_plays(&self, player: impl ObjectTypeAPI<'static>, role: RoleType<'static>) {
        let plays = build_edge_plays(player.clone().into_vertex(), role.clone().into_vertex());
        self.snapshot.as_ref().put(plays.into_storage_key().into_owned_array());
        let plays_reverse = build_edge_plays_reverse(role.into_vertex(), player.into_vertex());
        self.snapshot.as_ref().put(plays_reverse.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_delete_plays(&self, player: impl ObjectTypeAPI<'static>, role: RoleType<'static>) {
        let plays = build_edge_plays(player.clone().into_vertex(), role.clone().into_vertex());
        self.snapshot.as_ref().delete(plays.into_storage_key().into_owned_array());
        let plays_reverse = build_edge_plays_reverse(role.into_vertex(), player.into_vertex());
        self.snapshot.as_ref().delete(plays_reverse.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_set_relates(&self, relation: RelationType<'static>, role: RoleType<'static>) {
        let relates = build_edge_relates(relation.clone().into_vertex(), role.clone().into_vertex());
        self.snapshot.as_ref().put(relates.into_storage_key().into_owned_array());
        let relates_reverse = build_edge_relates_reverse(role.into_vertex(), relation.into_vertex());
        self.snapshot.as_ref().put(relates_reverse.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_delete_relates(&self, relation: RelationType<'static>, role: RoleType<'static>) {
        let relates = build_edge_relates(relation.clone().into_vertex(), role.clone().into_vertex());
        self.snapshot.as_ref().delete(relates.into_storage_key().into_owned_array());
        let relates_reverse = build_edge_relates_reverse(role.into_vertex(), relation.into_vertex());
        self.snapshot.as_ref().delete(relates_reverse.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_set_value_type(&self, attribute: AttributeType<'static>, value_type: ValueType) {
        let property_key =
            build_property_type_value_type(attribute.into_vertex()).into_storage_key().into_owned_array();
        let property_value = ByteArray::copy(&value_type.value_type_id().bytes());
        self.snapshot.as_ref().put_val(property_key, property_value);
    }

    pub(crate) fn storage_set_annotation_abstract(&self, type_: impl TypeAPI<'static>) {
        let annotation_property = build_property_type_annotation_abstract(type_.into_vertex());
        self.snapshot.as_ref().put(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_delete_annotation_abstract(&self, type_: impl TypeAPI<'static>) {
        let annotation_property = build_property_type_annotation_abstract(type_.into_vertex());
        self.snapshot.as_ref().delete(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_set_annotation_distinct(&self, type_: impl TypeAPI<'static>) {
        let annotation_property = build_property_type_annotation_distinct(type_.into_vertex());
        self.snapshot.as_ref().put(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_delete_annotation_distinct(&self, type_: impl TypeAPI<'static>) {
        let annotation_property = build_property_type_annotation_distinct(type_.into_vertex());
        self.snapshot.as_ref().delete(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_set_edge_annotation_distinct<'b>(&self, edge: impl IntoCanonicalTypeEdge<'b>) {
        let annotation_property = build_property_type_edge_annotation_distinct(edge.into_type_edge());
        self.snapshot.as_ref().put(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_delete_edge_annotation_distinct<'b>(&self, edge: impl IntoCanonicalTypeEdge<'b>) {
        let annotation_property = build_property_type_edge_annotation_distinct(edge.into_type_edge());
        self.snapshot.as_ref().delete(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_set_annotation_independent(&self, type_: impl TypeAPI<'static>) {
        let annotation_property = build_property_type_annotation_independent(type_.into_vertex());
        self.snapshot.as_ref().put(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_storage_annotation_independent(&self, type_: impl TypeAPI<'static>) {
        let annotation_property = build_property_type_annotation_independent(type_.into_vertex());
        self.snapshot.as_ref().delete(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_set_annotation_cardinality(
        &self,
        type_: impl TypeAPI<'static>,
        annotation: AnnotationCardinality,
    ) {
        self.snapshot.as_ref().put_val(
            build_property_type_annotation_cardinality(type_.into_vertex()).into_storage_key().into_owned_array(),
            ByteArray::boxed(serialise_annotation_cardinality(annotation)),
        );
    }

    pub(crate) fn storage_delete_annotation_cardinality(&self, type_: impl TypeAPI<'static>) {
        let annotation_property = build_property_type_annotation_cardinality(type_.into_vertex());
        self.snapshot.as_ref().delete(annotation_property.into_storage_key().into_owned_array());
    }

    pub(crate) fn storage_set_edge_annotation_cardinality<'b>(
        &self,
        edge: impl IntoCanonicalTypeEdge<'b>,
        annotation: AnnotationCardinality,
    ) {
        self.snapshot.as_ref().put_val(
            build_property_type_edge_annotation_cardinality(edge.into_type_edge())
                .into_storage_key()
                .into_owned_array(),
            ByteArray::boxed(serialise_annotation_cardinality(annotation)),
        );
    }

    pub(crate) fn storage_delete_edge_annotation_cardinality<'b>(&self, edge: impl IntoCanonicalTypeEdge<'b>) {
        let annotation_property = build_property_type_edge_annotation_cardinality(edge.into_type_edge());
        self.snapshot.as_ref().delete(annotation_property.into_storage_key().into_owned_array());
    }
}

pub trait ReadableType<'a, 'b>: TypeAPI<'a> {
    // Consider replacing 'b with 'static
    type SelfRead: ReadableType<'b, 'b>;
    type AnnotationType: Hash + Eq + From<Annotation>;
    const ROOT_KIND: Kind;
    fn read_from(b: Bytes<'b, BUFFER_KEY_INLINE>) -> Self::SelfRead;
}

impl<'a, 'b> ReadableType<'a, 'b> for AttributeType<'a> {
    type SelfRead = AttributeType<'b>;
    type AnnotationType = AttributeTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Attribute;

    fn read_from(b: Bytes<'b, BUFFER_KEY_INLINE>) -> Self::SelfRead {
        AttributeType::new(new_vertex_attribute_type(b))
    }
}

impl<'a, 'b> ReadableType<'a, 'b> for EntityType<'a> {
    type SelfRead = EntityType<'b>;
    type AnnotationType = EntityTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Entity;
    fn read_from(b: Bytes<'b, BUFFER_KEY_INLINE>) -> Self::SelfRead {
        EntityType::new(new_vertex_entity_type(b))
    }
}

impl<'a, 'b> ReadableType<'a, 'b> for RelationType<'a> {
    type SelfRead = RelationType<'b>;
    type AnnotationType = RelationTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Relation;
    fn read_from(b: Bytes<'b, BUFFER_KEY_INLINE>) -> RelationType<'b> {
        RelationType::new(new_vertex_relation_type(b))
    }
}

impl<'a, 'b> ReadableType<'a, 'b> for RoleType<'a> {
    type SelfRead = RoleType<'b>;
    type AnnotationType = RoleTypeAnnotation;
    const ROOT_KIND: Kind = Kind::Role;
    fn read_from(b: Bytes<'b, BUFFER_KEY_INLINE>) -> RoleType<'b> {
        RoleType::new(new_vertex_role_type(b))
    }
}
