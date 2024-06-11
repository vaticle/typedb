/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

use encoding::{
    graph::definition::{definition_key::DefinitionKey, r#struct::StructDefinition},
    value::{label::Label, value_type::ValueType},
};
use storage::{sequence_number::SequenceNumber, MVCCStorage, ReadSnapshotOpenError};

use crate::type_::{
    attribute_type::AttributeType,
    entity_type::EntityType,
    object_type::ObjectType,
    owns::{Owns, OwnsAnnotation},
    plays::Plays,
    relates::Relates,
    relation_type::RelationType,
    role_type::RoleType,
    type_manager::type_cache::{
        kind_cache::{
            AttributeTypeCache, CommonTypeCache, EntityTypeCache, OwnerPlayerCache, OwnsCache, PlaysCache,
            RelationTypeCache, RoleTypeCache,
        },
        selection,
        selection::{CacheGetter, HasCommonTypeCache, HasOwnerPlayerCache},
        struct_definition_cache::StructDefinitionCache,
    },
    KindAPI, Ordering, OwnerAPI, PlayerAPI, TypeAPI,
};

// TODO: could/should we slab allocate the schema cache?
pub struct TypeCache {
    open_sequence_number: SequenceNumber,

    // Types that are borrowable and returned from the cache
    entity_types: Box<[Option<EntityTypeCache>]>,
    relation_types: Box<[Option<RelationTypeCache>]>,
    role_types: Box<[Option<RoleTypeCache>]>,
    attribute_types: Box<[Option<AttributeTypeCache>]>,

    owns: HashMap<Owns<'static>, OwnsCache>,
    plays: HashMap<Plays<'static>, PlaysCache>,

    struct_definitions: Box<[Option<StructDefinitionCache>]>,

    entity_types_index_label: HashMap<Label<'static>, EntityType<'static>>,
    relation_types_index_label: HashMap<Label<'static>, RelationType<'static>>,
    role_types_index_label: HashMap<Label<'static>, RoleType<'static>>,
    attribute_types_index_label: HashMap<Label<'static>, AttributeType<'static>>,
    struct_definition_index_by_name: HashMap<String, DefinitionKey<'static>>,
}

selection::impl_cache_getter!(EntityTypeCache, EntityType, entity_types);
selection::impl_cache_getter!(AttributeTypeCache, AttributeType, attribute_types);
selection::impl_cache_getter!(RelationTypeCache, RelationType, relation_types);
selection::impl_cache_getter!(RoleTypeCache, RoleType, role_types);

selection::impl_has_common_type_cache!(EntityTypeCache, EntityType<'static>);
selection::impl_has_common_type_cache!(AttributeTypeCache, AttributeType<'static>);
selection::impl_has_common_type_cache!(RelationTypeCache, RelationType<'static>);
selection::impl_has_common_type_cache!(RoleTypeCache, RoleType<'static>);

selection::impl_has_owner_player_cache!(EntityTypeCache, EntityType<'static>);
selection::impl_has_owner_player_cache!(RelationTypeCache, RelationType<'static>);

impl TypeCache {
    // If creation becomes slow, We should restore pre-fetching of the schema
    //  with a single pass on disk (as it was in 1f339733feaf4542e47ff604462f107d2ade1f1a)
    pub fn new<D>(
        storage: Arc<MVCCStorage<D>>,
        open_sequence_number: SequenceNumber,
    ) -> Result<Self, TypeCacheCreateError> {
        use TypeCacheCreateError::SnapshotOpen;
        // note: since we will parse out many heterogenous properties/edges from the schema, we will scan once into a vector,
        //       then go through it again to pull out the type information.

        let snapshot =
            storage.open_snapshot_read_at(open_sequence_number).map_err(|error| SnapshotOpen { source: error })?;

        let entity_type_caches = EntityTypeCache::create(&snapshot);
        let relation_type_caches = RelationTypeCache::create(&snapshot);
        let role_type_caches = RoleTypeCache::create(&snapshot);
        let attribute_type_caches = AttributeTypeCache::create(&snapshot);
        let struct_definition_caches = StructDefinitionCache::create(&snapshot);

        let entity_types_index_label = Self::build_label_to_type_index(&entity_type_caches);
        let relation_types_index_label = Self::build_label_to_type_index(&relation_type_caches);
        let role_types_index_label = Self::build_label_to_type_index(&role_type_caches);
        let attribute_types_index_label = Self::build_label_to_type_index(&attribute_type_caches);
        let struct_definition_index_by_name = Self::build_name_to_struct_definition_index(&struct_definition_caches);

        Ok(TypeCache {
            open_sequence_number,
            entity_types: entity_type_caches,
            relation_types: relation_type_caches,
            role_types: role_type_caches,
            attribute_types: attribute_type_caches,
            owns: OwnsCache::create(&snapshot),
            plays: PlaysCache::create(&snapshot),
            struct_definitions: struct_definition_caches,

            entity_types_index_label,
            relation_types_index_label,
            role_types_index_label,
            attribute_types_index_label,
            struct_definition_index_by_name,
        })
    }

    fn build_label_to_type_index<T: KindAPI<'static>, Cache: HasCommonTypeCache<T>>(
        type_cache_array: &[Option<Cache>],
    ) -> HashMap<Label<'static>, T> {
        type_cache_array
            .iter()
            .filter_map(|entry| {
                entry
                    .as_ref()
                    .map(|cache| (cache.common_type_cache().label.clone(), cache.common_type_cache().type_.clone()))
            })
            .collect()
    }

    fn build_name_to_struct_definition_index(
        struct_cache_array: &[Option<StructDefinitionCache>],
    ) -> HashMap<String, DefinitionKey<'static>> {
        struct_cache_array
            .iter()
            .filter_map(|entry| {
                entry.as_ref().map(|cache| (cache.definition.name.clone(), cache.definition_key.clone()))
            })
            .collect()
    }

    pub(crate) fn get_object_type(&self, label: &Label<'_>) -> Option<ObjectType<'static>> {
        (self.get_entity_type(label).map(ObjectType::Entity))
            .or_else(|| self.get_relation_type(label).map(ObjectType::Relation))
    }

    pub(crate) fn get_entity_type(&self, label: &Label<'_>) -> Option<EntityType<'static>> {
        self.entity_types_index_label.get(label).cloned()
    }

    pub(crate) fn get_relation_type(&self, label: &Label<'_>) -> Option<RelationType<'static>> {
        self.relation_types_index_label.get(label).cloned()
    }

    pub(crate) fn get_role_type(&self, label: &Label<'_>) -> Option<RoleType<'static>> {
        self.role_types_index_label.get(label).cloned()
    }

    pub(crate) fn get_attribute_type(&self, label: &Label<'_>) -> Option<AttributeType<'static>> {
        self.attribute_types_index_label.get(label).cloned()
    }

    pub(crate) fn get_supertype<'a, 'this, T, CACHE>(&'this self, type_: T) -> Option<T::SelfStatic>
    where
        T: KindAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasCommonTypeCache<T::SelfStatic> + 'this,
    {
        Some(T::get_cache(self, type_).common_type_cache().supertype.as_ref()?.clone())
    }

    pub(crate) fn get_supertypes<'a, 'this, T, CACHE>(&'this self, type_: T) -> &'this Vec<T::SelfStatic>
    where
        T: KindAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasCommonTypeCache<T::SelfStatic> + 'this,
    {
        &T::get_cache(self, type_).common_type_cache().supertypes
    }
    pub(crate) fn get_subtypes<'a, 'this, T, CACHE>(&'this self, type_: T) -> &'this Vec<T::SelfStatic>
    where
        T: KindAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasCommonTypeCache<T::SelfStatic> + 'this,
    {
        &T::get_cache(self, type_).common_type_cache().subtypes_declared
    }

    pub(crate) fn get_subtypes_transitive<'a, 'this, T, CACHE>(&'this self, type_: T) -> &'this Vec<T::SelfStatic>
    where
        T: KindAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasCommonTypeCache<T::SelfStatic> + 'this,
    {
        &T::get_cache(self, type_).common_type_cache().subtypes_transitive
    }

    pub(crate) fn get_label<'a, 'this, T, CACHE>(&'this self, type_: T) -> &'this Label<'static>
    where
        T: KindAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasCommonTypeCache<T::SelfStatic> + 'this,
    {
        &T::get_cache(self, type_).common_type_cache().label
    }

    pub(crate) fn is_root<'a, 'this, T, CACHE>(&'this self, type_: T) -> bool
    where
        T: KindAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasCommonTypeCache<T::SelfStatic> + 'this,
    {
        T::get_cache(self, type_).common_type_cache().is_root
    }

    pub(crate) fn get_annotations<'a, 'this, T, CACHE>(
        &'this self,
        type_: T,
    ) -> &HashSet<<<T as TypeAPI<'a>>::SelfStatic as KindAPI<'static>>::AnnotationType>
    where
        T: KindAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasCommonTypeCache<T::SelfStatic> + 'this,
    {
        &T::get_cache(self, type_).common_type_cache().annotations_declared
    }

    pub(crate) fn get_owns_for_attribute_type<'a>(&self, attribute_type: AttributeType<'a>) -> &HashSet<Owns<'static>> {
        &AttributeType::get_cache(self, attribute_type).owns
    }

    pub(crate) fn get_owns_for_attribute_type_transitive<'a>(
        &self,
        attribute_type: AttributeType<'a>,
    ) -> &HashMap<ObjectType<'static>, Owns<'static>> {
        &AttributeType::get_cache(self, attribute_type).owns_transitive
    }

    pub(crate) fn get_owns<'a, 'this, T, CACHE>(&'this self, type_: T) -> &HashSet<Owns<'static>>
    where
        T: OwnerAPI<'a> + PlayerAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasOwnerPlayerCache + 'this,
    {
        &T::get_cache(self, type_).owner_player_cache().owns_declared
    }

    pub(crate) fn get_owns_transitive<'a, 'this, T, CACHE>(
        &'this self,
        type_: T,
    ) -> &HashMap<AttributeType<'static>, Owns<'static>>
    where
        T: OwnerAPI<'a> + PlayerAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasOwnerPlayerCache + 'this,
    {
        &T::get_cache(self, type_).owner_player_cache().owns_transitive
    }

    pub(crate) fn get_role_type_ordering<'a>(&self, role_type: RoleType<'a>) -> Ordering {
        RoleType::get_cache(&self, role_type).ordering
    }

    pub(crate) fn get_relation_type_relates<'a>(&self, relation_type: RelationType<'a>) -> &HashSet<Relates<'static>> {
        &RelationType::get_cache(self, relation_type).relates_declared
    }

    pub(crate) fn get_relation_type_relates_transitive<'a>(
        &self,
        relation_type: RelationType<'a>,
    ) -> &HashMap<RoleType<'static>, Relates<'static>> {
        &RelationType::get_cache(self, relation_type).relates_transitive
    }

    pub(crate) fn get_plays_for_role_type<'a>(&self, role_type: RoleType<'a>) -> &HashSet<Plays<'static>> {
        &RoleType::get_cache(self, role_type).plays
    }

    pub(crate) fn get_plays_for_role_type_transitive<'a>(
        &self,
        role_type: RoleType<'a>,
    ) -> &HashMap<ObjectType<'static>, Plays<'static>> {
        &RoleType::get_cache(self, role_type).plays_transitive
    }

    pub(crate) fn get_plays<'a, 'this, T, CACHE>(&'this self, type_: T) -> &HashSet<Plays<'static>>
    where
        T: OwnerAPI<'a> + PlayerAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasOwnerPlayerCache + 'this,
    {
        &T::get_cache(self, type_).owner_player_cache().plays_declared
    }

    pub(crate) fn get_plays_transitive<'a, 'this, T, CACHE>(
        &'this self,
        type_: T,
    ) -> &'this HashMap<RoleType<'static>, Plays<'static>>
    where
        T: OwnerAPI<'a> + PlayerAPI<'a> + CacheGetter<CacheType = CACHE>,
        CACHE: HasOwnerPlayerCache + 'this,
    {
        &T::get_cache(self, type_).owner_player_cache().plays_transitive
    }

    pub(crate) fn get_attribute_type_value_type<'a>(&self, attribute_type: AttributeType<'a>) -> &Option<ValueType> {
        &AttributeType::get_cache(&self, attribute_type).value_type
    }

    pub(crate) fn get_owns_effective_annotations<'c>(
        &'c self,
        owns: Owns<'c>,
    ) -> &'c HashMap<OwnsAnnotation, Owns<'static>> {
        &self.owns.get(&owns).unwrap().effective_annotations
    }

    pub(crate) fn get_owns_ordering<'c>(&'c self, owns: Owns<'c>) -> Ordering {
        self.owns.get(&owns).unwrap().ordering
    }

    pub(crate) fn get_owns_override<'c>(&'c self, owns: Owns<'c>) -> &'c Option<Owns<'static>> {
        &self.owns.get(&owns).unwrap().overrides
    }

    pub(crate) fn get_plays_override<'c>(&'c self, plays: Plays<'c>) -> &'c Option<Plays<'static>> {
        &self.plays.get(&plays).unwrap().overrides
    }

    pub(crate) fn get_struct_definition_key(&self, label: &str) -> Option<DefinitionKey<'static>> {
        self.struct_definition_index_by_name.get(label).cloned()
    }

    pub(crate) fn get_struct_definition(&self, definition_key: DefinitionKey<'static>) -> &StructDefinition {
        &self.struct_definitions[definition_key.definition_id().as_uint() as usize].as_ref().unwrap().definition
    }
}

#[derive(Debug)]
pub enum TypeCacheCreateError {
    SnapshotOpen { source: ReadSnapshotOpenError },
}

impl fmt::Display for TypeCacheCreateError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SnapshotOpen { .. } => todo!(),
        }
    }
}

impl Error for TypeCacheCreateError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::SnapshotOpen { source } => Some(source),
        }
    }
}
