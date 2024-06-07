/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    borrow::{Borrow, Cow},
    collections::HashSet,
    sync::Arc,
};

use bytes::{byte_array::ByteArray, Bytes};
use encoding::{
    graph::{
        thing::{
            edge::{ThingEdgeHas, ThingEdgeHasReverse, ThingEdgeRelationIndex, ThingEdgeRolePlayer},
            property::{HAS_ORDER_PROPERTY_FACTORY, ROLE_PLAYER_ORDER_PROPERTY_FACTORY},
            vertex_attribute::{AttributeID, AttributeVertex},
            vertex_generator::ThingVertexGenerator,
            vertex_object::ObjectVertex,
        },
        type_::vertex::TypeVertexEncoding,
        Typed,
    },
    layout::prefix::Prefix,
    value::{
        boolean_bytes::BooleanBytes,
        date_time_bytes::DateTimeBytes,
        date_time_tz_bytes::DateTimeTZBytes,
        decimal_bytes::DecimalBytes,
        double_bytes::DoubleBytes,
        duration_bytes::DurationBytes,
        long_bytes::LongBytes,
        primitive_encoding::{decode_u64, encode_u64},
        string_bytes::StringBytes,
        struct_bytes::StructBytes,
        value::Value,
        value_struct::{StructIndexEntry, StructValue},
        value_type::{ValueType, ValueTypeCategory},
        ValueEncodable,
    },
    Keyable,
};
use itertools::Itertools;
use lending_iterator::LendingIterator;
use regex::Regex;
use resource::constants::{encoding::StructFieldIDUInt, snapshot::BUFFER_KEY_INLINE};
use storage::{
    key_range::KeyRange,
    key_value::StorageKey,
    snapshot::{write::Write, ReadableSnapshot, WritableSnapshot},
};

use super::{decode_role_players, encode_role_players};
use crate::{
    error::{ConceptReadError, ConceptWriteError},
    thing::{
        attribute::{Attribute, AttributeIterator, AttributeOwnerIterator, StructIndexToAttributeIterator},
        decode_attribute_ids, encode_attribute_ids,
        entity::{Entity, EntityIterator},
        object::{HasAttributeIterator, Object, ObjectAPI, ObjectIterator},
        relation::{IndexedPlayersIterator, Relation, RelationIterator, RelationRoleIterator, RolePlayerIterator},
        ThingAPI,
    },
    type_::{
        attribute_type::{AttributeType, AttributeTypeAnnotation},
        entity_type::EntityType,
        object_type::ObjectType,
        relation_type::RelationType,
        role_type::RoleType,
        type_manager::TypeManager,
        ObjectTypeAPI, OwnerAPI, TypeAPI,
    },
    ConceptStatus,
};

pub struct ThingManager {
    vertex_generator: Arc<ThingVertexGenerator>,
    type_manager: Arc<TypeManager>,
}

impl ThingManager {
    pub fn new(vertex_generator: Arc<ThingVertexGenerator>, type_manager: Arc<TypeManager>) -> Self {
        ThingManager { vertex_generator, type_manager }
    }

    pub(crate) fn type_manager(&self) -> &TypeManager {
        &self.type_manager
    }

    pub fn get_entities(&self, snapshot: &impl ReadableSnapshot) -> EntityIterator {
        let prefix = ObjectVertex::build_prefix_prefix(Prefix::VertexEntity);
        let snapshot_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::VertexEntity.fixed_width_keys()));
        EntityIterator::new(snapshot_iterator)
    }

    pub fn get_objects_in(&self, snapshot: &impl ReadableSnapshot, object_type: ObjectType<'_>) -> ObjectIterator {
        let vertex_prefix = match object_type {
            ObjectType::Entity(_) => Prefix::VertexEntity,
            ObjectType::Relation(_) => Prefix::VertexRelation,
        };
        let prefix = ObjectVertex::build_prefix_type(vertex_prefix.prefix_id(), object_type.vertex().type_id_());
        let snapshot_iterator = snapshot.iterate_range(KeyRange::new_within(prefix, vertex_prefix.fixed_width_keys()));
        ObjectIterator::new(snapshot_iterator)
    }

    pub fn get_entities_in(&self, snapshot: &impl ReadableSnapshot, entity_type: EntityType<'_>) -> EntityIterator {
        let prefix = ObjectVertex::build_prefix_type(Prefix::VertexEntity.prefix_id(), entity_type.vertex().type_id_());
        let snapshot_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::VertexEntity.fixed_width_keys()));
        EntityIterator::new(snapshot_iterator)
    }

    pub fn get_relations(&self, snapshot: &impl ReadableSnapshot) -> RelationIterator {
        let prefix = ObjectVertex::build_prefix_prefix(Prefix::VertexRelation);
        let snapshot_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::VertexRelation.fixed_width_keys()));
        RelationIterator::new(snapshot_iterator)
    }

    pub fn get_relations_in(
        &self,
        snapshot: &impl ReadableSnapshot,
        relation_type: RelationType<'_>,
    ) -> RelationIterator {
        let prefix =
            ObjectVertex::build_prefix_type(Prefix::VertexRelation.prefix_id(), relation_type.vertex().type_id_());
        let snapshot_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::VertexRelation.fixed_width_keys()));
        RelationIterator::new(snapshot_iterator)
    }

    pub(crate) fn get_relations_player<'o>(
        &self,
        snapshot: &impl ReadableSnapshot,
        player: &impl ObjectAPI<'o>,
    ) -> impl for<'a> LendingIterator<Item<'a> = Result<Relation<'a>, ConceptReadError>> {
        let prefix = ThingEdgeRolePlayer::prefix_reverse_from_player(player.vertex());
        let snapshot_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::EdgeRolePlayer.fixed_width_keys()));
        RelationRoleIterator::new(snapshot_iterator).map::<Result<Relation<'_>, _>, _>(|res| {
            let (rel, _, _) = res?;
            Ok(rel)
        })
    }

    pub(crate) fn get_relations_player_role<'o>(
        &self,
        snapshot: &impl ReadableSnapshot,
        player: &impl ObjectAPI<'o>,
        role_type: RoleType<'static>,
    ) -> impl for<'x> LendingIterator<Item<'x> = Result<Relation<'x>, ConceptReadError>> {
        let prefix = ThingEdgeRolePlayer::prefix_reverse_from_player(player.vertex());
        let snapshot_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::EdgeRolePlayer.fixed_width_keys()));
        RelationRoleIterator::new(snapshot_iterator).filter_map::<Result<Relation<'_>, _>, _>(move |item| match item {
            Ok((rel, role, _)) => (role == role_type).then_some(Ok(rel)),
            Err(error) => Some(Err(error)),
        })
    }

    pub fn get_attributes<'this, Snapshot: ReadableSnapshot>(
        &'this self,
        snapshot: &'this Snapshot,
    ) -> AttributeIterator<'_, Snapshot> {
        let start = AttributeVertex::build_prefix_prefix(Prefix::ATTRIBUTE_MIN);
        let end = AttributeVertex::build_prefix_prefix(Prefix::ATTRIBUTE_MAX);
        let attribute_iterator = snapshot.iterate_range(KeyRange::new_inclusive(start, end));

        let has_reverse_start = ThingEdgeHasReverse::prefix_from_prefix(Prefix::ATTRIBUTE_MIN);
        let has_reverse_end = ThingEdgeHasReverse::prefix_from_prefix(Prefix::ATTRIBUTE_MAX);
        let has_reverse_iterator = snapshot.iterate_range(KeyRange::new_inclusive(has_reverse_start, has_reverse_end));
        AttributeIterator::new(attribute_iterator, has_reverse_iterator, snapshot, self.type_manager())
    }

    pub fn get_attributes_in<'this>(
        &'this self,
        snapshot: &'this impl ReadableSnapshot,
        attribute_type: AttributeType<'_>,
    ) -> Result<AttributeIterator<'this, impl ReadableSnapshot>, ConceptReadError> {
        let attribute_value_type = attribute_type.get_value_type(snapshot, self.type_manager.as_ref())?;
        let Some(value_type) = attribute_value_type.as_ref() else {
            return Ok(AttributeIterator::new_empty());
        };

        let attribute_value_type_prefix = AttributeVertex::value_type_category_to_prefix_type(value_type.category());
        let prefix =
            AttributeVertex::build_prefix_type(attribute_value_type_prefix, attribute_type.vertex().type_id_());
        let attribute_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, attribute_value_type_prefix.fixed_width_keys()));

        let has_reverse_prefix =
            ThingEdgeHasReverse::prefix_from_type(attribute_value_type_prefix, attribute_type.vertex().type_id_());
        let has_reverse_iterator =
            snapshot.iterate_range(KeyRange::new_within(has_reverse_prefix, ThingEdgeHasReverse::FIXED_WIDTH_ENCODING));

        Ok(AttributeIterator::new(attribute_iterator, has_reverse_iterator, snapshot, self.type_manager()))
    }

    pub(crate) fn get_attribute_value<'a>(
        &self,
        snapshot: &impl ReadableSnapshot,
        attribute: &'a Attribute<'a>,
    ) -> Result<Value<'static>, ConceptReadError> {
        let attribute_type = attribute.type_();
        let value_type = attribute_type.get_value_type(snapshot, self.type_manager())?;
        match value_type.as_ref().unwrap() {
            ValueType::Boolean => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_boolean();
                Ok(Value::Boolean(BooleanBytes::new(attribute_id.bytes()).as_bool()))
            }
            ValueType::Long => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_long();
                Ok(Value::Long(LongBytes::new(attribute_id.bytes()).as_i64()))
            }
            ValueType::Double => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_double();
                Ok(Value::Double(DoubleBytes::new(attribute_id.bytes()).as_f64()))
            }
            ValueType::Decimal => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_decimal();
                Ok(Value::Decimal(DecimalBytes::new(attribute_id.bytes()).as_decimal()))
            }
            ValueType::DateTime => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_date_time();
                Ok(Value::DateTime(DateTimeBytes::new(attribute_id.bytes()).as_naive_date_time()))
            }
            ValueType::DateTimeTZ => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_date_time_tz();
                Ok(Value::DateTimeTZ(DateTimeTZBytes::new(attribute_id.bytes()).as_date_time()))
            }
            ValueType::Duration => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_duration();
                Ok(Value::Duration(DurationBytes::new(attribute_id.bytes()).as_duration()))
            }
            ValueType::String => {
                let attribute_id = attribute.vertex().attribute_id().unwrap_string();
                if attribute_id.is_inline() {
                    Ok(Value::String(Cow::Owned(String::from(attribute_id.get_inline_string_bytes().as_str()))))
                } else {
                    Ok(snapshot
                        .get_mapped(attribute.vertex().as_storage_key().as_reference(), |bytes| {
                            Value::String(Cow::Owned(String::from(
                                StringBytes::new(Bytes::<1>::Reference(bytes)).as_str(),
                            )))
                        })
                        .map_err(|error| ConceptReadError::SnapshotGet { source: error })?
                        .unwrap())
                }
            }
            ValueType::Struct(_) => Ok(snapshot
                .get_mapped(attribute.vertex().as_storage_key().as_reference(), |bytes| {
                    Value::Struct(Cow::Owned(StructBytes::new(Bytes::<1>::Reference(bytes)).as_struct()))
                })
                .map_err(|error| ConceptReadError::SnapshotGet { source: error })?
                .unwrap()),
        }
    }

    pub fn get_attribute_with_value(
        &self,
        snapshot: &impl ReadableSnapshot,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<Option<Attribute<'static>>, ConceptReadError> {
        let value_type = value.value_type();
        let attribute_value_type = attribute_type.get_value_type(snapshot, self.type_manager())?;
        if attribute_value_type.is_none() || attribute_value_type.as_ref().unwrap() != &value_type {
            return Ok(None);
        }

        let attribute = match value_type {
            | ValueType::Boolean
            | ValueType::Long
            | ValueType::Double
            | ValueType::Decimal
            | ValueType::DateTime
            | ValueType::DateTimeTZ
            | ValueType::Duration => {
                debug_assert!(AttributeID::is_inlineable(value.as_reference()));
                match self.get_attribute_with_value_inline(snapshot, attribute_type, value) {
                    Ok(Some(attribute)) => attribute,
                    fail => return fail,
                }
            }
            ValueType::String => {
                if AttributeID::is_inlineable(value.as_reference()) {
                    match self.get_attribute_with_value_inline(snapshot, attribute_type, value) {
                        Ok(Some(attribute)) => attribute,
                        fail => return fail,
                    }
                } else {
                    match self.vertex_generator.find_attribute_id_string_noinline(
                        attribute_type.vertex().type_id_(),
                        value.encode_string::<256>(),
                        snapshot,
                    ) {
                        Ok(Some(id)) => Attribute::new(AttributeVertex::build(
                            ValueTypeCategory::String,
                            attribute_type.vertex().type_id_(),
                            AttributeID::String(id),
                        )),
                        Ok(None) => return Ok(None),
                        Err(err) => return Err(ConceptReadError::SnapshotIterate { source: err }),
                    }
                }
            }
            ValueType::Struct(_) => {
                match self.vertex_generator.find_attribute_id_struct(
                    attribute_type.vertex().type_id_(),
                    value.encode_struct::<256>(),
                    snapshot,
                ) {
                    Ok(Some(id)) => {
                        let attribute = Attribute::new(AttributeVertex::build(
                            ValueTypeCategory::Struct,
                            attribute_type.vertex().type_id_(),
                            AttributeID::Struct(id),
                        ));
                        attribute
                    }
                    Ok(None) => return Ok(None),
                    Err(err) => return Err(ConceptReadError::SnapshotIterate { source: err }),
                }
            }
        };

        let is_independent = attribute.type_().is_independent(snapshot, self.type_manager())?;
        if is_independent || attribute.has_owners(snapshot, self) {
            Ok(Some(attribute))
        } else {
            Ok(None)
        }
    }

    fn get_attribute_with_value_inline(
        &self,
        snapshot: &impl ReadableSnapshot,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<Option<Attribute<'static>>, ConceptReadError> {
        debug_assert!(AttributeID::is_inlineable(value.as_reference()));
        let attribute_value_type = attribute_type.get_value_type(snapshot, self.type_manager())?;
        if attribute_value_type.is_none() || attribute_value_type.as_ref().unwrap() != &value.value_type() {
            return Ok(None);
        }
        let vertex = AttributeVertex::build(
            attribute_value_type.as_ref().unwrap().category(),
            attribute_type.vertex().type_id_(),
            AttributeID::build_inline(value),
        );
        snapshot
            .get_mapped(vertex.as_storage_key().as_reference(), |_| Attribute::new(vertex.clone()))
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })
    }

    pub(crate) fn has_attribute<'a>(
        &self,
        snapshot: &impl ReadableSnapshot,
        owner: &impl ObjectAPI<'a>,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<bool, ConceptReadError> {
        // TODO: check value type matches attribute value type
        let value_type = value.value_type();
        let vertex = if AttributeID::is_inlineable(value.as_reference()) {
            // don't need to do an extra lookup to get the attribute vertex - if it exists, it will have this ID
            AttributeVertex::build(
                value_type.category(),
                attribute_type.vertex().type_id_(),
                AttributeID::build_inline(value),
            )
        } else {
            // non-inline attributes require an extra lookup before checking for the has edge existence
            let attribute = self.get_attribute_with_value(snapshot, attribute_type, value)?;
            match attribute {
                Some(attribute) => attribute.into_vertex(),
                None => return Ok(false),
            }
        };

        let has = ThingEdgeHas::build(owner.vertex(), vertex);
        let has_exists = snapshot
            .get_mapped(has.into_storage_key().as_reference(), |_value| true)
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })?
            .unwrap_or(false);
        Ok(has_exists)
    }

    pub(crate) fn get_has_unordered<'a>(
        &self,
        snapshot: &impl ReadableSnapshot,
        owner: &impl ObjectAPI<'a>,
    ) -> HasAttributeIterator {
        let prefix = ThingEdgeHas::prefix_from_object(owner.vertex());
        HasAttributeIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeHas::FIXED_WIDTH_ENCODING)),
        )
    }

    pub fn get_attributes_by_struct_field<'this, 'a, Snapshot: ReadableSnapshot>(
        &'this self,
        snapshot: &'this Snapshot,
        attribute_type: AttributeType<'a>,
        path_to_field: Vec<StructFieldIDUInt>,
        value: Value<'_>,
    ) -> Result<StructIndexToAttributeIterator<'_, Snapshot>, ConceptReadError> {
        debug_assert!({
            let value_type = attribute_type.get_value_type(snapshot, &self.type_manager).unwrap().unwrap();
            value_type.category() == ValueTypeCategory::Struct
        });

        let prefix = StructIndexEntry::build_prefix_typeid_path_value(
            snapshot,
            self.vertex_generator.borrow(),
            &path_to_field,
            &value,
            &attribute_type.vertex(),
        )
        .map_err(|source| ConceptReadError::SnapshotIterate { source })?;
        let index_to_attribute_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::IndexValueToStruct.fixed_width_keys()));

        let attribute_value_type_prefix =
            AttributeVertex::value_type_category_to_prefix_type(ValueTypeCategory::Struct);

        let has_reverse_prefix =
            ThingEdgeHasReverse::prefix_from_type(attribute_value_type_prefix, attribute_type.vertex().type_id_());
        let has_reverse_iterator =
            snapshot.iterate_range(KeyRange::new_within(has_reverse_prefix, ThingEdgeHasReverse::FIXED_WIDTH_ENCODING));
        Ok(StructIndexToAttributeIterator::new(
            index_to_attribute_iterator,
            has_reverse_iterator,
            snapshot,
            &self.type_manager,
        ))
    }

    pub(crate) fn get_has_ordered<'this, 'a>(
        &'this self,
        snapshot: &'this impl ReadableSnapshot,
        owner: &impl ObjectAPI<'a>,
    ) -> HasAttributeIterator {
        let prefix = ThingEdgeHas::prefix_from_object(owner.vertex());
        HasAttributeIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeHas::FIXED_WIDTH_ENCODING)),
        )
    }

    pub(crate) fn get_has_type_unordered<'this, 'a>(
        &'this self,
        snapshot: &'this impl ReadableSnapshot,
        owner: &impl ObjectAPI<'a>,
        attribute_type: AttributeType<'static>,
    ) -> Result<HasAttributeIterator, ConceptReadError> {
        let attribute_value_type = attribute_type.get_value_type(snapshot, self.type_manager())?;
        let value_type = match attribute_value_type.as_ref() {
            None => {
                todo!("Handle missing value type - for abstract attributes. Or assume this will never happen")
            }
            Some(value_type) => value_type,
        };
        let prefix = ThingEdgeHas::prefix_from_object_to_type(
            owner.vertex(),
            value_type.category(),
            attribute_type.into_vertex(),
        );
        Ok(HasAttributeIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeHas::FIXED_WIDTH_ENCODING)),
        ))
    }

    pub(crate) fn get_has_type_ordered<'a>(
        &self,
        snapshot: &impl ReadableSnapshot,
        owner: &impl ObjectAPI<'a>,
        attribute_type: AttributeType<'static>,
    ) -> Result<Vec<Attribute<'static>>, ConceptReadError> {
        let key = HAS_ORDER_PROPERTY_FACTORY.build(owner.vertex(), attribute_type.vertex());
        let attribute_value_type = attribute_type.get_value_type(snapshot, self.type_manager())?;
        let value_type = match attribute_value_type.as_ref() {
            None => {
                todo!("Handle missing value type - for abstract attributes. Or assume this will never happen")
            }
            Some(value_type) => value_type,
        };
        let attributes = snapshot
            .get_mapped(key.as_storage_key().as_reference(), |bytes| {
                decode_attribute_ids(value_type.category(), bytes.bytes())
                    .map(|id| {
                        Attribute::new(AttributeVertex::build(
                            value_type.category(),
                            attribute_type.vertex().type_id_(),
                            id,
                        ))
                    })
                    .collect()
            })
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })?
            .unwrap_or_else(Vec::new);
        Ok(attributes)
    }

    pub(crate) fn get_owners<'this>(
        &'this self,
        snapshot: &'this impl ReadableSnapshot,
        attribute: Attribute<'_>,
    ) -> AttributeOwnerIterator {
        let prefix = ThingEdgeHasReverse::prefix_from_attribute(attribute.into_vertex());
        AttributeOwnerIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeHasReverse::FIXED_WIDTH_ENCODING)),
        )
    }

    pub(crate) fn get_owners_by_type<'this, 'a>(
        &'this self,
        snapshot: &'this impl ReadableSnapshot,
        attribute: Attribute<'_>,
        owner_type: impl ObjectTypeAPI<'a>,
    ) -> AttributeOwnerIterator {
        let prefix = ThingEdgeHasReverse::prefix_from_attribute_to_type(attribute.into_vertex(), owner_type.vertex());
        AttributeOwnerIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeHasReverse::FIXED_WIDTH_ENCODING)),
        )
    }

    pub(crate) fn has_owners(
        &self,
        snapshot: &impl ReadableSnapshot,
        attribute: Attribute<'_>,
        buffered_only: bool,
    ) -> bool {
        let prefix = ThingEdgeHasReverse::prefix_from_attribute(attribute.into_vertex());
        snapshot.any_in_range(KeyRange::new_within(prefix, ThingEdgeHasReverse::FIXED_WIDTH_ENCODING), buffered_only)
    }

    pub(crate) fn get_relations_roles<'this, 'a>(
        &'this self,
        snapshot: &'this impl ReadableSnapshot,
        player: impl ObjectAPI<'a>,
    ) -> RelationRoleIterator {
        let prefix = ThingEdgeRolePlayer::prefix_reverse_from_player(player.into_vertex());
        RelationRoleIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeRolePlayer::FIXED_WIDTH_ENCODING)),
        )
    }

    pub(crate) fn has_role_players(
        &self,
        snapshot: &impl ReadableSnapshot,
        relation: Relation<'_>,
        buffered_only: bool, // FIXME use enums
    ) -> bool {
        let prefix = ThingEdgeRolePlayer::prefix_from_relation(relation.into_vertex());
        snapshot.any_in_range(KeyRange::new_within(prefix, ThingEdgeRolePlayer::FIXED_WIDTH_ENCODING), buffered_only)
    }

    pub(crate) fn get_role_players(
        &self,
        snapshot: &impl ReadableSnapshot,
        relation: Relation<'_>,
    ) -> RolePlayerIterator {
        let prefix = ThingEdgeRolePlayer::prefix_from_relation(relation.into_vertex());
        RolePlayerIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeRolePlayer::FIXED_WIDTH_ENCODING)),
        )
    }

    pub(crate) fn get_role_players_ordered(
        &self,
        snapshot: &impl ReadableSnapshot,
        relation: Relation<'_>,
        role_type: RoleType<'static>,
    ) -> Result<Vec<Object<'static>>, ConceptReadError> {
        let key = ROLE_PLAYER_ORDER_PROPERTY_FACTORY.build(relation.into_vertex(), role_type.into_vertex());
        let players = snapshot
            .get_mapped(key.as_storage_key().as_reference(), |bytes| {
                decode_role_players(bytes.bytes()).map(|vertex| Object::new(vertex).into_owned()).collect()
            })
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })?
            .unwrap_or_else(Vec::new);
        Ok(players)
    }

    pub(crate) fn get_indexed_players<'a>(
        &'a self,
        snapshot: &'a impl ReadableSnapshot,
        from: Object<'_>,
    ) -> IndexedPlayersIterator {
        let prefix = ThingEdgeRelationIndex::prefix_from(from.vertex());
        IndexedPlayersIterator::new(
            snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeRelationIndex::FIXED_WIDTH_ENCODING)),
        )
    }

    pub(crate) fn get_status(
        &self,
        snapshot: &impl ReadableSnapshot,
        key: StorageKey<'_, BUFFER_KEY_INLINE>,
    ) -> ConceptStatus {
        snapshot
            .get_buffered_write(key.as_reference())
            .map(|write| match write {
                Write::Insert { .. } => ConceptStatus::Inserted,
                Write::Put { .. } => ConceptStatus::Put,
                Write::Delete => ConceptStatus::Deleted,
            })
            .unwrap_or_else(|| {
                debug_assert!(
                    snapshot.get::<BUFFER_KEY_INLINE>(key.as_reference()).unwrap().is_some(),
                    "Attempting to get write status of a key that was not written to in this transaction: {key:?}",
                );
                ConceptStatus::Persisted
            })
    }

    pub(crate) fn object_exists<'a>(
        &self,
        snapshot: &impl ReadableSnapshot,
        object: &impl ObjectAPI<'a>,
    ) -> Result<bool, ConceptReadError> {
        match snapshot.get::<0>(object.vertex().as_storage_key().as_reference()) {
            Ok(value) => Ok(value.is_some()),
            Err(error) => Err(ConceptReadError::SnapshotGet { source: error }),
        }
    }
}

impl<'txn> ThingManager {
    pub(crate) fn lock_existing<'a>(&self, snapshot: &mut impl WritableSnapshot, object: impl ObjectAPI<'a>) {
        snapshot.unmodifiable_lock_add(object.into_vertex().as_storage_key().into_owned_array())
    }

    // TODO we should differentiate "validation errors" and "an error occurred during validation"
    pub fn finalise(&self, snapshot: &mut impl WritableSnapshot) -> Result<(), Vec<ConceptWriteError>> {
        self.cleanup_relations(snapshot).map_err(|err| vec![err])?;
        self.cleanup_attributes(snapshot).map_err(|err| vec![err])?;
        let thing_errors = self.thing_errors(snapshot);
        match thing_errors {
            Ok(errors) if errors.is_empty() => Ok(()),
            Ok(errors) => Err(errors),
            Err(error) => Err(vec![ConceptWriteError::ConceptRead { source: error }]),
        }
    }

    fn cleanup_relations(&self, snapshot: &mut impl WritableSnapshot) -> Result<(), ConceptWriteError> {
        let mut any_deleted = true;
        while any_deleted {
            any_deleted = false;
            for (key, _) in snapshot
                .iterate_buffered_writes_range(KeyRange::new_within(
                    ThingEdgeRolePlayer::prefix(),
                    ThingEdgeRolePlayer::FIXED_WIDTH_ENCODING,
                ))
                .filter(|(_, write)| matches!(write, Write::Delete))
            {
                let edge = ThingEdgeRolePlayer::new(Bytes::Reference(key.byte_array().as_ref()));
                let relation = Relation::new(edge.from());
                if relation.get_status(snapshot, self) == ConceptStatus::Deleted {
                    continue;
                }
                if !relation.has_players(snapshot, self) {
                    relation.delete(snapshot, self)?;
                    any_deleted = true;
                }
            }
        }

        let mut any_deleted = true;
        while any_deleted {
            any_deleted = false;
            for key in snapshot
                .iterate_buffered_writes_range(KeyRange::new_within(
                    ObjectVertex::build_prefix_prefix(Prefix::VertexRelation),
                    ObjectVertex::FIXED_WIDTH_ENCODING,
                ))
                .filter_map(|(key, write)| (!matches!(write, Write::Delete)).then_some(key))
            {
                let relation = Relation::new(ObjectVertex::new(Bytes::reference(key.bytes())));
                if !relation.has_players(snapshot, self) {
                    relation.delete(snapshot, self)?;
                    any_deleted = true;
                }
            }
        }

        Ok(())
    }

    fn cleanup_attributes(&self, snapshot: &mut impl WritableSnapshot) -> Result<(), ConceptWriteError> {
        for (key, _write) in snapshot
            .iterate_buffered_writes_range(KeyRange::new_within(
                ThingEdgeHas::prefix(),
                ThingEdgeHas::FIXED_WIDTH_ENCODING,
            ))
            .filter(|(_, write)| matches!(write, Write::Delete))
        {
            let edge = ThingEdgeHas::new(Bytes::Reference(key.byte_array().as_ref()));
            let attribute = Attribute::new(edge.to());
            let is_independent = attribute
                .type_()
                .is_independent(snapshot, self.type_manager())
                .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
            if attribute.get_status(snapshot, self) == ConceptStatus::Deleted {
                continue;
            }
            if !is_independent && !attribute.has_owners(snapshot, self) {
                attribute.delete(snapshot, self)?;
            }
        }

        for (key, _value) in snapshot
            .iterate_writes_range(KeyRange::new_exclusive(
                Bytes::inline(Prefix::ATTRIBUTE_MIN.prefix_id().bytes(), 1),
                Bytes::inline(Prefix::ATTRIBUTE_MAX.prefix_id().bytes(), 1),
            ))
            .filter_map(|(key, write)| match write {
                Write::Put { value, .. } => Some((key, value)),
                _ => None,
            })
            .collect_vec()
            .into_iter()
        {
            let attribute = Attribute::new(AttributeVertex::new(Bytes::reference(key.bytes())));
            let is_independent = attribute
                .type_()
                .is_independent(snapshot, self.type_manager())
                .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
            if !is_independent && !attribute.has_owners(snapshot, self) {
                self.unput_attribute(snapshot, attribute)?;
            }
        }

        Ok(())
    }

    fn thing_errors(&self, snapshot: &mut impl WritableSnapshot) -> Result<Vec<ConceptWriteError>, ConceptReadError> {
        let mut errors = Vec::new();

        self.validate_ownerships(&mut errors, snapshot)?;

        let mut relations_validated = HashSet::new();
        for (key, _) in snapshot
            .iterate_buffered_writes_range(KeyRange::new_within(
                ThingEdgeRolePlayer::prefix(),
                ThingEdgeRolePlayer::FIXED_WIDTH_ENCODING,
            ))
            .filter(|(_, write)| !matches!(write, Write::Delete))
        {
            let edge = ThingEdgeRolePlayer::new(Bytes::reference(key.bytes()));
            let relation = Relation::new(edge.from());
            if !relations_validated.contains(&relation) {
                errors.extend(relation.errors(snapshot, self)?);
                relations_validated.insert(relation.into_owned());
            }
        }

        Ok(errors)
    }

    fn validate_ownerships(
        &self,
        errors: &mut Vec<ConceptWriteError>,
        snapshot: &impl WritableSnapshot,
    ) -> Result<(), ConceptReadError> {
        for (key, _) in snapshot.iterate_buffered_writes_range(KeyRange::new_within(
            ThingEdgeHas::prefix(),
            ThingEdgeHas::FIXED_WIDTH_ENCODING,
        )) {
            let edge = ThingEdgeHas::new(Bytes::Reference(key.byte_array().as_ref()));
            let owner = Object::new(edge.from());
            if !self.object_exists(snapshot, &owner)? {
                continue;
            }
            let attribute = Attribute::new(edge.to());
            self.validate_owner(owner, attribute.type_(), snapshot, errors)?;
        }

        for key in snapshot
            .iterate_writes_range(KeyRange::new_inclusive(
                Bytes::<0>::reference(ObjectVertex::build_prefix_prefix(Prefix::VertexEntity).bytes()),
                Bytes::<0>::reference(ObjectVertex::build_prefix_prefix(Prefix::VertexRelation).bytes()),
            ))
            .filter_map(|(key, write)| match write {
                Write::Insert { .. } => Some(key),
                Write::Delete => None,
                Write::Put { .. } => unreachable!("Encountered a Put for an entity"),
            })
        {
            let owner = Object::new(ObjectVertex::new(Bytes::reference(key.bytes())));
            let owner_type = owner.type_();
            for owns in &owner_type.get_owns(snapshot, self.type_manager())? {
                if owns.is_key(snapshot, &*self.type_manager)? {
                    self.validate_owner(owner.as_reference(), owns.attribute(), snapshot, errors)?;
                }
            }
        }

        Ok(())
    }

    fn validate_owner(
        &self,
        owner: Object<'_>,
        attribute_type: AttributeType<'static>,
        snapshot: &impl WritableSnapshot,
        errors: &mut Vec<ConceptWriteError>,
    ) -> Result<(), ConceptReadError> {
        let owner_type = owner.type_();
        let owns = owner_type
            .get_owns_attribute(snapshot, self.type_manager(), attribute_type.clone())?
            .expect("encountered a has edge without a corresponding owns in the schema");

        if let Some(cardinality) = owns.get_cardinality(snapshot, self.type_manager())? {
            let count = owner.get_has_type(snapshot, self, attribute_type.clone())?.count();
            if !cardinality.is_valid(count as u64) {
                if owns.is_key(snapshot, &*self.type_manager)? {
                    if count == 0 {
                        errors
                            .push(ConceptWriteError::KeyMissing { owner: owner.into_owned(), key_type: attribute_type })
                    } else {
                        errors.push(ConceptWriteError::MultipleKeys {
                            owner: owner.into_owned(),
                            key_type: attribute_type,
                        })
                    }
                } else {
                    errors.push(ConceptWriteError::CardinalityViolation {
                        owner: owner.into_owned(),
                        attribute_type,
                        cardinality,
                    })
                }
            }
        };
        Ok(())
    }

    pub fn create_entity<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        entity_type: EntityType<'static>,
    ) -> Result<Entity<'a>, ConceptWriteError> {
        Ok(Entity::new(self.vertex_generator.create_entity(entity_type.vertex().type_id_(), snapshot)))
    }

    pub fn create_relation<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation_type: RelationType<'static>,
    ) -> Result<Relation<'a>, ConceptWriteError> {
        Ok(Relation::new(self.vertex_generator.create_relation(relation_type.vertex().type_id_(), snapshot)))
    }

    pub fn create_attribute<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<Attribute<'a>, ConceptWriteError> {
        self.put_attribute(snapshot, attribute_type, value)
    }

    pub(crate) fn put_attribute<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<Attribute<'a>, ConceptWriteError> {
        let value_type = attribute_type.get_value_type(snapshot, self.type_manager.as_ref())?;
        if Some(&value.value_type()) == value_type.as_ref() {
            let vertex = match value {
                Value::Boolean(bool) => {
                    let encoded_boolean = BooleanBytes::build(bool);
                    self.vertex_generator.create_attribute_boolean(
                        attribute_type.vertex().type_id_(),
                        encoded_boolean,
                        snapshot,
                    )
                }
                Value::Long(long) => {
                    let encoded_long = LongBytes::build(long);
                    self.vertex_generator.create_attribute_long(
                        attribute_type.vertex().type_id_(),
                        encoded_long,
                        snapshot,
                    )
                }
                Value::Double(double) => {
                    let encoded_double = DoubleBytes::build(double);
                    self.vertex_generator.create_attribute_double(
                        attribute_type.vertex().type_id_(),
                        encoded_double,
                        snapshot,
                    )
                }
                Value::Decimal(decimal) => {
                    let encoded_decimal = DecimalBytes::build(decimal);
                    self.vertex_generator.create_attribute_decimal(
                        attribute_type.vertex().type_id_(),
                        encoded_decimal,
                        snapshot,
                    )
                }
                Value::DateTime(date_time) => {
                    let encoded_date_time = DateTimeBytes::build(date_time);
                    self.vertex_generator.create_attribute_date_time(
                        attribute_type.vertex().type_id_(),
                        encoded_date_time,
                        snapshot,
                    )
                }
                Value::DateTimeTZ(date_time_tz) => {
                    let encoded_date_time_tz = DateTimeTZBytes::build(date_time_tz);
                    self.vertex_generator.create_attribute_date_time_tz(
                        attribute_type.vertex().type_id_(),
                        encoded_date_time_tz,
                        snapshot,
                    )
                }
                Value::Duration(duration) => {
                    let encoded_duration = DurationBytes::build(duration);
                    self.vertex_generator.create_attribute_duration(
                        attribute_type.vertex().type_id_(),
                        encoded_duration,
                        snapshot,
                    )
                }
                Value::String(string) => {
                    let annotations =
                        self.type_manager.get_attribute_type_annotations(snapshot, attribute_type.clone())?;
                    for annotation in annotations.iter() {
                        match annotation {
                            AttributeTypeAnnotation::Abstract(_) => todo!("create abstract attribute"),
                            AttributeTypeAnnotation::Independent(_) => (),
                            AttributeTypeAnnotation::Regex(regex) => {
                                let regex = regex.regex();
                                if !Regex::new(regex).unwrap().is_match(&string) {
                                    return Err(ConceptWriteError::StringAttributeRegex {
                                        regex: regex.to_owned(),
                                        value: string.into_owned(),
                                    });
                                }
                            }
                        }
                    }
                    let encoded_string: StringBytes<'_, BUFFER_KEY_INLINE> = StringBytes::build_ref(&string);
                    self.vertex_generator
                        .create_attribute_string(attribute_type.vertex().type_id_(), encoded_string, snapshot)
                        .map_err(|err| ConceptWriteError::SnapshotIterate { source: err })?
                }
                Value::Struct(struct_) => {
                    let encoded_struct: StructBytes<'static, BUFFER_KEY_INLINE> = StructBytes::build(&struct_);
                    let struct_attribute = self
                        .vertex_generator
                        .create_attribute_struct(attribute_type.vertex().type_id_(), encoded_struct, snapshot)
                        .map_err(|err| ConceptWriteError::SnapshotIterate { source: err })?;
                    self.index_struct_fields(snapshot, &struct_attribute, &struct_)?;
                    struct_attribute
                }
            };
            Ok(Attribute::new(vertex))
        } else {
            Err(ConceptWriteError::ValueTypeMismatch {
                expected: value_type.as_ref().cloned(),
                provided: value.value_type(),
            })
        }
    }

    fn index_struct_fields<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        attribute_vertex: &AttributeVertex<'static>,
        struct_value: &StructValue<'a>,
    ) -> Result<(), ConceptWriteError> {
        let index_entries = struct_value
            .create_index_entries(snapshot, self.vertex_generator.borrow(), &attribute_vertex)
            .map_err(|err| ConceptWriteError::SnapshotIterate { source: err })?;
        for entry in index_entries {
            let StructIndexEntry { key, value } = entry;
            match value {
                None => snapshot.put(key.into_storage_key().into_owned_array()),
                Some(value) => snapshot.put_val(key.into_storage_key().into_owned_array(), value.into_array()),
            }
        }
        Ok(())
    }

    pub(crate) fn delete_entity(&self, snapshot: &mut impl WritableSnapshot, entity: Entity<'_>) {
        let key = entity.into_vertex().into_storage_key().into_owned_array();
        snapshot.unmodifiable_lock_remove(&key);
        snapshot.delete(key)
    }

    pub(crate) fn delete_relation(&self, snapshot: &mut impl WritableSnapshot, relation: Relation<'_>) {
        let key = relation.into_vertex().into_storage_key().into_owned_array();
        snapshot.unmodifiable_lock_remove(&key);
        snapshot.delete(key)
    }

    pub(crate) fn delete_attribute(
        &self,
        snapshot: &mut impl WritableSnapshot,
        attribute: Attribute<'_>,
    ) -> Result<(), ConceptWriteError> {
        let key = attribute.into_vertex().into_storage_key().into_owned_array();
        snapshot.delete(key);
        Ok(())
    }

    pub(crate) fn uninsert_entity(&self, snapshot: &mut impl WritableSnapshot, entity: Entity<'_>) {
        let key = entity.into_vertex().into_storage_key().into_owned_array();
        snapshot.unmodifiable_lock_remove(&key);
        snapshot.uninsert(key)
    }

    pub(crate) fn uninsert_relation(&self, snapshot: &mut impl WritableSnapshot, relation: Relation<'_>) {
        let key = relation.into_vertex().into_storage_key().into_owned_array();
        snapshot.unmodifiable_lock_remove(&key);
        snapshot.uninsert(key)
    }

    pub(crate) fn unput_attribute(
        &self,
        snapshot: &mut impl WritableSnapshot,
        mut attribute: Attribute<'_>,
    ) -> Result<(), ConceptWriteError> {
        let value = match attribute
            .get_value(snapshot, self)
            .map_err(|error| ConceptWriteError::ConceptRead { source: error })?
        {
            Value::String(string) => ByteArray::copy(string.as_bytes()),
            _ => ByteArray::empty(),
        };
        let key = attribute.into_vertex().into_storage_key().into_owned_array();
        snapshot.unput_val(key, value);
        Ok(())
    }

    pub(crate) fn set_has_unordered<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        owner: &impl ObjectAPI<'a>,
        mut attribute: Attribute<'_>,
    ) {
        self.set_has_count(snapshot, owner, attribute, 1)
    }

    pub(crate) fn set_has_count<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        owner: &impl ObjectAPI<'a>,
        mut attribute: Attribute<'_>,
        count: u64,
    ) {
        let attribute_type = attribute.type_();
        let value = match attribute.get_value(snapshot, self) {
            Ok(value) => value,
            // When setting attribute ownership, either the attribute was just created, or it was
            // fetched from the storage by key, so a non-inlined value may be missing.
            // There should be no way for outside code to get an instance of an `Attribute` without
            // going through one of the above code paths, so `get_value()` better succeed.
            Err(error) => panic!("Error encountered when attempting to insert ownership for an attribute: {error:?}"),
        };
        // TODO: handle duplicates
        // note: we always re-put the attribute. TODO: optimise knowing when the attribute pre-exists.
        self.put_attribute(snapshot, attribute_type, value).unwrap();
        owner.set_modified(snapshot, self);
        let has = ThingEdgeHas::build(owner.vertex(), attribute.vertex());
        snapshot.put_val(has.into_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(count)));
        let has_reverse = ThingEdgeHasReverse::build(attribute.into_vertex(), owner.vertex());
        snapshot.put_val(has_reverse.into_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(count)));
    }

    pub(crate) fn unset_has<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        owner: &impl ObjectAPI<'a>,
        attribute: Attribute<'_>,
    ) {
        owner.set_modified(snapshot, self);
        let owner_status = owner.get_status(snapshot, self);
        let has = ThingEdgeHas::build(owner.vertex(), attribute.vertex()).into_storage_key().into_owned_array();
        let has_reverse =
            ThingEdgeHasReverse::build(attribute.into_vertex(), owner.vertex()).into_storage_key().into_owned_array();
        match owner_status {
            ConceptStatus::Inserted => {
                let count = 1;
                snapshot.unput_val(has, ByteArray::copy(&encode_u64(count)));
                snapshot.unput_val(has_reverse, ByteArray::copy(&encode_u64(count)));
            }
            ConceptStatus::Persisted => {
                snapshot.delete(has);
                snapshot.delete(has_reverse);
            }
            ConceptStatus::Put => unreachable!("Encountered a `put` attribute owner: {owner:?}."),
            ConceptStatus::Deleted => unreachable!("Attempting to unset attribute ownership on a deleted owner."),
        }
    }

    pub(crate) fn set_has_ordered<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        owner: &impl ObjectAPI<'a>,
        attribute_type: AttributeType<'static>,
        attributes: Vec<Attribute<'_>>,
    ) -> Result<(), ConceptWriteError> {
        owner.set_modified(snapshot, self);
        let attribute_value_type = attribute_type
            .get_value_type(snapshot, self.type_manager())?
            .expect("Handle missing value type - for abstract attributes. Or assume this will never happen");
        let key = HAS_ORDER_PROPERTY_FACTORY.build(owner.vertex(), attribute_type.into_vertex());
        let value = encode_attribute_ids(
            attribute_value_type.category(),
            attributes.into_iter().map(|attr| attr.into_vertex().attribute_id()),
        );
        snapshot.put_val(key.into_storage_key().into_owned_array(), value);
        Ok(())
    }

    pub(crate) fn unset_has_ordered<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        owner: &impl ObjectAPI<'a>,
        attribute_type: AttributeType<'static>,
    ) {
        owner.set_modified(snapshot, self);
        let order_property = HAS_ORDER_PROPERTY_FACTORY.build(owner.vertex(), attribute_type.into_vertex());
        snapshot.delete(order_property.into_storage_key().into_owned_array())
    }

    pub(crate) fn put_role_player_unordered<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        player: impl ObjectAPI<'a>,
        role_type: RoleType<'_>,
    ) -> Result<(), ConceptWriteError> {
        let count: u64 = 1;
        // must be idempotent, so no lock required -- cannot fail

        let role_player =
            ThingEdgeRolePlayer::build_role_player(relation.vertex(), player.vertex(), role_type.clone().into_vertex());
        snapshot.put_val(role_player.into_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(count)));

        let role_player_reverse = ThingEdgeRolePlayer::build_role_player_reverse(
            player.clone().into_vertex(),
            relation.clone().into_vertex(),
            role_type.clone().into_vertex(),
        );
        snapshot
            .put_val(role_player_reverse.into_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(count)));

        if self
            .type_manager
            .relation_index_available(snapshot, relation.type_())
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
        {
            self.relation_index_player_regenerate(snapshot, relation, Object::new(player.vertex()), role_type, 1)?;
        }
        Ok(())
    }

    pub(crate) fn set_role_players_ordered<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        role_type: RoleType<'static>,
        players: Vec<Object<'_>>,
    ) -> Result<(), ConceptWriteError> {
        relation.set_modified(snapshot, self);
        let key = ROLE_PLAYER_ORDER_PROPERTY_FACTORY.build(relation.into_vertex(), role_type.into_vertex());
        let value = encode_role_players(players.into_iter().map(|player| player.into_vertex()));
        snapshot.put_val(key.into_storage_key().into_owned_array(), value);
        Ok(())
    }

    pub(crate) fn set_role_player_count<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        player: impl ObjectAPI<'a>,
        role_type: RoleType<'_>,
        count: u64,
    ) -> Result<(), ConceptWriteError> {
        let role_player =
            ThingEdgeRolePlayer::build_role_player(relation.vertex(), player.vertex(), role_type.clone().into_vertex());
        let role_player_reverse = ThingEdgeRolePlayer::build_role_player_reverse(
            player.vertex(),
            relation.vertex(),
            role_type.clone().into_vertex(),
        );

        if count == 0 {
            snapshot.delete(role_player.as_storage_key().into_owned_array());
            snapshot.delete(role_player_reverse.as_storage_key().into_owned_array());
        } else {
            snapshot.put_val(role_player.as_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(count)));
            snapshot
                .put_val(role_player_reverse.as_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(count)));

            if self
                .type_manager
                .relation_index_available(snapshot, relation.type_())
                .map_err(|err| ConceptWriteError::ConceptRead { source: err })?
            {
                let player = Object::new(player.vertex());
                self.relation_index_player_regenerate(snapshot, relation, player, role_type, count)?
            }
        }

        // must lock to fail concurrent transactions updating the same counters
        snapshot.exclusive_lock_add(role_player.into_storage_key().into_owned_array().into_byte_array());

        Ok(())
    }

    /// Delete all counts of the specific role player in a given relation, and update indexes if required
    pub fn unset_role_player<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        player: impl ObjectAPI<'a>,
        role_type: RoleType<'_>,
    ) -> Result<(), ConceptWriteError> {
        let role_player =
            ThingEdgeRolePlayer::build_role_player(relation.vertex(), player.vertex(), role_type.clone().into_vertex())
                .into_storage_key()
                .into_owned_array();

        let role_player_reverse =
            ThingEdgeRolePlayer::build_role_player_reverse(player.vertex(), relation.vertex(), role_type.vertex())
                .into_storage_key()
                .into_owned_array();

        let owner_status = relation.get_status(&*snapshot, self);

        match owner_status {
            ConceptStatus::Inserted => {
                let count = 1;
                snapshot.unput_val(role_player, ByteArray::copy(&encode_u64(count)));
                snapshot.unput_val(role_player_reverse, ByteArray::copy(&encode_u64(count)));
            }
            ConceptStatus::Persisted => {
                snapshot.delete(role_player);
                snapshot.delete(role_player_reverse);
            }
            ConceptStatus::Put => unreachable!("Encountered a `put` relation: {relation:?}."),
            ConceptStatus::Deleted => unreachable!("Attempting to unset attribute ownership on a deleted owner."),
        }

        if self
            .type_manager
            .relation_index_available(snapshot, relation.type_())
            .map_err(|error| ConceptWriteError::ConceptRead { source: error })?
        {
            self.relation_index_player_deleted(snapshot, relation, player, role_type)?;
        }
        Ok(())
    }

    /// Add a player to a relation that supports duplicates
    /// Caller must provide a lock that prevents race conditions on the player counts on the relation
    pub(crate) fn increment_role_player<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        player: impl ObjectAPI<'a>,
        role_type: RoleType<'_>,
    ) -> Result<(), ConceptWriteError> {
        let role_player =
            ThingEdgeRolePlayer::build_role_player(relation.vertex(), player.vertex(), role_type.clone().into_vertex());
        let rp_count = snapshot
            .get_mapped(role_player.as_storage_key().as_reference(), |arr| decode_u64(arr.bytes().try_into().unwrap()))
            .unwrap();

        #[cfg(debug_assertions)]
        {
            let role_player_reverse = ThingEdgeRolePlayer::build_role_player_reverse(
                player.vertex(),
                relation.vertex(),
                role_type.clone().into_vertex(),
            );
            let rp_reverse_count = snapshot
                .get_mapped(role_player_reverse.as_storage_key().as_reference(), |arr| {
                    decode_u64(arr.bytes().try_into().unwrap())
                })
                .unwrap();
            debug_assert_eq!(&rp_count, &rp_reverse_count, "roleplayer count mismatch!");
        }

        self.set_role_player_count(snapshot, relation, player, role_type, rp_count.unwrap_or(0) + 1)
    }

    /// Remove a player from a relation that supports duplicates
    /// Caller must provide a lock that prevents race conditions on the player counts on the relation
    pub(crate) fn decrement_role_player<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        player: impl ObjectAPI<'a>,
        role_type: RoleType<'_>,
        decrement_count: u64,
    ) -> Result<(), ConceptWriteError> {
        let role_player =
            ThingEdgeRolePlayer::build_role_player(relation.vertex(), player.vertex(), role_type.clone().into_vertex());
        let rp_count = snapshot
            .get_mapped(role_player.as_storage_key().as_reference(), |arr| decode_u64(arr.bytes().try_into().unwrap()))
            .unwrap();

        #[cfg(debug_assertions)]
        {
            let role_player_reverse = ThingEdgeRolePlayer::build_role_player_reverse(
                player.vertex(),
                relation.vertex(),
                role_type.clone().into_vertex(),
            );
            let rp_reverse_count = snapshot
                .get_mapped(role_player_reverse.as_storage_key().as_reference(), |arr| {
                    decode_u64(arr.bytes().try_into().unwrap())
                })
                .unwrap();
            debug_assert_eq!(&rp_count, &rp_reverse_count, "roleplayer count mismatch!");
        }

        self.set_role_player_count(snapshot, relation, player, role_type, rp_count.unwrap_or(0) - 1)
    }

    ///
    /// Clean up all parts of a relation index to do with a specific role player
    /// after the player has been deleted.
    ///
    pub(crate) fn relation_index_player_deleted<'a>(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        player: impl ObjectAPI<'a>,
        role_type: RoleType<'_>,
    ) -> Result<(), ConceptWriteError> {
        let players = relation
            .get_players(snapshot, self)
            .map_static(|item| {
                let (roleplayer, _count) = item?;
                Ok((roleplayer.player().into_owned(), roleplayer.role_type()))
            })
            .try_collect::<Vec<_>, _>()
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        for (rp_player, rp_role_type) in players {
            debug_assert!(!(rp_player == Object::new(rp_player.vertex()) && role_type == rp_role_type));
            let index = ThingEdgeRelationIndex::build(
                player.vertex(),
                rp_player.vertex(),
                relation.vertex(),
                role_type.vertex().type_id_(),
                rp_role_type.vertex().type_id_(),
            );
            snapshot.delete(index.as_storage_key().into_owned_array());
            let index_reverse = ThingEdgeRelationIndex::build(
                rp_player.vertex(),
                player.vertex(),
                relation.vertex(),
                rp_role_type.vertex().type_id_(),
                role_type.vertex().type_id_(),
            );
            snapshot.delete(index_reverse.as_storage_key().into_owned_array());
        }
        Ok(())
    }

    /// For N duplicate role players, the self-edges are available N-1 times.
    /// For N duplicate player 1, and M duplicate player 2 - from N to M has M index repetitions,
    /// while M to N has N index repetitions.
    pub(crate) fn relation_index_player_regenerate(
        &self,
        snapshot: &mut impl WritableSnapshot,
        relation: Relation<'_>,
        player: Object<'_>,
        role_type: RoleType<'_>,
        count_for_player: u64,
    ) -> Result<(), ConceptWriteError> {
        debug_assert_ne!(count_for_player, 0);
        let players = relation
            .get_players(snapshot, self)
            .map_static(|item| {
                let (roleplayer, count) = item?;
                Ok((roleplayer.player().into_owned(), roleplayer.role_type(), count))
            })
            .try_collect::<Vec<_>, _>()
            .map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        for (rp_player, rp_role_type, rp_count) in players {
            let is_same_rp = rp_player == player && rp_role_type == role_type;
            if is_same_rp {
                let repetitions = count_for_player - 1;
                if repetitions > 0 {
                    let index = ThingEdgeRelationIndex::build(
                        player.vertex(),
                        player.vertex(),
                        relation.vertex(),
                        role_type.vertex().type_id_(),
                        role_type.vertex().type_id_(),
                    );
                    snapshot
                        .put_val(index.as_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(repetitions)));
                }
            } else {
                let rp_repetitions = rp_count;
                let index = ThingEdgeRelationIndex::build(
                    player.vertex(),
                    rp_player.vertex(),
                    relation.vertex(),
                    role_type.vertex().type_id_(),
                    rp_role_type.vertex().type_id_(),
                );
                snapshot
                    .put_val(index.as_storage_key().into_owned_array(), ByteArray::copy(&encode_u64(rp_repetitions)));
                let player_repetitions = count_for_player;
                let index_reverse = ThingEdgeRelationIndex::build(
                    rp_player.vertex(),
                    player.vertex(),
                    relation.vertex(),
                    rp_role_type.vertex().type_id_(),
                    role_type.vertex().type_id_(),
                );
                snapshot.put_val(
                    index_reverse.as_storage_key().into_owned_array(),
                    ByteArray::copy(&encode_u64(player_repetitions)),
                );
            }
        }
        Ok(())
    }
}
