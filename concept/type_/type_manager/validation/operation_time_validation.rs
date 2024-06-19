/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashMap;

use encoding::{
    graph::{
        thing::{edge::ThingEdgeRolePlayer, vertex_object::ObjectVertex},
        type_::vertex::TypeVertexEncoding,
        Typed,
    },
    layout::prefix::Prefix,
    value::{label::Label, value_type::ValueType},
};
use lending_iterator::LendingIterator;
use storage::{key_range::KeyRange, snapshot::ReadableSnapshot};

use crate::{
    thing::{
        object::ObjectAPI,
        relation::{RelationIterator, RolePlayerIterator},
        thing_manager::ThingManager,
    },
    type_::{
        annotation::{Annotation, AnnotationAbstract},
        attribute_type::AttributeType,
        entity_type::EntityType,
        object_type::ObjectType,
        owns::Owns,
        plays::Plays,
        relation_type::RelationType,
        role_type::RoleType,
        type_manager::{type_reader::TypeReader, validation::SchemaValidationError},
        KindAPI, TypeAPI,
    },
};
macro_rules! object_type_match {
    ($obj_var:ident, $block:block) => {
        match &$obj_var {
            ObjectType::Entity($obj_var) => $block,
            ObjectType::Relation($obj_var) => $block,
        }
    };
}

macro_rules! get_label {
    ($snapshot: ident, $type_:ident) => {
        TypeReader::get_label($snapshot, $type_).unwrap().unwrap()
    };
}

pub struct OperationTimeValidation {}

impl OperationTimeValidation {
    pub(crate) fn validate_type_exists<Snapshot, T>(snapshot: &Snapshot, type_: T) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
        T: KindAPI<'static>,
    {
        TypeReader::get_label(snapshot, type_).map_err(|err| SchemaValidationError::ConceptRead(err))?;
        Ok(())
    }

    pub(crate) fn validate_type_is_not_root<Snapshot, T>(
        snapshot: &Snapshot,
        type_: T,
    ) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
        T: KindAPI<'static>,
    {
        let label = TypeReader::get_label(snapshot, type_).map_err(SchemaValidationError::ConceptRead)?.unwrap();
        let is_root = TypeReader::check_type_is_root(&label, T::ROOT_KIND);
        if is_root {
            Err(SchemaValidationError::RootModification)
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_no_subtypes<Snapshot, T>(snapshot: &Snapshot, type_: T) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
        T: KindAPI<'static>,
    {
        let no_subtypes =
            TypeReader::get_subtypes(snapshot, type_.clone()).map_err(SchemaValidationError::ConceptRead)?.is_empty();
        if no_subtypes {
            Ok(())
        } else {
            Err(SchemaValidationError::DeletingTypeWithSubtypes(get_label!(snapshot, type_)))
        }
    }

    pub(crate) fn validate_label_uniqueness<'a, Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        new_label: &Label<'static>,
    ) -> Result<(), SchemaValidationError> {
        let attribute_clash = TypeReader::get_labelled_type::<AttributeType<'static>>(snapshot, &new_label)
            .map_err(SchemaValidationError::ConceptRead)?
            .is_some();
        let relation_clash = TypeReader::get_labelled_type::<RelationType<'static>>(snapshot, &new_label)
            .map_err(SchemaValidationError::ConceptRead)?
            .is_some();
        let entity_clash = TypeReader::get_labelled_type::<EntityType<'static>>(snapshot, &new_label)
            .map_err(SchemaValidationError::ConceptRead)?
            .is_some();

        if attribute_clash || relation_clash || entity_clash {
            Err(SchemaValidationError::LabelUniqueness(new_label.clone()))
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_value_types_compatible(
        subtype_value_type: Option<ValueType>,
        supertype_value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError> {
        let is_compatible = match (&subtype_value_type, &supertype_value_type) {
            ((None, None) | (None, Some(_)) | (Some(_), None)) => true,
            (Some(sub), Some(sup)) => sup == sub,
        };

        if is_compatible {
            Ok(())
        } else {
            Err(SchemaValidationError::IncompatibleValueTypes(subtype_value_type, supertype_value_type))
        }
    }

    pub(crate) fn validate_annotation_regex_compatible_value_type(
        value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError> {
        let is_compatible = match &value_type {
            Some(ValueType::String) => true,
            _ => false
        };

        if is_compatible {
            Ok(())
        } else {
            Err(SchemaValidationError::IncompatibleValueType(value_type))
        }
    }

    pub(crate) fn validate_type_is_abstract<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
    ) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
        T: KindAPI<'static>,
    {
        let is_abstract = TypeReader::get_type_annotations(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .contains(&T::AnnotationType::from(Annotation::Abstract(AnnotationAbstract)));
        if is_abstract {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeIsNotAbstract(get_label!(snapshot, type_)))
        }
    }

    pub(crate) fn validate_sub_does_not_create_cycle<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
        supertype: T,
    ) -> Result<(), SchemaValidationError>
    where
        T: KindAPI<'static>,
        Snapshot: ReadableSnapshot,
    {
        let existing_supertypes = TypeReader::get_supertypes_transitive(snapshot, supertype.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        if supertype == type_ || existing_supertypes.contains(&type_) {
            Err(SchemaValidationError::CyclicTypeHierarchy(
                get_label!(snapshot, type_),
                get_label!(snapshot, supertype),
            ))
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_role_is_inherited<Snapshot>(
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
        role_type: RoleType<'static>,
    ) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
    {
        let super_relation =
            TypeReader::get_supertype(snapshot, relation_type).map_err(SchemaValidationError::ConceptRead)?;
        if super_relation.is_none() {
            // TODO: Handle better. This could be misleading.
            return Err(SchemaValidationError::RootModification);
        }
        let is_inherited = TypeReader::get_relates_transitive(snapshot, super_relation.unwrap())
            .map_err(SchemaValidationError::ConceptRead)?
            .contains_key(&role_type);
        if is_inherited {
            Ok(())
        } else {
            Err(SchemaValidationError::RelatesNotInherited(role_type))
        }
    }

    pub(crate) fn validate_owns_is_inherited<Snapshot>(
        snapshot: &Snapshot,
        owner: ObjectType<'static>,
        attribute: AttributeType<'static>,
    ) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
    {
        let res = object_type_match!(owner, {
            let super_owner =
                TypeReader::get_supertype(snapshot, owner.clone()).map_err(SchemaValidationError::ConceptRead)?;
            if super_owner.is_none() {
                return Err(SchemaValidationError::RootModification);
            }
            let owns_transitive: HashMap<AttributeType<'static>, Owns<'static>> =
                TypeReader::get_implemented_interfaces_transitive(snapshot, super_owner.unwrap())
                    .map_err(SchemaValidationError::ConceptRead)?;
            let is_inherited = owns_transitive.contains_key(&attribute);
            if is_inherited {
                Ok(())
            } else {
                Err(SchemaValidationError::OwnsNotInherited(attribute))
            }
        });
        res
    }

    pub(crate) fn validate_overridden_is_supertype<Snapshot, T>(
        snapshot: &Snapshot,
        type_: T,
        overridden: T,
    ) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
        T: KindAPI<'static>,
    {
        let supertypes = TypeReader::get_supertypes_transitive(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        if supertypes.contains(&overridden.clone()) {
            Ok(())
        } else {
            Err(SchemaValidationError::OverriddenTypeNotSupertype(
                get_label!(snapshot, type_),
                get_label!(snapshot, overridden),
            ))
        }
    }

    pub(crate) fn validate_plays_is_inherited<Snapshot>(
        snapshot: &Snapshot,
        player: ObjectType<'static>,
        role_type: RoleType<'static>,
    ) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
    {
        let is_inherited = object_type_match!(player, {
            let super_player =
                TypeReader::get_supertype(snapshot, player.clone()).map_err(SchemaValidationError::ConceptRead)?;
            if super_player.is_none() {
                return Err(SchemaValidationError::RootModification);
            }
            let plays_transitive: HashMap<RoleType<'static>, Plays<'static>> =
                TypeReader::get_implemented_interfaces_transitive(snapshot, super_player.unwrap())
                    .map_err(SchemaValidationError::ConceptRead)?;
            plays_transitive.contains_key(&role_type)
        });
        if is_inherited {
            Ok(())
        } else {
            Err(SchemaValidationError::PlaysNotInherited(player.into_owned(), role_type))
        }
    }

    pub(crate) fn validate_plays_is_declared<Snapshot>(
        snapshot: &Snapshot,
        player: ObjectType<'static>,
        role_type: RoleType<'static>,
    ) -> Result<(), SchemaValidationError>
    where
        Snapshot: ReadableSnapshot,
    {
        let plays = Plays::new(ObjectType::new(player.clone().into_vertex()), role_type.clone());
        let is_declared = TypeReader::get_implemented_interfaces::<Plays<'static>>(snapshot, player.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .contains(&plays);
        if is_declared {
            Ok(())
        } else {
            Err(SchemaValidationError::PlaysNotDeclared(player.into_owned(), role_type))
        }
    }

    // TODO: Refactor
    pub(crate) fn validate_exact_type_no_instances_entity<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        thing_manager: &ThingManager<Snapshot>,
        entity_type: EntityType<'_>,
    ) -> Result<(), SchemaValidationError> {
        let mut entity_iterator = thing_manager.get_entities_in(snapshot, entity_type.clone());
        match entity_iterator.next() {
            None => Ok(()),
            Some(Ok(_)) => Err(SchemaValidationError::DeletingTypeWithInstances(get_label!(snapshot, entity_type))),
            Some(Err(concept_read_error)) => Err(SchemaValidationError::ConceptRead(concept_read_error)),
        }
    }
    pub(crate) fn validate_exact_type_no_instances_relation<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        thing_manager: &ThingManager<Snapshot>,
        relation_type: RelationType<'_>,
    ) -> Result<(), SchemaValidationError> {
        let mut relation_iterator = thing_manager.get_relations_in(snapshot, relation_type.clone());
        match relation_iterator.next() {
            None => Ok(()),
            Some(Ok(_)) => Err(SchemaValidationError::DeletingTypeWithInstances(get_label!(snapshot, relation_type))),
            Some(Err(concept_read_error)) => Err(SchemaValidationError::ConceptRead(concept_read_error)),
        }
    }

    pub(crate) fn validate_exact_type_no_instances_attribute<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        thing_manager: &ThingManager<Snapshot>,
        attribute_type: AttributeType<'_>,
    ) -> Result<(), SchemaValidationError> {
        let mut attribute_iterator = thing_manager
            .get_attributes_in(snapshot, attribute_type.clone())
            .map_err(|err| SchemaValidationError::ConceptRead(err.clone()))?;
        match attribute_iterator.next() {
            None => Ok(()),
            Some(Ok(_)) => Err(SchemaValidationError::DeletingTypeWithInstances(get_label!(snapshot, attribute_type))),
            Some(Err(err)) => Err(SchemaValidationError::ConceptRead(err.clone())),
        }
    }

    pub(crate) fn validate_exact_type_no_instances_role<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        thing_manager: &ThingManager<Snapshot>,
        role_type: RoleType<'_>,
    ) -> Result<(), SchemaValidationError> {
        // TODO: See if we can use existing methods from the ThingManager
        let relation_type = TypeReader::get_relation(snapshot, role_type.clone().into_owned())
            .map_err(SchemaValidationError::ConceptRead)?
            .relation();
        let prefix =
            ObjectVertex::build_prefix_type(Prefix::VertexRelation.prefix_id(), relation_type.vertex().type_id_());
        let snapshot_iterator =
            snapshot.iterate_range(KeyRange::new_within(prefix, Prefix::VertexRelation.fixed_width_keys()));
        let mut relation_iterator = RelationIterator::new(snapshot_iterator);
        while let Some(result) = relation_iterator.next() {
            let relation_instance = result.map_err(SchemaValidationError::ConceptRead)?;
            let prefix = ThingEdgeRolePlayer::prefix_from_relation(relation_instance.into_vertex());
            let mut role_player_iterator = RolePlayerIterator::new(
                snapshot.iterate_range(KeyRange::new_within(prefix, ThingEdgeRolePlayer::FIXED_WIDTH_ENCODING)),
            );
            match role_player_iterator.next() {
                None => {}
                Some(Ok(_)) => {
                    let role_type_clone = role_type.clone();
                    Err(SchemaValidationError::DeletingTypeWithInstances(get_label!(snapshot, role_type_clone)))?;
                }
                Some(Err(concept_read_error)) => {
                    Err(SchemaValidationError::ConceptRead(concept_read_error))?;
                }
            }
        }

        Ok(())
    }
}
