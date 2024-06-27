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
use encoding::graph::type_::edge::TypeEdgeEncoding;
use lending_iterator::LendingIterator;
use storage::{key_range::KeyRange, snapshot::ReadableSnapshot};

use crate::{
    thing::{
        object::ObjectAPI,
        relation::{RelationIterator, RolePlayerIterator},
        thing_manager::ThingManager,
    },
    type_::{
        annotation::{Annotation, AnnotationAbstract, AnnotationCategory, AnnotationCardinality},
        attribute_type::AttributeType,
        entity_type::EntityType,
        object_type::ObjectType,
        owns::Owns,
        plays::Plays,
        relation_type::RelationType,
        relates::Relates,
        role_type::RoleType,
        type_manager::{type_reader::TypeReader, validation::SchemaValidationError},
        KindAPI, TypeAPI, ObjectTypeAPI,
        Ordering,
    },
};
use crate::type_::InterfaceImplementation;

macro_rules! object_type_match {
    ($obj_var:ident, $block:block) => {
        match &$obj_var {
            ObjectType::Entity($obj_var) => $block
            ObjectType::Relation($obj_var) => $block
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

    pub(crate) fn validate_no_abstract_attribute_types_owned<Snapshot, T>(
        snapshot: &Snapshot,
        type_: T) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: ObjectTypeAPI<'static>,
    {
        TypeReader::get_implemented_interfaces_declared(snapshot, type_)
            .map_err(SchemaValidationError::ConceptRead)?
            .iter().map(Owns::attribute)
            .try_for_each(|attribute_type: AttributeType<'static>| {
                if Self::type_is_abstract(snapshot, attribute_type.clone())? {
                    Err(SchemaValidationError::OwnsAbstractType(get_label!(snapshot, attribute_type)))
                } else {
                    Ok(())
                }
            })?;

        Ok(())
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

    fn validate_role_name_uniqueness_non_transitive<'a, Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
        new_label: &Label<'static>,
    ) -> Result<(), SchemaValidationError> {
        let scoped_label = Label::build_scoped(
            new_label.name.as_str(),
            TypeReader::get_label(snapshot, relation_type).unwrap().unwrap().name().as_str(),
        );

        if TypeReader::get_labelled_type::<RoleType<'static>>(snapshot, &scoped_label)
            .map_err(SchemaValidationError::ConceptRead)?
            .is_some() {
            Err(SchemaValidationError::RoleNameUniqueness(new_label.clone()))
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_role_name_uniqueness<'a, Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
        label: &Label<'static>,
    ) -> Result<(), SchemaValidationError> {
        let existing_relation_supertypes = TypeReader::get_supertypes(snapshot, relation_type.clone().into_owned())
            .map_err(SchemaValidationError::ConceptRead)?;

        Self::validate_role_name_uniqueness_non_transitive(snapshot, relation_type, label)?;
        for relation_supertype in existing_relation_supertypes {
            Self::validate_role_name_uniqueness_non_transitive(snapshot, relation_supertype, label)?;
        }

        Ok(())
    }

    pub(crate) fn validate_value_types_compatible(
        subtype_value_type: Option<ValueType>,
        supertype_value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError> {
        let is_compatible = match (&subtype_value_type, &supertype_value_type) {
            (None, None) | (None, Some(_)) | (Some(_), None) => true,
            (Some(sub), Some(sup)) => sup == sub,
        };

        if is_compatible {
            Ok(())
        } else {
            Err(SchemaValidationError::IncompatibleValueTypes(subtype_value_type, supertype_value_type))
        }
    }

    pub(crate) fn validate_value_type_exists(
        value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError> {
        match &value_type {
            Some(_) => Ok(()),
            None => Err(SchemaValidationError::AbsentValueType) // TODO: Put label here!!
        }
    }

    // TODO: Move to annotation_compatibility ?

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

    pub(crate) fn validate_owns_attribute_type_does_not_have_annotation_category_when_setting_owns_annotation<Snapshot>(
        snapshot: &Snapshot,
        owns: Owns<'_>,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let attribute_type = owns.attribute();
        let owns_has_annotation = true;
        let attribute_type_has_annotation =
            Self::type_has_annotation_category(snapshot, attribute_type.clone(), annotation_category)?;

        if owns_has_annotation && attribute_type_has_annotation {
            Err(SchemaValidationError::AnnotationCanOnlyBeSetOnAttributeOrOwns(
                get_label!(snapshot, attribute_type), annotation_category)
            )
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_type_does_not_have_annotation_regex(
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
        if Self::type_is_abstract(snapshot, type_.clone())? {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeIsNotAbstract(get_label!(snapshot, type_)))
        }
    }

    pub(crate) fn type_is_abstract<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
    ) -> Result<bool, SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        Self::type_has_annotation(snapshot, type_.clone(), Annotation::Abstract(AnnotationAbstract))
    }

    pub(crate) fn validate_ownership_abstractness<Snapshot>(
        snapshot: &Snapshot,
        owner: impl KindAPI<'static>,
        attribute: AttributeType<'static>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let is_owner_abstract = Self::type_is_abstract(snapshot, owner.clone())?;
        let is_attribute_abstract = Self::type_is_abstract(snapshot, attribute.clone())?;

        match (&is_owner_abstract, &is_attribute_abstract) {
            (true, true) | (false, false) | (true, false) => Ok(()),
            (false, true) => Err(SchemaValidationError::NonAbstractCannotOwnAbstract(
                get_label!(snapshot, owner), get_label!(snapshot, attribute))
            ),
        }
    }

    pub(crate) fn validate_cardinality_arguments(
        cardinality: AnnotationCardinality,
    ) -> Result<(), SchemaValidationError> {
        let is_valid = match cardinality.end() {
            Some(end) if cardinality.start() > end => false,
            Some(end) if cardinality.start() == end && end == 0 => false,
            _ => true,
        };

        if is_valid {
            Ok(())
        } else {
            Err(SchemaValidationError::InvalidCardinalityArguments(cardinality.start(), cardinality.end()))
        }
    }

    pub(crate) fn validate_type_has_annotation<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
        annotation: Annotation,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        if Self::type_has_annotation(snapshot, type_.clone(), annotation)? {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeDoesNotHaveAnnotation(get_label!(snapshot, type_)))
        }
    }

    fn type_has_annotation<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
        annotation: Annotation,
    ) -> Result<bool, SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        let has = TypeReader::get_type_annotations_declared(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .contains(&T::AnnotationType::from(annotation));
        Ok(has)
    }

    pub(crate) fn validate_type_has_annotation_category<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        if Self::type_has_annotation_category(snapshot, type_.clone(), annotation_category)? {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeDoesNotHaveAnnotation(get_label!(snapshot, type_)))
        }
    }

    fn type_has_annotation_category<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
        annotation_category: AnnotationCategory,
    ) -> Result<bool, SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        let has = TypeReader::get_type_annotations_declared(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .iter().map(|annotation| annotation.clone().into().category())
            .any(|annotation| annotation == annotation_category);
        Ok(has)
    }

    pub(crate) fn validate_type_supertype_abstractness<T, Snapshot>(
        snapshot: &Snapshot,
        subtype: T,
        supertype: T,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        let subtype_abstract = Self::type_has_annotation_category(snapshot, subtype.clone(), AnnotationCategory::Abstract)?;
        let supertype_abstract = Self::type_has_annotation_category(snapshot, supertype.clone(), AnnotationCategory::Abstract)?;

        match (subtype_abstract, supertype_abstract) {
            (false, false) | (false, true) | (true, true) => Ok(()),
            (true, false) => Err(SchemaValidationError::NonAbstractSupertypeOfAbstractSubtype(
                get_label!(snapshot, supertype), get_label!(snapshot, subtype)
            ))
        }
    }

    pub(crate) fn validate_type_ordering<Snapshot>(
        snapshot: &Snapshot,
        role_type: RoleType<'_>,
        expected_ordering: Ordering,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let ordering = TypeReader::get_type_ordering(snapshot, role_type)
            .map_err(SchemaValidationError::ConceptRead)?;
        if ordering == expected_ordering {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeOrderingIsIncompatible(expected_ordering, ordering))
        }
    }

    pub(crate) fn validate_owns_ordering<Snapshot>(
        snapshot: &Snapshot,
        owns: Owns<'_>,
        expected_ordering: Ordering,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let ordering = TypeReader::get_type_edge_ordering(snapshot, owns)
            .map_err(SchemaValidationError::ConceptRead)?;
        if ordering == expected_ordering {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeOrderingIsIncompatible(expected_ordering, ordering))
        }
    }

    // TODO: Modify it to validate Distinct is ordered with explicit error!
    pub(crate) fn validate_relates_distinct_ordering<Snapshot>(
        snapshot: &Snapshot,
        relates: Relates<'_>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let role = relates.role();
        let ordering = TypeReader::get_type_ordering(snapshot, role.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        if ordering == Ordering::Ordered {
            Ok(())
        } else {
            Err(SchemaValidationError::InvalidOrderingForDistinctAnnotation(get_label!(snapshot, role)))
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
        let existing_supertypes = TypeReader::get_supertypes(snapshot, supertype.clone())
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
        let is_inherited = TypeReader::get_relates(snapshot, super_relation.unwrap())
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
                TypeReader::get_implemented_interfaces(snapshot, super_owner.unwrap())
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
        if type_ == overridden {
            return Ok(());
        }

        let supertypes = TypeReader::get_supertypes(snapshot, type_.clone())
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
                TypeReader::get_implemented_interfaces(snapshot, super_player.unwrap())
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
        let is_declared = TypeReader::get_implemented_interfaces_declared::<Plays<'static>>(snapshot, player.clone())
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
        let relation_type = TypeReader::get_role_type_relates(snapshot, role_type.clone().into_owned())
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

    pub(crate) fn validate_unsetted_annotation_is_not_inherited<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
        annotation_category: AnnotationCategory
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        let annotations = TypeReader::get_type_annotations(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        let found_annotation = annotations.iter()
            .map(|(existing_annotation, source)| (existing_annotation.clone().into().category(), source))
            .find(|(existing_category, source)| existing_category.clone() == annotation_category);

        match found_annotation {
            Some((_, owner)) => {
                if type_ == owner.clone() {
                    Ok(())
                } else {
                    let owner = owner.clone();
                    Err(SchemaValidationError::CannotUnsetInheritedAnnotation(
                        annotation_category, get_label!(snapshot, owner)
                    ))
                }
            },
            None => Ok(())
        }
    }

    pub(crate) fn validate_unsetted_edge_annotation_is_not_inherited<EDGE, Snapshot>(
        snapshot: &Snapshot,
        edge: EDGE,
        annotation_category: AnnotationCategory
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone,
    {
        let annotations = TypeReader::get_type_edge_annotations(snapshot, edge.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        let found_annotation = annotations.iter()
            .map(|(existing_annotation, source)| (existing_annotation.clone().category(), source))
            .find(|(existing_category, source)| existing_category.clone() == annotation_category);

        match found_annotation {
            Some((_, owner)) => {
                if edge == *owner {
                    Ok(())
                } else {
                    Err(SchemaValidationError::CannotUnsetInheritedEdgeAnnotation(annotation_category))
                }
            },
            None => Ok(())
        }
    }
}
