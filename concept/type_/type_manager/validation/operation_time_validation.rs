/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashMap;
use std::hash::Hash;
use itertools::Itertools;

use encoding::{
    graph::{
        thing::{edge::ThingEdgeRolePlayer, vertex_object::ObjectVertex},
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
        annotation::{Annotation, AnnotationAbstract, AnnotationCategory, AnnotationCardinality, AnnotationRegex},
        attribute_type::{AttributeType, AttributeTypeAnnotation},
        entity_type::EntityType,
        object_type::ObjectType,
        owns::Owns,
        plays::Plays,
        relation_type::RelationType,
        relates::Relates,
        role_type::RoleType,
        type_manager::{
            type_reader::TypeReader,
            validation::{
                SchemaValidationError,
            }
        },
        KindAPI, TypeAPI, ObjectTypeAPI,
        Ordering, InterfaceImplementation
    },
};
use crate::error::ConceptWriteError;

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
        // TODO: Check struct clash?

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

    pub(crate) fn validate_struct_name_uniqueness<'a, Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        name: &String,
    ) -> Result<(), SchemaValidationError> {
        let struct_clash = TypeReader::get_struct_definition_key(snapshot, name.as_str())
            .map_err(SchemaValidationError::ConceptRead)?
            .is_some();
        // TODO: Check other types clash?

        if struct_clash {
            Err(SchemaValidationError::NameUniqueness(name.clone()))
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_value_type_is_compatible_with_new_supertypes_value_type<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        subtype: AttributeType<'static>,
        supertype: AttributeType<'static>,
    ) -> Result<(), SchemaValidationError> {

        let subtype_declared_value_type = TypeReader::get_value_type_declared(snapshot, subtype.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        let subtype_transitive_value_type = TypeReader::get_value_type_without_source(snapshot, subtype.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        let supertype_value_type = TypeReader::get_value_type_without_source(snapshot, supertype.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        match (&subtype_declared_value_type, &subtype_transitive_value_type, &supertype_value_type) {
            (None, None, None) => Ok(()),
            (None, None, Some(_)) => Ok(()),
            (None, Some(_), None) => {
                Self::validate_when_attribute_type_loses_value_type(snapshot, subtype, subtype_transitive_value_type)
            },
            (Some(_), None, None) => Ok(()),
            (Some(_), Some(_), None) => Ok(()),
            | (None, Some(old_value_type), Some(new_value_type))
            | (Some(old_value_type), None, Some(new_value_type))
            | (Some(old_value_type), Some(_), Some(new_value_type)) => {
                if old_value_type == new_value_type {
                    Ok(())
                } else {
                    Err(SchemaValidationError::CannotChangeValueTypeOfAttributeType(
                        get_label!(snapshot, subtype), subtype_declared_value_type))
                }
            },
        }
    }

    pub(crate) fn validate_value_type_can_be_unset<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
        declared_value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError> {
        let attribute_supertype = TypeReader::get_supertype(snapshot, attribute_type.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        match &attribute_supertype {
            Some(supertype) => {
                let supertype_value_type = TypeReader::get_value_type_without_source(snapshot, supertype.clone())
                    .map_err(SchemaValidationError::ConceptRead)?;
                match supertype_value_type {
                    Some(_) => Ok(()),
                    None => Self::validate_when_attribute_type_loses_value_type(snapshot, attribute_type, declared_value_type),
                }
            },
            None => Self::validate_when_attribute_type_loses_value_type(snapshot, attribute_type, declared_value_type),
        }
    }

    pub(crate) fn validate_value_type_compatible_with_abstractness<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
        value_type: Option<ValueType>,
        abstract_set: Option<bool>,
    ) -> Result<(), SchemaValidationError> {
        let is_abstract = abstract_set.unwrap_or(
            Self::type_has_annotation_category(snapshot, attribute_type.clone(), AnnotationCategory::Abstract)?
        );

        match &value_type {
            Some(_) => Ok(()),
            None => {
                if is_abstract {
                    Ok(())
                } else {
                    Err(SchemaValidationError::AttributeTypeWithoutValueTypeShouldBeAbstract(
                        get_label!(snapshot, attribute_type)
                    ))
                }
            }
        }
    }

    // TODO: Move to annotation_compatibility ?

    pub(crate) fn validate_annotation_regex_compatible_value_type<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
        value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError> {
        let is_compatible = match &value_type {
            Some(ValueType::String) => true,
            _ => false
        };

        if is_compatible {
            Ok(())
        } else {
            Err(SchemaValidationError::AnnotationRegexOnAttributeRequiresStringValueType(get_label!(snapshot, attribute_type)))
        }
    }

    pub(crate) fn validate_annotation_set_only_for_interface<IMPL, Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        interface: IMPL::InterfaceType,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            IMPL: InterfaceImplementation<'static, ObjectType = ObjectType<'static>> + Hash + Eq,
    {
        let implementations = TypeReader::get_implementations_for_interface::<IMPL>(
            snapshot, interface.clone()
        ).map_err(SchemaValidationError::ConceptRead)?;

        for (_, implementation) in implementations {
            let implementation_annotations = TypeReader::get_type_edge_annotations(snapshot, implementation)
                .map_err(SchemaValidationError::ConceptRead)?;
            if implementation_annotations.iter()
                .map(|(annotation, _)| annotation.category())
                .contains(&annotation_category) {
                return Err(SchemaValidationError::CannotSetAnnotationToInterfaceBecauseItAlreadyExistsForItsImplementation(
                    get_label!(snapshot, interface), annotation_category
                ));
            }
        }

        Ok(())
    }

    pub(crate) fn validate_annotation_set_only_for_interface_implementation<IMPL, Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        interface_implementation: IMPL,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            IMPL: InterfaceImplementation<'static, ObjectType = ObjectType<'static>> + Hash + Eq,
    {
        let interface = interface_implementation.interface();
        let interface_annotations = TypeReader::get_type_annotations(snapshot, interface.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        if interface_annotations.iter()
            .map(|(annotation, _)| annotation.clone().into().category())
            .contains(&annotation_category) {
            return Err(SchemaValidationError::CannotSetAnnotationToInterfaceImplementationBecauseItAlreadyExistsForItsInterface(
                get_label!(snapshot, interface), annotation_category
            ));
        }

        Ok(())
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
            Self::type_has_declared_annotation_category(snapshot, attribute_type.clone(), annotation_category)?;

        if owns_has_annotation && attribute_type_has_annotation {
            Err(SchemaValidationError::AnnotationCanOnlyBeSetOnAttributeOrOwns(
                get_label!(snapshot, attribute_type), annotation_category)
            )
        } else {
            Ok(())
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
        Self::type_has_declared_annotation(snapshot, type_.clone(), Annotation::Abstract(AnnotationAbstract))
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
            Err(SchemaValidationError::InvalidCardinalityArguments(cardinality))
        }
    }

    pub(crate) fn validate_regex_arguments(
        regex: AnnotationRegex,
    ) -> Result<(), SchemaValidationError> {
        if !regex.regex().is_empty() {
            Ok(())
        } else {
            Err(SchemaValidationError::InvalidRegexArguments(regex))
        }
    }

    pub(crate) fn validate_cardinality_narrows_annotation<EDGE, Snapshot>(
        snapshot: &Snapshot,
        supertype_edge: EDGE,
        cardinality: AnnotationCardinality,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            EDGE: InterfaceImplementation<'static> + Clone,
    {
        if let Some(supertype_annotation) = Self::edge_get_annotation_by_category(
            snapshot, supertype_edge, AnnotationCategory::Cardinality
        )? {
            match supertype_annotation {
                Annotation::Cardinality(supertype_cardinality) => {
                    if supertype_cardinality.narrowed_correctly_by(&cardinality) {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::CardinalityShouldNarrowInheritedCardinality(supertype_cardinality.clone()))
                    }
                }
                _ => unreachable!("Should not reach it for Cardinality-related function")
            }
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_type_regex_narrows_annotation<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        supertype: impl KindAPI<'static>,
        regex: AnnotationRegex,
    ) -> Result<(), SchemaValidationError> {
        if let Some(supertype_annotation) = Self::type_get_annotation_by_category(
            snapshot, supertype, AnnotationCategory::Regex
        )? {
            match supertype_annotation {
                Annotation::Regex(supertype_regex) => {
                    if supertype_regex.regex() == regex.regex() {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::RegexCannotBeRedeclaredOnSubtypes(
                            supertype_regex.clone()
                        ))
                    }
                },
                _ => unreachable!("Should not reach it for Regex-related function")
            }
        } else {
            Ok(())
        }
    }

    pub(crate) fn validate_edge_regex_narrows_annotation<EDGE, Snapshot>(
        snapshot: &Snapshot,
        supertype_edge: EDGE,
        regex: AnnotationRegex,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            EDGE: InterfaceImplementation<'static> + Clone,
    {
        if let Some(supertype_annotation) = Self::edge_get_annotation_by_category(
            snapshot, supertype_edge, AnnotationCategory::Regex
        )? {
            match supertype_annotation {
                Annotation::Regex(supertype_regex) => {
                    if supertype_regex.regex() == regex.regex() {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::RegexCannotBeRedeclaredOnSubtypes(
                            supertype_regex.clone()
                        ))
                    }
                },
                _ => unreachable!("Should not reach it for Regex-related function")
            }
        } else {
            Ok(())
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
        if Self::type_has_declared_annotation(snapshot, type_.clone(), annotation)? {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeDoesNotHaveAnnotation(get_label!(snapshot, type_)))
        }
    }

    pub(crate) fn validate_type_has_declared_annotation_category<T, Snapshot>(
        snapshot: &Snapshot,
        type_: T,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: KindAPI<'static>,
    {
        if Self::type_has_declared_annotation_category(snapshot, type_.clone(), annotation_category)? {
            Ok(())
        } else {
            Err(SchemaValidationError::TypeDoesNotHaveAnnotation(get_label!(snapshot, type_)))
        }
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
        let subtype_abstract = Self::type_has_declared_annotation_category(snapshot, subtype.clone(), AnnotationCategory::Abstract)?;
        let supertype_abstract = Self::type_has_declared_annotation_category(snapshot, supertype.clone(), AnnotationCategory::Abstract)?;

        match (subtype_abstract, supertype_abstract) {
            (false, false) | (false, true) | (true, true) => Ok(()),
            (true, false) => Err(SchemaValidationError::NonAbstractSupertypeOfAbstractSubtype(
                get_label!(snapshot, supertype), get_label!(snapshot, subtype)
            ))
        }
    }

    pub(crate) fn validate_relates_distinct_annotation_ordering<Snapshot>(
        snapshot: &Snapshot,
        relates: Relates<'static>,
        ordering: Option<Ordering>,
        distinct_set: Option<bool>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let role = relates.role();
        let ordering = ordering.unwrap_or(
            TypeReader::get_type_ordering(snapshot, role.clone()).map_err(SchemaValidationError::ConceptRead)?
        );
        let distinct_set = distinct_set.unwrap_or(
            Self::edge_get_annotation_by_category(snapshot, relates, AnnotationCategory::Distinct)?.is_some()
        );

        if Self::is_ordering_compatible_with_distinct_annotation(ordering, distinct_set) {
            Ok(())
        } else {
            Err(SchemaValidationError::InvalidOrderingForDistinctAnnotation(get_label!(snapshot, role)))
        }
    }

    pub(crate) fn validate_owns_distinct_annotation_ordering<Snapshot>(
        snapshot: &Snapshot,
        owns: Owns<'static>,
        ordering: Option<Ordering>,
        distinct_set: Option<bool>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let attribute = owns.attribute();
        let ordering = ordering.unwrap_or(
            TypeReader::get_type_edge_ordering(snapshot, owns.clone()).map_err(SchemaValidationError::ConceptRead)?
        );
        let distinct_set = distinct_set.unwrap_or(
            Self::edge_get_annotation_by_category(snapshot, owns, AnnotationCategory::Distinct)?.is_some()
        );

        if Self::is_ordering_compatible_with_distinct_annotation(ordering, distinct_set) {
            Ok(())
        } else {
            Err(SchemaValidationError::InvalidOrderingForDistinctAnnotation(get_label!(snapshot, attribute)))
        }
    }

    pub(crate) fn validate_role_supertype_ordering_match<Snapshot>(
        snapshot: &Snapshot,
        subtype_role: RoleType<'static>,
        supertype_role: RoleType<'static>,
        set_subtype_role_ordering: Option<Ordering>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let subtype_ordering = set_subtype_role_ordering.unwrap_or(
            TypeReader::get_type_ordering(snapshot, subtype_role.clone())
                .map_err(SchemaValidationError::ConceptRead)?
        );
        let supertype_ordering = TypeReader::get_type_ordering(
            snapshot, supertype_role.clone()).map_err(SchemaValidationError::ConceptRead
        )?;

        if subtype_ordering == supertype_ordering {
            Ok(())
        } else {
            Err(SchemaValidationError::OrderingDoesNotMatchWithSupertype(
                get_label!(snapshot, subtype_role), get_label!(snapshot, supertype_role)
            ))
        }
    }

    pub(crate) fn validate_owns_override_ordering_match<Snapshot>(
        snapshot: &Snapshot,
        subtype_owns: Owns<'static>,
        supertype_owns: Owns<'static>,
        set_subtype_owns_ordering: Option<Ordering>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let subtype_ordering = set_subtype_owns_ordering.unwrap_or(
            TypeReader::get_type_edge_ordering(snapshot, subtype_owns.clone())
                .map_err(SchemaValidationError::ConceptRead)?
        );
        let supertype_ordering = TypeReader::get_type_edge_ordering(snapshot, supertype_owns.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        if subtype_ordering == supertype_ordering {
            Ok(())
        } else {
            let subtype_attribute = subtype_owns.attribute();
            let supertype_attribute = supertype_owns.attribute();
            Err(SchemaValidationError::OrderingDoesNotMatchWithSupertype(
                get_label!(snapshot, subtype_attribute), get_label!(snapshot, supertype_attribute)
            ))
        }
    }

    pub(crate) fn validate_supertype_annotations_compatibility<Snapshot>(
        snapshot: &Snapshot,
        subtype: impl KindAPI<'static>,
        supertype: impl KindAPI<'static>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let subtype_declared_annotations = TypeReader::get_type_annotations_declared(snapshot, subtype)
            .map_err(SchemaValidationError::ConceptRead)?;
        for subtype_annotation in subtype_declared_annotations {
            let subtype_annotation = subtype_annotation.clone().into();
            let category = subtype_annotation.category();
            OperationTimeValidation::validate_type_declared_annotation_is_compatible_with_inherited_annotations(
                snapshot, supertype.clone(), category
            )?;

            match subtype_annotation {
                Annotation::Regex(regex) =>
                    OperationTimeValidation::validate_type_regex_narrows_annotation(
                        snapshot, supertype.clone(), regex
                    )?,
                | Annotation::Abstract(_)
                | Annotation::Distinct(_)
                | Annotation::Independent(_)
                | Annotation::Unique(_)
                | Annotation::Key(_)
                | Annotation::Cardinality(_)
                | Annotation::Cascade(_) => {}
            }
        }

        Ok(())
    }

    pub(crate) fn validate_edge_override_annotations_compatibility<EDGE, Snapshot>(
        snapshot: &Snapshot,
        edge: EDGE,
        overridden_edge: EDGE,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone,
    {
        let subtype_declared_annotations = TypeReader::get_type_edge_annotations_declared(snapshot, edge)
            .map_err(SchemaValidationError::ConceptRead)?;
        for subtype_annotation in subtype_declared_annotations {
            let category = subtype_annotation.category();
            OperationTimeValidation::validate_declared_edge_annotation_is_compatible_with_inherited_annotations(
                snapshot, overridden_edge.clone(), category
            )?;

            match subtype_annotation {
                Annotation::Cardinality(cardinality) =>
                    OperationTimeValidation::validate_cardinality_narrows_annotation(
                        snapshot, overridden_edge.clone(), cardinality
                    )?,
                Annotation::Regex(regex) =>
                    OperationTimeValidation::validate_edge_regex_narrows_annotation(
                        snapshot, overridden_edge.clone(), regex
                    )?,
                | Annotation::Abstract(_)
                | Annotation::Distinct(_)
                | Annotation::Independent(_)
                | Annotation::Unique(_)
                | Annotation::Key(_)
                | Annotation::Cascade(_) => {}
            }
        }

        Ok(())
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

    pub(crate) fn validate_relates_is_inherited<Snapshot>(
        snapshot: &Snapshot,
        relation_type: RelationType<'static>,
        role_type: RoleType<'static>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let super_relation =
            TypeReader::get_supertype(snapshot, relation_type.clone()).map_err(SchemaValidationError::ConceptRead)?;
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
            Err(SchemaValidationError::RelatesNotInherited(relation_type, role_type))
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
        let is_inherited = object_type_match!(owner, {
            let super_owner =
                TypeReader::get_supertype(snapshot, owner.clone()).map_err(SchemaValidationError::ConceptRead)?;
            if super_owner.is_none() {
                return Err(SchemaValidationError::RootModification);
            }
            let owns_transitive: HashMap<AttributeType<'static>, Owns<'static>> =
                TypeReader::get_implemented_interfaces(snapshot, super_owner.unwrap())
                    .map_err(SchemaValidationError::ConceptRead)?;
            owns_transitive.contains_key(&attribute)
        });
        if is_inherited {
            Ok(())
        } else {
            Err(SchemaValidationError::OwnsNotInherited(owner, attribute))
        }
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

    pub(crate) fn validate_attribute_type_owns_not_overridden<T, Snapshot>(
        snapshot: &Snapshot,
        owner: T,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: ObjectTypeAPI<'static>,
    {
        let is_overridden = {
            let all_overridden = TypeReader::get_overridden_interfaces::<Owns<'static>, T>(snapshot, owner.clone())
                .map_err(SchemaValidationError::ConceptRead)?;
            all_overridden.contains_key(&attribute_type)
        };
        if !is_overridden {
            Ok(())
        } else {
            Err(SchemaValidationError::OwnsCannotBeDeclaredAsItHasBeenOverridden(
                get_label!(snapshot, owner), attribute_type
            ))
        }
    }

    pub(crate) fn validate_role_plays_not_overridden<T, Snapshot>(
        snapshot: &Snapshot,
        player: T,
        role_type: RoleType<'static>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            T: ObjectTypeAPI<'static>,
    {
        let is_overridden = {
            let all_overridden = TypeReader::get_overridden_interfaces::<Plays<'static>, T>(snapshot, player.clone())
                .map_err(SchemaValidationError::ConceptRead)?;
            all_overridden.contains_key(&role_type)
        };
        if !is_overridden {
            Ok(())
        } else {
            Err(SchemaValidationError::PlaysCannotBeDeclaredAsItHasBeenOverridden(
                get_label!(snapshot, player), role_type
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
            Err(SchemaValidationError::PlaysNotInherited(player, role_type))
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

    pub(crate) fn validate_value_type_compatible_with_existing_value_type<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
        value_type: ValueType,
        existing_value_type_with_source: Option<(ValueType, AttributeType<'static>)>,
    ) -> Result<(), SchemaValidationError> {
        if let Some((existing_value_type, existing_value_type_source)) = existing_value_type_with_source {
            return if existing_value_type == value_type {
                Ok(())
            } else {
                Err(SchemaValidationError::ValueTypeNotCompatibleWithExitingValueTypeOf(
                    get_label!(snapshot, attribute_type),
                    get_label!(snapshot, existing_value_type_source),
                    existing_value_type,
                ))
            }
        }
        Ok(())
    }

    pub(crate) fn validate_value_type_compatible_with_subtypes_value_types<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
        value_type: ValueType,
    ) -> Result<(), SchemaValidationError> {
        let subtypes = TypeReader::get_subtypes_transitive(snapshot, attribute_type.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        for subtype in subtypes {
            let subtype_value_type_opt = TypeReader::get_value_type_declared(snapshot, subtype.clone())
                .map_err(SchemaValidationError::ConceptRead)?;
            if let Some(subtype_value_type) = subtype_value_type_opt {
                if subtype_value_type != value_type {
                    let subtype = subtype.clone();
                    return Err(SchemaValidationError::ValueTypeNotCompatibleWithSubtypesValueType(
                        get_label!(snapshot, attribute_type),
                        get_label!(snapshot, subtype),
                        subtype_value_type,
                    ));
                }
            }
        }
        Ok(())
    }

    pub(crate) fn validate_when_attribute_type_loses_value_type<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
        value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError> {
        match value_type {
            Some(_) => {
                Self::validate_value_type_compatible_with_abstractness(snapshot, attribute_type.clone(), None, None)?;
                Self::validate_current_annotations_do_not_require_unset_value_type(snapshot, attribute_type.clone())?;
                Self::validate_no_non_abstract_subtypes_without_value_type(snapshot, attribute_type)
                // TODO: Re-enable when we get the thing_manager
                // OperationTimeValidation::validate_exact_type_no_instances_attribute(snapshot, self, attribute.clone())
            }
            None => Ok(())
        }
    }

    pub(crate) fn validate_no_non_abstract_subtypes_without_value_type<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), SchemaValidationError> {
        let subtypes = TypeReader::get_subtypes_transitive(snapshot, attribute_type.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        for subtype in subtypes {
            let no_value_type = TypeReader::get_value_type_declared(snapshot, subtype.clone())
                .map_err(SchemaValidationError::ConceptRead)?
                .is_none();

            if no_value_type
                && !Self::type_has_declared_annotation_category(snapshot, subtype.clone(), AnnotationCategory::Abstract)? {
                    let subtype = subtype.clone();
                    return Err(SchemaValidationError::NonAbstractSubtypeWithoutValueTypeExists(
                        get_label!(snapshot, attribute_type),
                        get_label!(snapshot, subtype),
                    ));
                }
            }
        Ok(())
    }

    pub(crate) fn validate_current_annotations_do_not_require_unset_value_type<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), SchemaValidationError> {
        let annotations = TypeReader::get_type_annotations(snapshot, attribute_type.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        for (annotation, _) in annotations {
            match annotation {
                AttributeTypeAnnotation::Regex(_) => return Err(
                    SchemaValidationError::AnnotationRegexOnAttributeRequiresStringValueType(
                        get_label!(snapshot, attribute_type)
                    )
                ),
                | AttributeTypeAnnotation::Abstract(_)
                | AttributeTypeAnnotation::Independent(_) => {}
            }
        }

        let attribute_owns =
            TypeReader::get_implementations_for_interface::<Owns<'static>>(snapshot, attribute_type.clone())
                .map_err(SchemaValidationError::ConceptRead)?;
        for (owner, owns) in attribute_owns {
            let owns_annotations = TypeReader::get_type_edge_annotations(snapshot, owns.clone())
                .map_err(SchemaValidationError::ConceptRead)?;
            for (annotation, _) in owns_annotations {
                match annotation {
                    Annotation::Regex(_) => return Err(
                        SchemaValidationError::AnnotationRegexOnOwnsRequiresStringValueType(
                            get_label!(snapshot, attribute_type), get_label!(snapshot, owner)
                        )
                    ),
                    Annotation::Unique(_) => {
                        if Self::is_owns_value_type_keyable(None) {
                            return Err(
                                SchemaValidationError::AnnotationUniqueOnOwnsRequiresKeyableValueType(
                                    get_label!(snapshot, attribute_type), get_label!(snapshot, owner)
                                )
                            )
                        }
                    },
                    Annotation::Key(_) => {
                        if Self::is_owns_value_type_keyable(None) {
                            return Err(
                                SchemaValidationError::AnnotationKeyOnOwnsRequiresKeyableValueType(
                                    get_label!(snapshot, attribute_type), get_label!(snapshot, owner)
                                )
                            )
                        }
                    },
                    | Annotation::Abstract(_)
                    | Annotation::Distinct(_)
                    | Annotation::Independent(_)
                    | Annotation::Cardinality(_)
                    | Annotation::Cascade(_) => {}
                }
            }
        }

        Ok(())
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

    pub(crate) fn validate_unset_owns_is_not_inherited<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        owner: ObjectType<'static>,
        attribute_type: AttributeType<'static>,
    ) -> Result<(), SchemaValidationError> {
        let all_owns: HashMap<AttributeType<'static>, Owns<'static>> =
            TypeReader::get_implemented_interfaces(snapshot, owner.clone())
                .map_err(SchemaValidationError::ConceptRead)?;
        let found_owns = all_owns.iter()
            .find(|(existing_owns_attribute_type, existing_owns)|
                **existing_owns_attribute_type == attribute_type);

        match found_owns {
            Some((_, owns)) => {
                if owner == owns.owner() {
                    Ok(())
                } else {
                    let owns_owner = owns.owner();
                    Err(SchemaValidationError::CannotUnsetInheritedOwns(
                        get_label!(snapshot, attribute_type), get_label!(snapshot, owner)
                    ))
                }
            },
            None => Ok(())
        }
    }

    pub(crate) fn validate_unset_plays_is_not_inherited<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        player: ObjectType<'static>,
        role_type: RoleType<'static>,
    ) -> Result<(), SchemaValidationError> {
        let all_plays: HashMap<RoleType<'static>, Plays<'static>> =
            TypeReader::get_implemented_interfaces(snapshot, player.clone())
                .map_err(SchemaValidationError::ConceptRead)?;
        let found_plays = all_plays.iter()
            .find(|(existing_plays_role_type, existing_plays)|
                **existing_plays_role_type == role_type);

        match found_plays {
            Some((_, plays)) => {
                if player == plays.player() {
                    Ok(())
                } else {
                    let plays_player = plays.player();
                    Err(SchemaValidationError::CannotUnsetInheritedPlays(
                        get_label!(snapshot, role_type), get_label!(snapshot, plays_player)
                    ))
                }
            },
            None => Ok(())
        }
    }

    pub(crate) fn validate_unset_annotation_is_not_inherited<T, Snapshot>(
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

    pub(crate) fn validate_unset_edge_annotation_is_not_inherited<EDGE, Snapshot>(
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

    pub(crate) fn validate_type_declared_annotation_is_compatible_with_inherited_annotations<Snapshot>(
        snapshot: &Snapshot,
        type_: impl KindAPI<'static>,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let existing_annotations = TypeReader::get_type_annotations(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        for (existing_annotation, _) in existing_annotations {
            let existing_annotation_category = existing_annotation.clone().into().category();
            if !existing_annotation_category.compatible_to_transitively_add(annotation_category) {
                return Err(SchemaValidationError::DeclaredAnnotationIsNotCompatibleWithInheritedAnnotation(
                    annotation_category, existing_annotation_category, get_label!(snapshot, type_)
                ))
            }
        }

        Ok(())
    }

    pub(crate) fn validate_declared_edge_annotation_is_compatible_with_inherited_annotations<EDGE, Snapshot>(
        snapshot: &Snapshot,
        edge: EDGE,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone,
    {
        let existing_annotations = TypeReader::get_type_edge_annotations(snapshot, edge.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        for (existing_annotation, _) in existing_annotations {
            let existing_annotation_category = existing_annotation.category();
            if !existing_annotation_category.compatible_to_transitively_add(annotation_category) {
                let interface = edge.interface();
                return Err(SchemaValidationError::DeclaredAnnotationIsNotCompatibleWithInheritedAnnotation(
                    annotation_category, existing_annotation_category, get_label!(snapshot, interface)
                ))
            }
        }

        Ok(())
    }

    pub(crate) fn validate_set_annotation_is_compatible_with_declared_annotations<Snapshot>(
        snapshot: &Snapshot,
        type_: impl KindAPI<'static>,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let existing_annotations = TypeReader::get_type_annotations_declared(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        for existing_annotation in existing_annotations {
            let existing_annotation_category = existing_annotation.clone().into().category();
            if !existing_annotation_category.compatible_to_declare_together(annotation_category) {
                return Err(SchemaValidationError::AnnotationIsNotCompatibleWithDeclaredAnnotation(
                    annotation_category, existing_annotation_category, get_label!(snapshot, type_)
                ))
            }
        }

        Ok(())
    }

    pub(crate) fn validate_set_edge_annotation_is_compatible_with_declared_annotations<EDGE, Snapshot>(
        snapshot: &Snapshot,
        edge: EDGE,
        annotation_category: AnnotationCategory,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static> + Clone,
    {
        let existing_annotations = TypeReader::get_type_edge_annotations_declared(snapshot, edge.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        for existing_annotation in existing_annotations {
            let existing_annotation_category = existing_annotation.category();
            if !existing_annotation_category.compatible_to_declare_together(annotation_category) {
                let interface = edge.interface();
                return Err(SchemaValidationError::AnnotationIsNotCompatibleWithDeclaredAnnotation(
                    annotation_category, existing_annotation_category, get_label!(snapshot, interface)
                ))
            }
        }

        Ok(())
    }

    pub(crate) fn validate_owns_value_type_keyable<Snapshot>(
        snapshot: &Snapshot,
        owns: Owns<'static>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let value_type = TypeReader::get_value_type_without_source(snapshot, owns.attribute().clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        if Self::is_owns_value_type_keyable(value_type.clone()) {
            Ok(())
        } else {
            let owner = owns.owner();
            let attribute_type = owns.attribute();
            Err(SchemaValidationError::ValueTypeIsNotKeyable(
                get_label!(snapshot, owner), get_label!(snapshot, attribute_type), value_type
            ))
        }
    }

    pub fn validate_value_type_keyable_for_all_owns_annotations<Snapshot>(
        snapshot: &Snapshot,
        attribute_type: AttributeType<'static>,
        value_type: Option<ValueType>,
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let all_owns = TypeReader::get_implementations_for_interface::<Owns<'static>>(snapshot, attribute_type.clone())
            .map_err(SchemaValidationError::ConceptRead)?;

        for (_, owns) in all_owns {
            Self::validate_owns_value_type_keyable_for_annotations(snapshot, owns, value_type.clone())?
        }
        Ok(())
    }

    fn validate_owns_value_type_keyable_for_annotations<Snapshot>(
        snapshot: &Snapshot,
        owns: Owns<'static>,
        value_type: Option<ValueType>
    ) -> Result<(), SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
    {
        let annotations = TypeReader::get_type_edge_annotations(snapshot, owns.clone())
            .map_err(SchemaValidationError::ConceptRead)?;
        for (annotation, _) in annotations {
            match annotation {
                Annotation::Unique(_) => {
                    if !Self::is_owns_value_type_keyable(value_type.clone()) {
                        let owner = owns.owner();
                        let attribute_type = owns.attribute();
                        return Err(SchemaValidationError::ValueTypeIsNotKeyableForUniqueAnnotation(
                            get_label!(snapshot, owner), get_label!(snapshot, attribute_type), value_type
                        ))
                    }
                }
                Annotation::Key(_) => {
                    if !Self::is_owns_value_type_keyable(value_type.clone()) {
                        let owner = owns.owner();
                        let attribute_type = owns.attribute();
                        return Err(SchemaValidationError::ValueTypeIsNotKeyableForKeyAnnotation(
                            get_label!(snapshot, owner), get_label!(snapshot, attribute_type), value_type
                        ))
                    }
                }
                | Annotation::Abstract(_)
                | Annotation::Distinct(_)
                | Annotation::Independent(_)
                | Annotation::Cardinality(_)
                | Annotation::Regex(_)
                | Annotation::Cascade(_) => {}
            }
        }
        Ok(())
    }

    pub(crate) fn is_owns_value_type_keyable(value_type_opt: Option<ValueType>) -> bool
    {
        match value_type_opt {
            Some(value_type) => value_type.keyable(),
            None => true,
        }
    }

    // TODO: Try to wrap all these type_has_***annotation and edge_has_***annotation into several macros!

    // TODO: Refactor to type_get_declared_annotaiton
    fn type_has_declared_annotation<T, Snapshot>(
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

    fn type_has_declared_annotation_category<T, Snapshot>(
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
            .any(|found_category| found_category == annotation_category);
        Ok(has)
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
        let has = TypeReader::get_type_annotations(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .contains_key(&T::AnnotationType::from(annotation));
        Ok(has)
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
        let has = TypeReader::get_type_annotations(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .iter().map(|(annotation, _)| annotation.clone().into().category())
            .any(|found_category| found_category == annotation_category);
        Ok(has)
    }

    fn type_get_annotation_by_category<Snapshot: ReadableSnapshot>(
        snapshot: &Snapshot,
        type_: impl KindAPI<'static>,
        annotation_category: AnnotationCategory,
    ) -> Result<Option<Annotation>, SchemaValidationError> {
        let annotation = TypeReader::get_type_annotations(snapshot, type_.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .into_iter().map(|(found_annotation, _)| found_annotation)
            .find(|found_annotation| found_annotation.clone().into().category() == annotation_category);
        Ok(annotation.map(|val| val.clone().into()))
    }

    fn edge_get_annotation_by_category<EDGE, Snapshot>(
        snapshot: &Snapshot,
        edge: EDGE,
        annotation_category: AnnotationCategory,
    ) -> Result<Option<Annotation>, SchemaValidationError>
        where
            Snapshot: ReadableSnapshot,
            EDGE: InterfaceImplementation<'static> + Clone,
    {
        let annotation = TypeReader::get_type_edge_annotations(snapshot, edge.clone())
            .map_err(SchemaValidationError::ConceptRead)?
            .into_iter().map(|(found_annotation, _)| found_annotation)
            .find(|found_annotation| found_annotation.category() == annotation_category);
        Ok(annotation.map(|val| val.clone()))
    }

    fn is_ordering_compatible_with_distinct_annotation(
        ordering: Ordering,
        distinct_set: bool,
    ) -> bool {
        if distinct_set {
            ordering == Ordering::Ordered
        } else {
            true
        }
    }
}
