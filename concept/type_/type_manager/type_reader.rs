/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use bytes::Bytes;
use encoding::{
    error::EncodingError,
    graph::{
        definition::{definition_key::DefinitionKey, r#struct::StructDefinition, DefinitionValueEncoding},
        type_::{
            edge::{TypeEdge, TypeEdgeEncoding},
            index::{LabelToTypeVertexIndex, NameToStructDefinitionIndex},
            property::{TypeEdgeProperty, TypeEdgePropertyEncoding, TypeVertexProperty, TypeVertexPropertyEncoding},
            vertex::TypeVertexEncoding,
            Kind,
        },
    },
    layout::infix::Infix,
    value::{label::Label, string_bytes::StringBytes, value_type::ValueType},
    Keyable,
};
use iterator::Collector;
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use storage::{key_range::KeyRange, snapshot::ReadableSnapshot};

use crate::{
    error::ConceptReadError,
    type_::{
        annotation::{
            Annotation, AnnotationAbstract, AnnotationCardinality, AnnotationDistinct, AnnotationIndependent,
            AnnotationKey, AnnotationRegex, AnnotationUnique,
        },
        attribute_type::AttributeType,
        object_type::ObjectType,
        owns::Owns,
        relates::Relates,
        relation_type::RelationType,
        role_type::RoleType,
        sub::Sub,
        type_manager::validation::annotation_compatibility::is_edge_annotation_inherited,
        EdgeOverride, InterfaceImplementation, KindAPI, Ordering, TypeAPI,
    },
};
use crate::type_::type_manager::validation::annotation_compatibility::is_annotation_inherited;

pub struct TypeReader {}

impl TypeReader {
    pub(crate) fn check_type_is_root(type_label: &Label<'_>, kind: Kind) -> bool {
        type_label == &kind.root_label()
    }

    pub(crate) fn get_labelled_type<T>(
        snapshot: &impl ReadableSnapshot,
        label: &Label<'_>,
    ) -> Result<Option<T>, ConceptReadError>
    where
        T: TypeAPI<'static>,
    {
        let key = LabelToTypeVertexIndex::build(label.scoped_name.as_reference()).into_storage_key();
        match snapshot.get::<BUFFER_KEY_INLINE>(key.as_reference()) {
            Err(error) => Err(ConceptReadError::SnapshotGet { source: error }),
            Ok(None) => Ok(None),
            Ok(Some(value)) => match T::from_bytes(Bytes::Array(value)) {
                Ok(type_) => Ok(Some(type_)),
                Err(err) => match err {
                    EncodingError::UnexpectedPrefix { .. } => Ok(None),
                    _ => Err(ConceptReadError::Encoding { source: err }),
                },
            },
        }
    }

    pub(crate) fn get_struct_definition_key(
        snapshot: &impl ReadableSnapshot,
        name: &str,
    ) -> Result<Option<DefinitionKey<'static>>, ConceptReadError> {
        let index_key = NameToStructDefinitionIndex::build(StringBytes::<BUFFER_KEY_INLINE>::build_ref(name));
        let bytes = snapshot.get(index_key.into_storage_key().as_reference()).unwrap();
        Ok(bytes.map(|value| DefinitionKey::new(Bytes::Array(value))))
    }

    pub(crate) fn get_struct_definition(
        snapshot: &impl ReadableSnapshot,
        definition_key: DefinitionKey<'_>,
    ) -> Result<StructDefinition, ConceptReadError> {
        let bytes =
            snapshot.get::<BUFFER_VALUE_INLINE>(definition_key.clone().into_storage_key().as_reference()).unwrap();
        Ok(StructDefinition::from_bytes(bytes.unwrap().as_ref()))
    }
    // TODO: Should get_{super/sub}type[s_transitive] return T or T::SelfStatic.
    // T::SelfStatic is the more consistent, more honest interface, but T is convenient.
    pub(crate) fn get_supertype<T>(snapshot: &impl ReadableSnapshot, subtype: T) -> Result<Option<T>, ConceptReadError>
    where
        T: TypeAPI<'static>,
    {
        Ok(snapshot
            .iterate_range(KeyRange::new_within(
                Sub::prefix_for_canonical_edges_from(subtype),
                TypeEdge::FIXED_WIDTH_ENCODING,
            ))
            .first_cloned()
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })?
            .map(|(key, _)| Sub::<T>::decode_canonical_edge(Bytes::Array(key.into_byte_array())).supertype()))
    }

    pub fn get_supertypes<T>(
        snapshot: &impl ReadableSnapshot,
        subtype: T,
    ) -> Result<Vec<T>, ConceptReadError>
    where
        T: KindAPI<'static>,
    {
        // supertypes do NOT include themselves by design
        let mut supertypes: Vec<T> = Vec::new();
        let mut supertype_opt = TypeReader::get_supertype(snapshot, subtype.clone())?;
        while let Some(supertype) = supertype_opt {
            supertypes.push(supertype.clone());
            supertype_opt = TypeReader::get_supertype(snapshot, supertype.clone())?;
        }
        Ok(supertypes)
    }

    pub(crate) fn get_subtypes<T>(snapshot: &impl ReadableSnapshot, supertype: T) -> Result<Vec<T>, ConceptReadError>
    where
        T: KindAPI<'static>,
    {
        Ok(snapshot
            .iterate_range(KeyRange::new_within(
                Sub::prefix_for_reverse_edges_from(supertype),
                TypeEdge::FIXED_WIDTH_ENCODING,
            ))
            .collect_cloned_vec(|key, _| {
                Sub::<T>::decode_reverse_edge(Bytes::Reference(key.byte_ref()).into_owned()).subtype()
            })
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })?)
    }

    pub fn get_subtypes_transitive<T>(snapshot: &impl ReadableSnapshot, subtype: T) -> Result<Vec<T>, ConceptReadError>
    where
        T: KindAPI<'static>,
    {
        //subtypes DO NOT include themselves by design
        let mut subtypes: Vec<T> = Vec::new();
        let mut stack = TypeReader::get_subtypes(snapshot, subtype.clone())?;
        while let Some(subtype) = stack.pop() {
            subtypes.push(subtype.clone());
            stack.append(&mut TypeReader::get_subtypes(snapshot, subtype)?);
            // TODO: Should we pass an accumulator instead?
        }
        Ok(subtypes)
    }

    pub(crate) fn get_label<'a>(
        snapshot: &impl ReadableSnapshot,
        type_: impl TypeAPI<'a>,
    ) -> Result<Option<Label<'static>>, ConceptReadError> {
        Self::get_type_property::<Label<'static>>(snapshot, type_)
    }

    pub(crate) fn get_implemented_interfaces_declared<IMPL>(
        snapshot: &impl ReadableSnapshot,
        owner: impl TypeAPI<'static>,
    ) -> Result<HashSet<IMPL>, ConceptReadError>
    where
        IMPL: InterfaceImplementation<'static> + Hash + Eq,
    {
        let owns_prefix = IMPL::prefix_for_canonical_edges_from(IMPL::ObjectType::new(owner.into_vertex()));
        snapshot
            .iterate_range(KeyRange::new_within(owns_prefix, TypeEdge::FIXED_WIDTH_ENCODING))
            .collect_cloned_hashset(|key, _| IMPL::decode_canonical_edge(Bytes::Reference(key.byte_ref()).into_owned()))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_implemented_interfaces<IMPL, T>(
        snapshot: &impl ReadableSnapshot,
        object_type: T,
    ) -> Result<HashMap<IMPL::InterfaceType, IMPL>, ConceptReadError>
    where
        T: TypeAPI<'static>,
        IMPL: InterfaceImplementation<'static> + Hash + Eq,
    {
        let mut transitive_implementations: HashMap<IMPL::InterfaceType, IMPL> = HashMap::new();
        let mut overridden_interfaces: HashSet<IMPL::InterfaceType> = HashSet::new();
        let mut current_type = Some(object_type);
        while current_type.is_some() {
            let declared_implementations =
                Self::get_implemented_interfaces_declared::<IMPL>(snapshot, current_type.as_ref().unwrap().clone())?;
            for implementation in declared_implementations.into_iter() {
                let interface = implementation.interface();
                if !overridden_interfaces.contains(&interface) {
                    debug_assert!(!transitive_implementations.contains_key(&interface)); // TODO: This fails in the case of implicit overrides, such as redeclaring an ownership with a stronger annotation.
                    transitive_implementations.insert(implementation.interface(), implementation.clone());
                }
                // Has to be outside so we ignore transitively overridden ones too
                if let Some(overridden) = Self::get_implementation_override(snapshot, implementation.clone())? {
                    overridden_interfaces.add(overridden.interface());
                }
            }
            current_type = Self::get_supertype(snapshot, current_type.unwrap())?;
        }
        Ok(transitive_implementations)
    }

    pub(crate) fn get_implementation_override<IMPL>(
        snapshot: &impl ReadableSnapshot,
        implementation: IMPL,
    ) -> Result<Option<IMPL>, ConceptReadError>
    where
        IMPL: TypeEdgeEncoding<'static> + Hash + Eq,
    {
        let override_property_key = EdgeOverride::<IMPL>::build_key(implementation);
        snapshot
            .get_mapped(override_property_key.into_storage_key().as_reference(), |overridden_edge_bytes| {
                EdgeOverride::<IMPL>::from_value_bytes(overridden_edge_bytes).overridden
            })
            .map_err(|error| ConceptReadError::SnapshotGet { source: error })
    }

    pub(crate) fn get_implementations_for_interface_declared<IMPL>(
        snapshot: &impl ReadableSnapshot,
        interface_type: IMPL::InterfaceType,
    ) -> Result<HashSet<IMPL>, ConceptReadError>
    where
        IMPL: InterfaceImplementation<'static> + Hash + Eq,
    {
        let owns_prefix = IMPL::prefix_for_reverse_edges_from(interface_type);
        snapshot
            .iterate_range(KeyRange::new_within(owns_prefix, TypeEdge::FIXED_WIDTH_ENCODING))
            .collect_cloned_hashset(|key, _| IMPL::decode_reverse_edge(Bytes::Array(key.byte_ref().into())))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_implementations_for_interface<IMPL>(
        snapshot: &impl ReadableSnapshot,
        interface_type: IMPL::InterfaceType,
    ) -> Result<HashMap<ObjectType<'static>, IMPL>, ConceptReadError>
    where
        IMPL: InterfaceImplementation<'static, ObjectType = ObjectType<'static>> + Hash + Eq,
    {
        let mut impl_transitive: HashMap<ObjectType<'static>, IMPL> = HashMap::new();
        let declared_impl_set: HashSet<IMPL> =
            Self::get_implementations_for_interface_declared(snapshot, interface_type.clone())?;

        for declared_impl in declared_impl_set {
            let mut stack = Vec::new();
            stack.push(declared_impl.object());
            while let Some(sub_object) = stack.pop() {
                let mut declared_impl_was_overridden = false;
                for sub_owner_owns in Self::get_implemented_interfaces_declared::<IMPL>(snapshot, sub_object.clone())? {
                    if let Some(overridden_impl) = Self::get_implementation_override(snapshot, sub_owner_owns.clone())?
                    {
                        declared_impl_was_overridden =
                            declared_impl_was_overridden || overridden_impl.interface() == interface_type;
                    }
                }
                if !declared_impl_was_overridden {
                    debug_assert!(!impl_transitive.contains_key(&sub_object));
                    impl_transitive.insert(sub_object.clone(), declared_impl.clone());
                    match sub_object {
                        ObjectType::Entity(owner) => Self::get_subtypes(snapshot, owner)?
                            .into_iter()
                            .for_each(|t| stack.push(ObjectType::new(t.into_vertex()))),
                        ObjectType::Relation(owner) => Self::get_subtypes(snapshot, owner)?
                            .into_iter()
                            .for_each(|t| stack.push(ObjectType::new(t.into_vertex()))),
                    };
                }
            }
        }
        Ok(impl_transitive)
    }

    pub(crate) fn get_relates_declared(
        snapshot: &impl ReadableSnapshot,
        relation: RelationType<'static>,
    ) -> Result<HashSet<Relates<'static>>, ConceptReadError> {
        let relates_prefix = Relates::prefix_for_canonical_edges_from(relation);
        snapshot
            .iterate_range(KeyRange::new_within(relates_prefix, TypeEdge::FIXED_WIDTH_ENCODING))
            .collect_cloned_hashset(|key, _| {
                Relates::decode_canonical_edge(Bytes::Reference(key.byte_ref()).into_owned())
            })
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_relates(
        snapshot: &impl ReadableSnapshot,
        relation: RelationType<'static>,
    ) -> Result<HashMap<RoleType<'static>, Relates<'static>>, ConceptReadError> {
        let mut transitive_relates: HashMap<RoleType<'static>, Relates<'static>> = HashMap::new();
        let mut overridden_relates: HashSet<RoleType<'static>> = HashSet::new();
        let mut current_relation = Some(relation);
        while current_relation.is_some() {
            let declared_relates = Self::get_relates_declared(snapshot, current_relation.as_ref().unwrap().clone())?;
            for relates in declared_relates.into_iter() {
                let role = relates.role();
                if !overridden_relates.contains(&role) {
                    debug_assert!(!transitive_relates.contains_key(&role));
                    transitive_relates.insert(role, relates.clone());
                }
                if let Some(overridden) = Self::get_supertype(snapshot, relates.role().clone())? {
                    overridden_relates.add(overridden);
                }
            }
            current_relation = Self::get_supertype(snapshot, current_relation.unwrap())?;
        }
        Ok(transitive_relates)
    }

    pub(crate) fn get_role_type_relates(
        snapshot: &impl ReadableSnapshot,
        role: RoleType<'static>,
    ) -> Result<Relates<'static>, ConceptReadError> {
        let relates_prefix = Relates::prefix_for_reverse_edges_from(role);
        snapshot
            .iterate_range(KeyRange::new_within(relates_prefix, TypeEdge::FIXED_WIDTH_ENCODING))
            .collect_cloned_vec(|key, _| Relates::decode_reverse_edge(Bytes::Reference(key.byte_ref()).into_owned()))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
            .map(|v| v.first().unwrap().clone())
    }

    pub(crate) fn get_value_type(
        snapshot: &impl ReadableSnapshot,
        type_: AttributeType<'_>,
    ) -> Result<Option<ValueType>, ConceptReadError> {
        Self::get_type_property::<ValueType>(snapshot, type_)
    }

    pub(crate) fn get_type_property<'a, PROPERTY>(
        snapshot: &impl ReadableSnapshot,
        type_: impl TypeVertexEncoding<'a>,
    ) -> Result<Option<PROPERTY>, ConceptReadError>
    where
        PROPERTY: TypeVertexPropertyEncoding<'static>,
    {
        let property = snapshot
            .get_mapped(PROPERTY::build_key(type_).into_storage_key().as_reference(), |value| {
                PROPERTY::from_value_bytes(value.clone())
            })
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })?;
        Ok(property)
    }

    pub(crate) fn get_type_ordering(
        snapshot: &impl ReadableSnapshot,
        role_type: RoleType<'_>,
    ) -> Result<Ordering, ConceptReadError> {
        Ok(Self::get_type_property(snapshot, role_type)?.unwrap())
    }

    pub(crate) fn get_type_annotations_declared<T: KindAPI<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_: T,
    ) -> Result<HashSet<T::AnnotationType>, ConceptReadError> {
        snapshot
            .iterate_range(KeyRange::new_inclusive(
                TypeVertexProperty::build(type_.vertex(), Infix::ANNOTATION_MIN).into_storage_key(),
                TypeVertexProperty::build(type_.vertex(), Infix::ANNOTATION_MAX).into_storage_key(),
            ))
            .collect_cloned_hashset(|key, value| {
                let annotation_key = TypeVertexProperty::new(Bytes::Reference(key.byte_ref()));
                let annotation = match annotation_key.infix() {
                    Infix::PropertyAnnotationAbstract => Annotation::Abstract(AnnotationAbstract),
                    Infix::PropertyAnnotationDistinct => Annotation::Distinct(AnnotationDistinct),
                    Infix::PropertyAnnotationIndependent => Annotation::Independent(AnnotationIndependent),
                    Infix::PropertyAnnotationCardinality => Annotation::Cardinality(
                        <AnnotationCardinality as TypeVertexPropertyEncoding>::from_value_bytes(value),
                    ),
                    Infix::PropertyAnnotationRegex => Annotation::Regex(
                        <AnnotationRegex as TypeVertexPropertyEncoding>::from_value_bytes(value),
                    ),
                    | Infix::_PropertyAnnotationLast
                    | Infix::PropertyAnnotationUnique
                    | Infix::PropertyAnnotationKey
                    | Infix::PropertyLabel
                    | Infix::PropertyValueType
                    | Infix::PropertyOrdering
                    | Infix::PropertyOverride
                    | Infix::PropertyHasOrder
                    | Infix::PropertyRolePlayerOrder => {
                        unreachable!("Retrieved unexpected infixes while reading annotations.")
                    }
                };
                T::AnnotationType::from(annotation)
            })
            .map_err(|err| ConceptReadError::SnapshotIterate { source: err.clone() })
    }

    pub(crate) fn get_type_annotations<T: KindAPI<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_: T,
    ) -> Result<HashSet<T::AnnotationType>, ConceptReadError> {
        // let mut effective_annotations: HashMap<T::AnnotationType, T> = HashMap::new();
        let mut annotations: HashSet<T::AnnotationType> = HashSet::new();
        let mut type_opt = Some(type_);
        while let Some(next_type) = type_opt {
            let declared_annotations = Self::get_type_annotations_declared(snapshot, next_type.clone())?;
            for annotation in declared_annotations {
                // TODO: Rename???? What to check???
                if is_annotation_inherited::<T>(&annotation, &annotations) {
                    // annotations.insert(annotation, next_type.clone());
                    annotations.insert(annotation);
                }
            }
            type_opt = Self::get_supertype(snapshot, next_type.clone())?;
        }
        Ok(annotations)
    }

    // TODO: this is currently breaking our architectural pattern that none of the Manager methods should operate graphs
    pub(crate) fn get_type_edge_annotations_declared<EDGE>(
        snapshot: &impl ReadableSnapshot,
        edge: EDGE,
    ) -> Result<HashSet<Annotation>, ConceptReadError>
    where
        EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static>,
    {
        let type_edge = edge.to_canonical_type_edge();
        snapshot
            .iterate_range(KeyRange::new_inclusive(
                TypeEdgeProperty::build(type_edge.clone(), Infix::ANNOTATION_MIN).into_storage_key(),
                TypeEdgeProperty::build(type_edge, Infix::ANNOTATION_MAX).into_storage_key(),
            ))
            .collect_cloned_hashset(|key, value| {
                let annotation_key = TypeEdgeProperty::new(Bytes::Reference(key.byte_ref()));
                match annotation_key.infix() {
                    Infix::PropertyAnnotationDistinct => Annotation::Distinct(AnnotationDistinct),
                    Infix::PropertyAnnotationIndependent => Annotation::Independent(AnnotationIndependent),
                    Infix::PropertyAnnotationUnique => Annotation::Unique(AnnotationUnique),
                    Infix::PropertyAnnotationKey => Annotation::Key(AnnotationKey),
                    Infix::PropertyAnnotationCardinality => Annotation::Cardinality(
                        <AnnotationCardinality as TypeEdgePropertyEncoding>::from_value_bytes(value),
                    ),
                    Infix::PropertyAnnotationRegex => Annotation::Regex(
                        <AnnotationRegex as TypeEdgePropertyEncoding>::from_value_bytes(value),
                    ),
                    | Infix::_PropertyAnnotationLast
                    | Infix::PropertyAnnotationAbstract
                    | Infix::PropertyLabel
                    | Infix::PropertyValueType
                    | Infix::PropertyOrdering
                    | Infix::PropertyOverride
                    | Infix::PropertyHasOrder
                    | Infix::PropertyRolePlayerOrder => {
                        unreachable!("Retrieved unexpected infixes while reading annotations.")
                    }
                }
            })
            .map_err(|err| ConceptReadError::SnapshotIterate { source: err.clone() })
    }

    pub(crate) fn get_type_edge_annotations<EDGE>(
        snapshot: &impl ReadableSnapshot,
        edge: EDGE,
    ) -> Result<HashMap<Annotation, EDGE>, ConceptReadError>
    where
        EDGE: TypeEdgeEncoding<'static> + InterfaceImplementation<'static>,
    {
        let mut annotations: HashMap<Annotation, EDGE> = HashMap::new();
        let mut edge_opt = Some(edge);
        while let Some(edge) = edge_opt {
            let declared_edge_annotations = Self::get_type_edge_annotations_declared(snapshot, edge.clone())?;
            for annotation in declared_edge_annotations {
                if is_edge_annotation_inherited(&annotation, &annotations) {
                    annotations.insert(annotation, edge.clone());
                }
            }
            edge_opt = Self::get_implementation_override(snapshot, edge.clone())?;
        }
        Ok(annotations)
    }

    pub(crate) fn get_type_edge_ordering(
        snapshot: &impl ReadableSnapshot,
        owns: Owns<'_>,
    ) -> Result<Ordering, ConceptReadError> {
        Ok(Self::get_type_edge_property::<Ordering>(snapshot, owns)?.unwrap())
    }

    pub(crate) fn get_type_edge_property<'a, PROPERTY>(
        snapshot: &impl ReadableSnapshot,
        edge: impl TypeEdgeEncoding<'a>,
    ) -> Result<Option<PROPERTY>, ConceptReadError>
    where
        PROPERTY: TypeEdgePropertyEncoding<'static>,
    {
        let property = snapshot
            .get_mapped(PROPERTY::build_key(edge).into_storage_key().as_reference(), |value| {
                PROPERTY::from_value_bytes(value)
            })
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })?;
        Ok(property)
    }
}
