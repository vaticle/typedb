/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::cmp::Ordering;

use bytes::Bytes;
use encoding::{
    graph::{
        thing::{edge::ThingEdgeHasReverse, vertex_attribute::AttributeVertex},
        type_::vertex::build_vertex_attribute_type,
        Typed,
    },
    value::{decode_value_u64, value_type::ValueType},
    AsBytes, Keyable,
};
use iterator::State;
use storage::{
    key_value::StorageKeyReference,
    snapshot::{iterator::SnapshotRangeIterator, ReadableSnapshot, WriteSnapshot},
};

use crate::{
    edge_iterator,
    error::{ConceptReadError, ConceptWriteError},
    thing::{object::Object, thing_manager::ThingManager, value::Value, ThingAPI},
    type_::{attribute_type::AttributeType, type_manager::TypeManager},
    ByteReference, ConceptAPI, ConceptStatus,
};

#[derive(Debug, Clone)]
pub struct Attribute<'a> {
    vertex: AttributeVertex<'a>,
    value: Option<Value<'a>>, // TODO: if we end up doing traversals over Vertex instead of Concept, we could embed the Value cache into the AttributeVertex
}

impl<'a> Attribute<'a> {
    pub(crate) fn new(vertex: AttributeVertex<'a>) -> Self {
        Attribute { vertex, value: None }
    }

    pub(crate) fn value_type(&self) -> ValueType {
        self.vertex.value_type()
    }

    pub fn type_(&self) -> AttributeType<'static> {
        AttributeType::new(build_vertex_attribute_type(self.vertex.type_id_()))
    }

    pub fn iid(&self) -> ByteReference<'_> {
        self.vertex.bytes()
    }

    pub fn get_value(
        &mut self,
        thing_manager: &ThingManager<impl ReadableSnapshot>,
    ) -> Result<Value<'_>, ConceptReadError> {
        if self.value.is_none() {
            let value = thing_manager.get_attribute_value(self)?;
            self.value = Some(value);
        }
        Ok(self.value.as_ref().unwrap().as_reference())
    }

    pub fn has_owners<'m>(&self, thing_manager: &'m ThingManager<impl ReadableSnapshot>) -> bool {
        match self.get_status(thing_manager) {
            ConceptStatus::Put | ConceptStatus::Persisted => thing_manager.has_owners(self.as_reference(), false),
            ConceptStatus::Inserted | ConceptStatus::Deleted => {
                unreachable!("Attributes are expected to always have a PUT status.")
            }
        }
    }

    pub fn get_owners<'m>(
        &self,
        thing_manager: &'m ThingManager<impl ReadableSnapshot>,
    ) -> AttributeOwnerIterator<'m, { ThingEdgeHasReverse::LENGTH_BOUND_PREFIX_FROM }> {
        thing_manager.get_owners(self.as_reference())
    }

    pub fn as_reference(&self) -> Attribute<'_> {
        Attribute { vertex: self.vertex.as_reference(), value: self.value.as_ref().map(|value| value.as_reference()) }
    }

    pub(crate) fn vertex<'this: 'a>(&'this self) -> AttributeVertex<'this> {
        self.vertex.as_reference()
    }

    pub(crate) fn into_vertex(self) -> AttributeVertex<'a> {
        self.vertex
    }

    pub fn into_owned(self) -> Attribute<'static> {
        Attribute::new(self.vertex.into_owned())
    }
}

impl<'a> ConceptAPI<'a> for Attribute<'a> {}

impl<'a> ThingAPI<'a> for Attribute<'a> {
    fn set_modified<D>(&self, thing_manager: &ThingManager<WriteSnapshot<D>>) {
        debug_assert_eq!(thing_manager.get_status(self.vertex().as_storage_key()), ConceptStatus::Put);
        // Attributes are always PUT, so we don't have to record a lock on modification
    }

    fn get_status<'m>(&self, thing_manager: &'m ThingManager<impl ReadableSnapshot>) -> ConceptStatus {
        thing_manager.get_status(self.vertex().as_storage_key())
    }

    fn errors<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
    ) -> Result<Vec<ConceptWriteError>, ConceptReadError> {
        Ok(Vec::new())
    }

    fn delete<D>(self, thing_manager: &ThingManager<WriteSnapshot<D>>) -> Result<(), ConceptWriteError> {
        let mut owner_iter = self.get_owners(thing_manager);
        let mut owner = owner_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        while let Some((object, count)) = owner {
            object.delete_has_many(thing_manager, self.as_reference(), count)?;
            owner = owner_iter.next().transpose().map_err(|err| ConceptWriteError::ConceptRead { source: err })?;
        }

        thing_manager.delete_attribute(self);
        Ok(())
    }
}

impl<'a> PartialEq<Self> for Attribute<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.vertex().eq(&other.vertex())
    }
}

impl<'a> Eq for Attribute<'a> {}

impl<'a> PartialOrd<Self> for Attribute<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> Ord for Attribute<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.vertex.cmp(&other.vertex())
    }
}

///
/// Attribute iterators handle hiding dependent attributes that were not deleted yet
///
pub struct AttributeIterator<'a, Snapshot: ReadableSnapshot, const A_PS: usize, const H_PS: usize> {
    type_manager: Option<&'a TypeManager<Snapshot>>,
    attributes_iterator: Option<SnapshotRangeIterator<'a, A_PS>>,
    has_reverse_iterator: Option<SnapshotRangeIterator<'a, H_PS>>,
    state: State<ConceptReadError>,
}

impl<'a, Snapshot: ReadableSnapshot, const A_PS: usize, const H_PS: usize> AttributeIterator<'a, Snapshot, A_PS, H_PS> {
    pub(crate) fn new(
        attributes_iterator: SnapshotRangeIterator<'a, A_PS>,
        has_reverse_iterator: SnapshotRangeIterator<'a, H_PS>,
        type_manager: &'a TypeManager<Snapshot>,
    ) -> Self {
        Self {
            type_manager: Some(type_manager),
            attributes_iterator: Some(attributes_iterator),
            has_reverse_iterator: Some(has_reverse_iterator),
            state: State::Init,
        }
    }

    pub(crate) fn new_empty() -> Self {
        Self { type_manager: None, attributes_iterator: None, has_reverse_iterator: None, state: State::Done }
    }

    fn storage_key_to_attribute_vertex<'b>(storage_key_ref: StorageKeyReference<'b>) -> AttributeVertex<'b> {
        AttributeVertex::new(Bytes::Reference(storage_key_ref.byte_ref()))
    }

    pub fn peek(&mut self) -> Option<Result<Attribute<'_>, ConceptReadError>> {
        self.iter_peek().map(|result| {
            result.map(|(storage_key, _value_bytes)| Attribute::new(Self::storage_key_to_attribute_vertex(storage_key)))
        })
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Result<Attribute<'_>, ConceptReadError>> {
        self.iter_next().map(|result| {
            result.map(|(storage_key, _value_bytes)| Attribute::new(Self::storage_key_to_attribute_vertex(storage_key)))
        })
    }

    pub fn seek(&mut self) {
        todo!()
    }

    fn iter_peek(&mut self) -> Option<Result<(StorageKeyReference<'_>, ByteReference<'_>), ConceptReadError>> {
        match &self.state {
            State::Init | State::ItemUsed => {
                self.find_next_state();
                self.iter_peek()
            }
            State::ItemReady => self
                .attributes_iterator
                .as_mut()
                .unwrap()
                .peek()
                .transpose()
                .map_err(|err| ConceptReadError::SnapshotIterate { source: err.clone() })
                .transpose(),
            State::Error(error) => Some(Err(error.clone())),
            State::Done => None,
        }
    }

    fn iter_next(&mut self) -> Option<Result<(StorageKeyReference<'_>, ByteReference<'_>), ConceptReadError>> {
        match &self.state {
            State::Init | State::ItemUsed => {
                self.find_next_state();
                self.iter_next()
            }
            State::ItemReady => {
                let next = self
                    .attributes_iterator
                    .as_mut()
                    .unwrap()
                    .next()
                    .transpose()
                    .map_err(|err| ConceptReadError::SnapshotIterate { source: err.clone() })
                    .transpose();
                let _ = self.has_reverse_iterator.as_mut().unwrap().next();
                self.state = State::ItemUsed;
                next
            }
            State::Error(error) => Some(Err(error.clone())),
            State::Done => None,
        }
    }

    fn find_next_state(&mut self) {
        assert!(matches!(&self.state, State::Init | State::ItemUsed));
        while matches!(&self.state, State::Init | State::ItemUsed) {
            let mut advance_attribute = false;
            match self.attributes_iterator.as_mut().unwrap().peek() {
                None => self.state = State::Done,
                Some(Ok((key, _))) => {
                    let attribute_vertex = Self::storage_key_to_attribute_vertex(key);
                    let independent = Attribute::new(attribute_vertex.as_reference())
                        .type_()
                        .is_independent(self.type_manager.as_ref().unwrap());
                    match independent {
                        Ok(true) => self.state = State::ItemReady,
                        Ok(false) => {
                            match Self::has_owner(self.has_reverse_iterator.as_mut().unwrap(), attribute_vertex) {
                                Ok(has_owner) => {
                                    if has_owner {
                                        self.state = State::ItemReady
                                    } else {
                                        advance_attribute = true
                                    }
                                }
                                Err(err) => self.state = State::Error(err),
                            }
                        }
                        Err(err) => self.state = State::Error(err.clone()),
                    }
                }
                Some(Err(err)) => self.state = State::Error(ConceptReadError::SnapshotIterate { source: err.clone() }),
            }
            if advance_attribute {
                let _ = self.attributes_iterator.as_mut().unwrap();
            }
        }
    }

    fn has_owner(
        has_reverse_iterator: &mut SnapshotRangeIterator<'a, H_PS>,
        attribute_vertex: AttributeVertex<'_>,
    ) -> Result<bool, ConceptReadError> {
        let has_reverse_prefix = ThingEdgeHasReverse::prefix_from_attribute(attribute_vertex.as_reference());
        has_reverse_iterator.seek(has_reverse_prefix.as_reference());
        match has_reverse_iterator.peek() {
            None => Ok(false),
            Some(Err(err)) => Err(ConceptReadError::SnapshotIterate { source: err.clone() }),
            Some(Ok((bytes, _))) => {
                let edge = ThingEdgeHasReverse::new(Bytes::Reference(bytes.byte_ref()));
                let edge_from = edge.from();
                match edge_from.cmp(&attribute_vertex) {
                    Ordering::Less => {
                        panic!("Unexpected attribute edge encountered for a previous attribute, which should not be possible.");
                    }
                    Ordering::Equal => Ok(true),
                    Ordering::Greater => Ok(false),
                }
            }
        }
    }

    pub fn collect_cloned(mut self) -> Vec<Attribute<'static>> {
        let mut vec = Vec::new();
        loop {
            let item = self.next();
            if item.is_none() {
                break;
            }
            let key = item.unwrap().unwrap().into_owned();
            vec.push(key);
        }
        vec
    }
}

fn storage_key_to_owner<'a>(
    storage_key_reference: StorageKeyReference<'a>,
    value: ByteReference<'a>,
) -> (Object<'a>, u64) {
    let edge = ThingEdgeHasReverse::new(Bytes::Reference(storage_key_reference.byte_ref()));
    (Object::new(edge.into_to()), decode_value_u64(value))
}

edge_iterator!(
    AttributeOwnerIterator;
    (Object<'_>, u64);
    storage_key_to_owner
);
