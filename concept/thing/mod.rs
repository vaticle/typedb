/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use bytes::{byte_array::ByteArray, Bytes};
use encoding::{
    graph::thing::{vertex_attribute::AttributeID, vertex_object::ObjectVertex},
    value::value_type::ValueTypeCategory,
    AsBytes,
};
use resource::constants::snapshot::BUFFER_VALUE_INLINE;
use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    thing::thing_manager::ThingManager,
    ConceptStatus,
};

pub mod attribute;
pub mod entity;
pub mod object;
pub mod relation;
pub mod statistics;
pub mod thing_manager;

pub trait ThingAPI<'a> {
    fn set_modified(&self, snapshot: &mut impl WritableSnapshot, thing_manager: &ThingManager);

    // TODO: implementers could cache the status in a OnceCell if we do many operations on the same Thing at once
    fn get_status(&self, snapshot: &impl ReadableSnapshot, thing_manager: &ThingManager) -> ConceptStatus;

    fn errors(
        &self,
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
    ) -> Result<Vec<ConceptWriteError>, ConceptReadError>;

    fn delete(
        self,
        snapshot: &mut impl WritableSnapshot,
        thing_manager: &ThingManager,
    ) -> Result<(), ConceptWriteError>;
}

// TODO: where do these belong? They're encodings of values we store for keys
pub(crate) fn decode_attribute_ids(
    value_type_category: ValueTypeCategory,
    bytes: &[u8],
) -> impl Iterator<Item = AttributeID> + '_ {
    let chunk_size = AttributeID::value_type_encoding_length(value_type_category);
    let chunks_iter = bytes.chunks_exact(chunk_size);
    debug_assert!(chunks_iter.remainder().is_empty());
    chunks_iter.map(move |chunk| AttributeID::new(value_type_category, chunk))
}

pub(crate) fn encode_attribute_ids(
    value_type_category: ValueTypeCategory,
    attribute_ids: impl Iterator<Item = AttributeID>,
) -> ByteArray<BUFFER_VALUE_INLINE> {
    let chunk_size = AttributeID::value_type_encoding_length(value_type_category);
    let (lower, upper) = attribute_ids.size_hint();
    let size_hint = upper.unwrap_or(lower) * chunk_size;
    let mut bytes = Vec::with_capacity(size_hint);
    for attribute_id in attribute_ids {
        bytes.extend(attribute_id.bytes());
    }
    // TODO allow inline?
    ByteArray::boxed(bytes.into())
}

pub(crate) fn decode_role_players(bytes: &[u8]) -> impl Iterator<Item = ObjectVertex<'_>> + '_ {
    let chunk_size = ObjectVertex::LENGTH;
    let chunks_iter = bytes.chunks_exact(chunk_size);
    debug_assert!(chunks_iter.remainder().is_empty());
    chunks_iter.map(move |chunk| ObjectVertex::new(Bytes::reference(chunk)))
}

pub(crate) fn encode_role_players<'a>(
    players: impl Iterator<Item = ObjectVertex<'a>>,
) -> ByteArray<BUFFER_VALUE_INLINE> {
    let chunk_size = ObjectVertex::LENGTH;
    let (lower, upper) = players.size_hint();
    let size_hint = upper.unwrap_or(lower) * chunk_size;
    let mut bytes = Vec::with_capacity(size_hint);
    for player in players {
        bytes.extend(player.bytes().bytes());
    }
    // TODO allow inline?
    ByteArray::boxed(bytes.into())
}
