/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use bytes::byte_array::ByteArray;
use encoding::{
    graph::thing::{vertex_attribute::AttributeID, vertex_object::ObjectVertex},
    value::value_type::ValueType,
};
use resource::constants::snapshot::BUFFER_VALUE_INLINE;
use storage::snapshot::{ReadableSnapshot, WriteSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    thing::thing_manager::ThingManager,
    ConceptStatus,
};

pub mod attribute;
pub mod entity;
pub mod object;
pub mod relation;
pub mod thing_manager;
pub mod value;

pub trait ThingAPI<'a> {
    fn set_modified<D>(&self, thing_manager: &ThingManager<WriteSnapshot<D>>);

    // TODO: implementers could cache the status in a OnceCell if we do many operations on the same Thing at once
    fn get_status<'m>(&self, thing_manager: &'m ThingManager<impl ReadableSnapshot>) -> ConceptStatus;

    fn errors<D>(
        &self,
        thing_manager: &ThingManager<WriteSnapshot<D>>,
    ) -> Result<Vec<ConceptWriteError>, ConceptReadError>;

    fn delete<D>(self, thing_manager: &ThingManager<WriteSnapshot<D>>) -> Result<(), ConceptWriteError>;
}

pub trait ObjectAPI<'a>: ThingAPI<'a> {
    fn vertex(&self) -> ObjectVertex<'_>;

    fn into_vertex(self) -> ObjectVertex<'a>;
}

// TODO: where do these belong? They're encodings of values we store for keys
pub(crate) fn decode_attribute_ids(value_type: ValueType, bytes: &[u8]) -> impl Iterator<Item = AttributeID> + '_ {
    let chunk_size = AttributeID::value_type_encoding_length(value_type);
    let chunks_iter = bytes.chunks_exact(chunk_size);
    debug_assert!(chunks_iter.remainder().is_empty());
    chunks_iter.map(move |chunk| AttributeID::new(value_type, chunk))
}

pub(crate) fn encode_attribute_ids(
    attribute_ids: impl Iterator<Item = AttributeID>,
) -> ByteArray<{ BUFFER_VALUE_INLINE }> {
    todo!()
}
