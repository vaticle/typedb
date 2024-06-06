/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    marker::PhantomData,
    sync::atomic::{AtomicU64, Ordering::Relaxed},
};

use bytes::Bytes;
use lending_iterator::LendingIterator;
use resource::constants::{encoding::DefinitionIDUInt, snapshot::BUFFER_KEY_INLINE};
use storage::{key_range::KeyRange, key_value::StorageKey, snapshot::WritableSnapshot};

use crate::{
    error::EncodingError,
    graph::{
        definition::definition_key::{DefinitionID, DefinitionKey},
        type_::{
            vertex::{TypeID, TypeIDUInt, TypeVertex},
            Kind,
        },
        Typed,
    },
    layout::prefix::Prefix,
    Keyable,
};

pub type TypeVertexAllocator = SchemaIDAllocator<TypeVertex<'static>>;
pub type DefinitionKeyAllocator = SchemaIDAllocator<DefinitionKey<'static>>;

pub trait SchemaID: Sized {
    const MIN_ID: u64;
    const MAX_ID: u64;

    fn object_from_id(prefix: Prefix, id: u64) -> Self;
    fn id_from_key(key: StorageKey<'_, BUFFER_KEY_INLINE>) -> u64;
    fn ids_exhausted_error(prefix: Prefix) -> EncodingError;
}

pub struct SchemaIDAllocator<T: SchemaID> {
    last_allocated_type_id: AtomicU64,
    prefix: Prefix,
    phantom: PhantomData<T>,
}

impl<'a, T: SchemaID + Keyable<'a, BUFFER_KEY_INLINE>> SchemaIDAllocator<T> {
    pub fn new(prefix: Prefix) -> Self {
        Self { last_allocated_type_id: AtomicU64::new(0), prefix, phantom: PhantomData }
    }

    fn find_unallocated_id<Snapshot: WritableSnapshot>(
        &self,
        snapshot: &mut Snapshot,
        start: u64,
    ) -> Result<Option<u64>, EncodingError> {
        let mut schema_object_iter = snapshot.iterate_range(KeyRange::new_inclusive(
            T::object_from_id(self.prefix, start).into_storage_key(),
            T::object_from_id(self.prefix, T::MAX_ID).into_storage_key(),
        ));
        for expected_next_id in start..=T::MAX_ID {
            match schema_object_iter.next() {
                None => return Ok(Some(expected_next_id)),
                Some(Err(err)) => {
                    return Err(EncodingError::SchemaIDAllocate { source: err.clone() });
                }
                Some(Ok((actual_next_key, _))) => {
                    let actual_id = T::id_from_key(actual_next_key);
                    if actual_id != expected_next_id {
                        return Ok(Some(expected_next_id));
                    }
                }
            }
        }
        Ok(None)
    }

    pub fn allocate<Snapshot: WritableSnapshot>(&self, snapshot: &mut Snapshot) -> Result<T, EncodingError> {
        let found = self.find_unallocated_id(snapshot, self.last_allocated_type_id.load(Relaxed))?;
        if let Some(allocated_id) = found {
            self.last_allocated_type_id.store(allocated_id, Relaxed);
            Ok(T::object_from_id(self.prefix, allocated_id))
        } else {
            match self.find_unallocated_id(snapshot, 0)? {
                None => Err(T::ids_exhausted_error(self.prefix)),
                Some(allocated_id) => {
                    self.last_allocated_type_id.store(allocated_id, Relaxed);
                    Ok(T::object_from_id(self.prefix, allocated_id))
                }
            }
        }
    }
}

impl SchemaID for TypeVertex<'static> {
    const MIN_ID: u64 = TypeIDUInt::MIN as u64;
    const MAX_ID: u64 = TypeIDUInt::MAX as u64;

    fn object_from_id(prefix: Prefix, id: u64) -> TypeVertex<'static> {
        debug_assert!((Self::MIN_ID..=Self::MAX_ID).contains(&id));
        TypeVertex::build(prefix.prefix_id(), TypeID::build(id as TypeIDUInt))
    }

    fn id_from_key(key: StorageKey<'_, BUFFER_KEY_INLINE>) -> u64 {
        TypeVertex::new(Bytes::reference(key.bytes())).type_id_().as_u16() as u64
    }

    fn ids_exhausted_error(prefix: Prefix) -> EncodingError {
        let kind = match prefix {
            Prefix::VertexEntityType => Kind::Entity,
            Prefix::VertexRelationType => Kind::Relation,
            Prefix::VertexAttributeType => Kind::Attribute,
            Prefix::VertexRoleType => Kind::Role,
            _ => unreachable!(),
        };
        EncodingError::TypeIDsExhausted { kind }
    }
}

impl SchemaID for DefinitionKey<'static> {
    const MIN_ID: u64 = DefinitionIDUInt::MIN as u64;
    const MAX_ID: u64 = DefinitionIDUInt::MAX as u64;

    fn object_from_id(prefix: Prefix, id: u64) -> Self {
        debug_assert!((Self::MIN_ID..=Self::MAX_ID).contains(&id));
        DefinitionKey::build(prefix, DefinitionID::build(id as DefinitionIDUInt))
    }

    fn id_from_key(key: StorageKey<'_, BUFFER_KEY_INLINE>) -> u64 {
        DefinitionKey::new(Bytes::reference(key.bytes())).definition_id().as_uint() as u64
    }

    fn ids_exhausted_error(prefix: Prefix) -> EncodingError {
        EncodingError::DefinitionIDsExhausted { prefix }
    }
}
