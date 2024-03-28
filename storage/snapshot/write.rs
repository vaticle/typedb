/*
 * Copyright (C) 2023 Vaticle
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

use bytes::byte_array::ByteArray;
use resource::constants::snapshot::BUFFER_VALUE_INLINE;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub(crate) enum Write {
    // Mark Key as required from storage. Caches existing storage Value. Conflicts with Delete.
    RequireExists { value: ByteArray<BUFFER_VALUE_INLINE> },
    // Insert KeyValue with a new version. Never conflicts.
    Insert { value: ByteArray<BUFFER_VALUE_INLINE> },
    // Insert KeyValue with new version if a concurrent Txn deletes Key. Boolean indicates requires re-insertion. Never conflicts.
    InsertPreexisting { value: ByteArray<BUFFER_VALUE_INLINE>, reinsert: Arc<AtomicBool> },
    // Delete with a new version. Conflicts with Require.
    Delete,
}

impl PartialEq for Write {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::RequireExists { value }, Self::RequireExists { value: other_value }) => value == other_value,
            (Self::Insert { value }, Self::Insert { value: other_value }) => value == other_value,
            (
                Self::InsertPreexisting { value, reinsert },
                Self::InsertPreexisting { value: other_value, reinsert: other_reinsert },
            ) => other_value == value && reinsert.load(Ordering::Acquire) == other_reinsert.load(Ordering::Acquire),
            (Self::Delete, Self::Delete) => true,
            _ => false,
        }
    }
}

impl Eq for Write {}

impl Write {
    pub(crate) fn is_insert(&self) -> bool {
        matches!(self, Write::Insert { .. })
    }

    pub(crate) fn is_insert_preexisting(&self) -> bool {
        matches!(self, Write::InsertPreexisting { .. })
    }

    pub(crate) fn is_delete(&self) -> bool {
        matches!(self, Write::Delete)
    }

    pub(crate) fn get_value(&self) -> &ByteArray<BUFFER_VALUE_INLINE> {
        match self {
            Write::Insert { value } | Write::InsertPreexisting { value, .. } | Write::RequireExists { value } => value,
            Write::Delete => panic!("Buffered delete does not have a value."),
        }
    }
}
