/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{hash_map::Entry, HashMap};

use bytes::{byte_reference::ByteReference, Bytes};
use resource::constants::{encoding::StructFieldIDUInt, snapshot::BUFFER_VALUE_INLINE};
use serde::{Deserialize, Serialize};

use crate::{
    error::EncodingError, graph::definition::DefinitionValueEncoding, layout::prefix::Prefix,
    value::value_type::ValueType,
};

#[derive(Serialize, Deserialize, Debug, Clone, Eq, PartialEq)]
pub struct StructDefinition {
    pub name: String,
    pub fields: HashMap<StructFieldIDUInt, StructDefinitionField>,
    pub field_names: HashMap<String, StructFieldIDUInt>,
}

#[derive(Serialize, Deserialize, Debug, Clone, Eq, PartialEq)]
pub struct StructDefinitionField {
    pub index: StructFieldIDUInt,
    pub optional: bool,
    pub value_type: ValueType,
}

impl StructDefinition {
    pub const PREFIX: Prefix = Prefix::DefinitionStruct;

    pub fn new(name: String) -> StructDefinition {
        StructDefinition { name, fields: HashMap::new(), field_names: HashMap::new() }
    }

    pub fn add_field(
        &mut self,
        field_name: String,
        value_type: ValueType,
        optional: bool,
    ) -> Result<(), EncodingError> {
        if self.fields.len() > StructFieldIDUInt::MAX as usize {
            Err(EncodingError::StructAlreadyHasMaximumNumberOfFields { struct_name: self.name.clone() })
        } else {
            match self.field_names.entry(field_name) {
                Entry::Vacant(entry) => {
                    let index = (0..self.fields.len() as StructFieldIDUInt)
                        .find(|idx| !self.fields.contains_key(idx))
                        .unwrap_or(self.fields.len() as StructFieldIDUInt);
                    self.fields.insert(index, StructDefinitionField { index, optional, value_type });
                    entry.insert(index);
                    Ok(())
                }
                Entry::Occupied(entry) => Err(EncodingError::StructDuplicateFieldDefinition {
                    struct_name: self.name.clone(),
                    field_name: entry.key().clone(),
                }),
            }
        }
    }

    pub fn delete_field(&mut self, field_name: String) -> Result<(), EncodingError> {
        if !self.field_names.contains_key(&field_name) {
            Err(EncodingError::StructFieldUnresolvable { struct_name: self.name.clone(), field_path: vec![field_name] })
        } else {
            let field_idx = self.field_names.remove(&field_name).unwrap();
            self.fields.remove(&field_idx).unwrap();
            Ok(())
        }
    }
}

impl DefinitionValueEncoding for StructDefinition {
    fn from_bytes<'b>(value: ByteReference<'b>) -> Self {
        bincode::deserialize(value.bytes()).unwrap()
    }

    fn into_bytes(self) -> Option<Bytes<'static, BUFFER_VALUE_INLINE>> {
        Some(Bytes::copy(bincode::serialize(&self).unwrap().as_slice()))
    }
}
