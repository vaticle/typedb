/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashMap;

use encoding::graph::definition::definition_key::DefinitionKey;
use resource::constants::encoding::StructFieldIDUInt;

use crate::thing::value::Value;

#[derive(Debug, Clone, PartialEq)]
pub struct StructValue<'a> {
    definition: DefinitionKey<'static>,

    // a map allows empty fields to not be recorded at all
    fields: HashMap<StructFieldIDUInt, Value<'a>>,
}

impl<'a> StructValue<'a> {
    pub fn definition_key(&self) -> DefinitionKey<'_> {
        self.definition.as_reference()
    }
}

// TODO: implement serialise/deserialise for the StructValue
//       since JSON serialisation seems to be able to handle recursive nesting, it should be able to handle that
