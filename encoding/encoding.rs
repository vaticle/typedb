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
 *
 */

pub mod thing;
pub mod type_;

use storage::key::Keyable;

pub enum Prefix {
    ENTITY_TYPE,
    ATTRIBUTE_TYPE,

    ENTITY,
    ATTRIBUTE
}

impl Keyable for Prefix {
    fn bytes(&self) -> &[u8] {
        match self {
            Prefix::ENTITY_TYPE => &[0],
            Prefix::ATTRIBUTE_TYPE => &[1],
            Prefix::ENTITY => &[100],
            Prefix::ATTRIBUTE => &[101],
        }
    }
}
