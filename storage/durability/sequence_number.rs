/*
 *  Copyright (C) 2023 Vaticle
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as
 *  published by the Free Software Foundation, either version 3 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

use std::fmt;
use serde::{Deserialize, Serialize};
use primitive::u80::U80;

#[derive(Serialize, Deserialize, Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct SequenceNumber {
    number: U80,
}

impl fmt::Display for SequenceNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SeqNr[{}]", self.number.number())
    }
}

impl SequenceNumber {
    pub const MAX: Self = Self { number: U80::MAX };

    pub fn new(number: U80) -> Self {
        Self { number }
    }

    pub fn next(&self) -> Self {
        Self { number: self.number + U80::new(1) }
    }

    pub fn previous(&self) -> Self {
        Self { number: self.number - U80::new(1) }
    }

    pub fn number(&self) -> U80 {
        self.number
    }

    pub fn serialise_be_into(&self, bytes: &mut [u8]) {
        assert_eq!(bytes.len(), U80::BYTES);
        let number_bytes = self.number.to_be_bytes();
        bytes.copy_from_slice(&number_bytes)
    }

    pub fn to_be_bytes(&self) -> [u8; U80::BYTES] {
        self.number.to_be_bytes()
    }

    pub fn invert(&self) -> Self {
        Self { number: U80::MAX - self.number }
    }

    pub const fn serialised_len() -> usize {
        U80::BYTES
    }
}

impl From<u128> for SequenceNumber {
    fn from(value: u128) -> Self {
        Self::new(U80::new(value))
    }
}
