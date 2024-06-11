/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use chrono::{Datelike, NaiveDate};

use super::primitive_encoding::{decode_i32, encode_i32};
use crate::graph::thing::vertex_attribute::AttributeIDLength;

#[derive(Debug, Copy, Clone)]
pub struct DateBytes {
    bytes: [u8; Self::LENGTH],
}

impl DateBytes {
    pub(crate) const LENGTH: usize = AttributeIDLength::Short.length();

    const DAYS_LENGTH: usize = i32::BITS as usize / 8;

    pub fn new(bytes: [u8; Self::LENGTH]) -> Self {
        Self { bytes }
    }

    pub fn build(date: NaiveDate) -> Self {
        let mut bytes = [0; Self::LENGTH];
        bytes[..Self::DAYS_LENGTH].copy_from_slice(&encode_i32(date.num_days_from_ce()));
        Self { bytes }
    }

    pub fn as_naive_date(&self) -> NaiveDate {
        let days = decode_i32(self.bytes[..Self::DAYS_LENGTH].try_into().unwrap());
        NaiveDate::from_num_days_from_ce_opt(days).unwrap()
    }

    pub(crate) fn bytes(&self) -> [u8; Self::LENGTH] {
        self.bytes
    }
}
