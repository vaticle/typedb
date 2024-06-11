/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

pub(super) fn decode_u16(bytes: [u8; 2]) -> u16 {
    u16::from_be_bytes(bytes)
}

pub(super) fn encode_u16(value: u16) -> [u8; 2] {
    value.to_be_bytes()
}

pub(super) fn decode_u32(bytes: [u8; 4]) -> u32 {
    u32::from_be_bytes(bytes)
}

pub(super) fn encode_u32(value: u32) -> [u8; 4] {
    value.to_be_bytes()
}

pub(super) fn decode_i32(bytes: [u8; 4]) -> i32 {
    i32::from_be_bytes(bytes) ^ i32::MIN
}

pub(super) fn encode_i32(value: i32) -> [u8; 4] {
    (value ^ i32::MIN).to_be_bytes()
}

pub fn decode_u64(bytes: [u8; 8]) -> u64 {
    u64::from_be_bytes(bytes)
}

pub fn encode_u64(value: u64) -> [u8; 8] {
    value.to_be_bytes()
}

pub(super) fn decode_i64(bytes: [u8; 8]) -> i64 {
    i64::from_be_bytes(bytes) ^ i64::MIN
}

pub(super) fn encode_i64(value: i64) -> [u8; 8] {
    (value ^ i64::MIN).to_be_bytes()
}
