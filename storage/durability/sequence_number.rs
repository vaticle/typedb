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

use std::cell::Cell;
use std::fmt;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::SeqCst;
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

pub struct AtomicSequenceNumber {
    epoch: Cell<u64>,
    seq_sync: AtomicU64,
}

impl AtomicSequenceNumber {
    const SEQ_NUMBER_BITS: u8 = 32;
    const SYNC_BITS: u8 = (64 - Self::SEQ_NUMBER_BITS);

    const UW_SYNC_MASK: u64 = (1 << Self::SYNC_BITS) - 1;
    const EPOCH_OVERFLOW_INCREMENT: u64 = (1 << Self::SYNC_BITS);

    #[inline]
    fn epoch_overflow_oudated(epoch: u64, seq_sync: u64) -> bool {
        let seq_sync_bits = seq_sync >> Self::SEQ_NUMBER_BITS;
        let epoch_sync_bits = epoch & Self::UW_SYNC_MASK;
        seq_sync_bits < epoch_sync_bits
    }

    #[inline]
    fn compose(epoch: u64, seq_sync: u64) -> SequenceNumber {
        SequenceNumber::from((((epoch & !Self::UW_SYNC_MASK) as u128) << Self::SEQ_NUMBER_BITS) | seq_sync as u128)
    }

    pub fn new(epoch: u64, seq: u32) -> Self {
        let lw_sync = (epoch & Self::UW_SYNC_MASK) << Self::SEQ_NUMBER_BITS;
        let seq_sync = (seq as u64) | lw_sync;
        AtomicSequenceNumber {
            epoch: Cell::new(epoch),
            seq_sync: AtomicU64::new(seq_sync),
        }
    }

    pub fn from_sequence_number(sequence_number: SequenceNumber) -> Self {
        let from = sequence_number.number().number();
        let epoch = (from >> Self::SEQ_NUMBER_BITS) as u64;
        let lw_mask = (u128::checked_shl(1, 65).unwrap() - 1) as u64;
        let seq_sync = (from as u64) & lw_mask;
        AtomicSequenceNumber {
            epoch: Cell::new(epoch),
            seq_sync: AtomicU64::new(seq_sync),
        }
    }

    pub fn load(&self) -> SequenceNumber {
        let epoch_read = self.epoch.get();
        let seq_sync_read = self.seq_sync.load(SeqCst);
        let epoch_overflow_update = if Self::epoch_overflow_oudated(epoch_read, seq_sync_read) { Self::EPOCH_OVERFLOW_INCREMENT } else { 0 };
        Self::compose(epoch_read + epoch_overflow_update, seq_sync_read)
    }

    pub fn fetch_increment(&self) -> SequenceNumber {
        // We need to be sure the epoch has not changed.
        let epoch_read = self.epoch.get();
        let seq_sync_before_increment = self.seq_sync.fetch_add(1, SeqCst);
        let epoch_overflow_update = if Self::epoch_overflow_oudated(epoch_read, seq_sync_before_increment) { Self::EPOCH_OVERFLOW_INCREMENT } else { 0 };
        Self::compose(epoch_read + epoch_overflow_update, seq_sync_before_increment)
    }

    pub fn increment_epoch(&self) {
        // TODO: Use Mutex to guarantee single writer?
        let next_epoch = self.epoch.get() + 1;
        let seq_sync_updated = next_epoch << Self::SEQ_NUMBER_BITS; // & Self::SEQ_SYNC_MASK; is not needed
        self.seq_sync.store(seq_sync_updated, SeqCst);
        self.epoch.set(next_epoch);
    }
}

impl From<SequenceNumber> for AtomicSequenceNumber {
    fn from(value: SequenceNumber) -> Self {
        let as_u128 = value.number().number();
        Self::new(
            (as_u128 >> Self::SEQ_NUMBER_BITS) as u64,
            as_u128 as u32,
        )
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Add;
    use primitive::u80::U80;
    use crate::sequence_number::{AtomicSequenceNumber, SequenceNumber};

    #[test]
    fn create_readback() {
        {
            let from: SequenceNumber = SequenceNumber::from(0x0000_0000_0000_0000__0000_1234_0000_ffff);
            let t = AtomicSequenceNumber::from_sequence_number(from);
            assert_eq!(from, t.load());
        }
        {
            let epoch = 0x0000_0000_0000_1234;
            let seq = 0x0000_ffff;
            let t: AtomicSequenceNumber = AtomicSequenceNumber::new(epoch, seq);
            assert_eq!(
                ((u128::checked_shl(epoch as u128, AtomicSequenceNumber::SYNC_BITS as u32).unwrap()) | seq as u128),
                t.load().number().number()
            );
        }
    }

    #[test]
    fn fetch_increment() {
        let epoch: u64 = 0x0000_0000_0000_1234;
        let seq: u32 = 0x0000_ffff;
        let expected = U80::new(0x0000_0000_0000_1234_0000_ffff);
        let t: AtomicSequenceNumber = AtomicSequenceNumber::new(epoch, seq);

        let fetched = t.fetch_increment();
        assert_eq!(expected, fetched.number());
        assert_eq!(expected.add(U80::new(1)), t.load().number());
    }

    #[test]
    fn increment_epoch() {
        {
            let epoch: u64 = 0x0000_0000_0000_1234;
            let seq: u32 = 0x0000_ffff;
            let expected = U80::new(0x0000_0000_0000_1235_0000_0000);
            let t: AtomicSequenceNumber = AtomicSequenceNumber::new(epoch, seq);
            t.increment_epoch();
            assert_eq!(expected, t.load().number());
        }
        {
            let epoch: u64 = 0x0000_0000_ffff_ffff;
            let seq: u32 = 0x0000_ffff;
            let expected = U80::new(0x0000_0001_0000_0000_0000_0000);
            let t: AtomicSequenceNumber = AtomicSequenceNumber::new(epoch, seq);
            t.increment_epoch();
            assert_eq!(expected, t.load().number());
        }
    }
}
