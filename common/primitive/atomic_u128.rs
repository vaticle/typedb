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

use std::cell::Cell;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::SeqCst;

/// Implements an AtomicU128 restricted to increments of u32.
/// The lower-word (LW) is implemented using an AtomicU64. It is always correct.
/// The upper word (UW) is implemented using u128, with an overlap of the upper 8 bits of the lower-word. The upper word + 8 sync-bits are eventually correct.
/// The overlap is used to detect the UW being outdated.
/// We restrict increments to at most u32::MAX, so that it is reasonable to assume:
/// 1. there are never concurrent updates to the sync-bits or to UW.
/// 2. The UW is out of sync by exactly 1 when sync_bits(LW) < sync_bits(UW), and is up-to-date otherwise
///
/// It is the responsibility of the thread that updates the sync_bits (and possibly overflow) to update sync_bits in the u128.
/// Other threads can return (UW+1)(LW) if sync_bits(LW) < sync_bits(UW);  (UW)(LW) otherwise
pub struct AtomicU128 {
    uw_sync: Cell<u128>,
    lw: AtomicU64,
}

const SYNC_MASK: u64 = 0xff00000000000000;
const UW_MASK: u128 = 0xffffffffffffffff_0000000000000000;
const UW_INCREMENT: u128 = 0x0000000000000001_0000000000000000;

impl AtomicU128 {

    pub fn new(from: u128) -> Self {
        AtomicU128 {
            uw_sync: Cell::new(from),
            lw: AtomicU64::new(from as u64)
        }
    }

    #[inline]
    fn uw_outdated(uw_sync: u128, lw: u64) -> bool {
        (lw & SYNC_MASK) < ((uw_sync as u64) & SYNC_MASK)
    }

    #[inline]
    fn compose(uw_sync: u128, lw: u64) -> u128 {
        (uw_sync & UW_MASK) | (lw as u128)
    }

    pub fn get(&self) -> u128 {
        let uw_read = self.uw_sync.get();
        let lw_read  = self.lw.load(SeqCst);
        let uw_increment = if Self::uw_outdated(uw_read, lw_read) { UW_INCREMENT } else { 0 };
        Self::compose(uw_read + uw_increment, lw_read)
    }

    pub fn add_and_get(&self, increment: u32) -> u128 {
        let uw_read = self.uw_sync.get();
        let lw_before_add = self.lw.fetch_add(increment as u64, SeqCst);
        let lw_after_add = u64::wrapping_add(lw_before_add, increment as u64);
        let uw_increment = if Self::uw_outdated(uw_read, lw_after_add) { UW_INCREMENT } else { 0 };
        let updated_sync_bits: bool = (lw_after_add & SYNC_MASK) != (lw_before_add & SYNC_MASK);

        if updated_sync_bits {
            let updated_uw_sync = ((uw_read & UW_MASK) + uw_increment) | (lw_after_add as u128);
            self.uw_sync.replace(updated_uw_sync);
            Self::compose(updated_uw_sync, lw_after_add)
        } else {
            Self::compose(uw_read + uw_increment, lw_after_add)
        }
    }

    pub fn compare_and_exchange_incremented(&self, current : u128, increment: u32) -> Result<u128, u128> {
        // UW must match to do a swap.
        let uw_read = self.uw_sync.get();
        // we can use current's LW in place of self.lw because current's sync-bits must be equal to lw's sync bits for the swap to succeed.
        let uw_increment = if Self::uw_outdated(uw_read, current as u64) { UW_INCREMENT } else { 0 };
        let uw_match_if_lw_match = ((uw_read & UW_MASK) + uw_increment) == (current & UW_MASK);

        // Can `uw_match_if_lw_match` be true if lw(current) = lw(self) but uw(current) != uw(self) ? No.
        //      Trying to show this should contradict that self.uw_sync cannot be ahead of self.lw.
        // Can `uw_match_if_lw_match` be false, but the true value be equal to current? Also, No.
        //      Sketch: Assume lw match, full match iff uw_match_if_lw_match is true.

        if uw_match_if_lw_match {
            let updated: u128 = current + increment as u128;
            let lw_cas_result = self.lw.compare_exchange(current as u64, updated as u64, SeqCst, SeqCst);
            match lw_cas_result {
                Ok(lw_swapped) => {
                    debug_assert_eq!(lw_swapped, current as u64);
                    // BUG: uw_sync needs to be updated
                    Ok(current)
                },
                Err(lw_swapped) => {
                    let uw_increment = if Self::uw_outdated(uw_read, lw_swapped) { UW_INCREMENT } else { 0 };
                    Err(Self::compose(uw_read + uw_increment, lw_swapped))
                }
            }
        } else {
            // If uw don't match, attempting a swap would write the wrong state to lw
            Err(self.get())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::atomic_u128::{AtomicU128, UW_INCREMENT};

    #[test]
    fn test_create_readback() {
        let from = 0x0123456789abcdef_0123456789abcdef;
        let t = AtomicU128::new(from);
        assert_eq!(from, t.get());
    }

    #[test]
    fn test_add_and_get() {
        let from: u128 = 0x0123456789abcdef__ffffffff_fedbca98;
        let increment: u32 = 0x11111111;
        let expected = from + increment as u128;
        let mut t = AtomicU128::new(from);
        let sum = t.add_and_get(increment);
        // println!("exp:{:#18x}_{:#18x}\nact:{:#18x}_{:#18x}", (expected >> 64), expected as u64, (sum >> 64) , sum as u64);
        assert_eq!(expected, sum);
        assert_eq!(expected, t.get());
    }

    #[test]
    fn test_compare_and_exchange_incremented__success() {
        let from: u128 = 0x0123456789abcdef__ffffffff_fedbca98;
        let increment: u32 = 0x11111111;
        let expected_updated = from + increment as u128;
        let mut t = AtomicU128::new(from);
        let ret = t.compare_and_exchange_incremented(from, increment);
        assert_eq!(Ok(from), ret);
        assert_eq!(expected_updated, t.get());
    }

    #[test]
    fn test_compare_and_exchange_incremented__failure() {
        let from: u128 = 0x0123456789abcdef__ffffffff_fedbca98;
        let increment: u32 = 0x11111111;
        let expected_ret = from + increment as u128;
        let mut t = AtomicU128::new(from);
        t.add_and_get(increment);

        let ret = t.compare_and_exchange_incremented(from, 0x1234);
        assert_eq!(Err(expected_ret), ret);
        assert_eq!(expected_ret, t.get());
    }

    #[test]
    fn test_compare_and_exchange_incremented__fail_on_uw() {
        let from: u128 = 0x0123456789abcdef__ffffffff_fedbca98;
        let increment: u32 = 0x11111111;
        let mut t = AtomicU128::new(from);
        let ret = t.compare_and_exchange_incremented(from + UW_INCREMENT, increment);
        assert_eq!(Err(from), ret);
        assert_eq!(from, t.get());
    }
}
