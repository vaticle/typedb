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
    ub_sync: u128,
    lb: AtomicU64,
}

const SYNC_MASK: u64 = 0xff00000000000000;
const UB_MASK: u128 = 0xffffffffffffffff_0000000000000000;
const UB_INCREMENT: u128 = 0x0000000000000001_0000000000000000;

impl AtomicU128 {

    pub fn new(from: u128) -> AtomicU128 {
        AtomicU128 {
            ub_sync: from,
            lb: AtomicU64::new((from as u64) & u64::MAX)
        }
    }

    #[inline]
    fn ub_outdated(ub_sync: u128, lb: u64) -> bool {
        (lb & SYNC_MASK) < ((ub_sync as u64) & SYNC_MASK)
    }

    #[inline]
    fn compose(ub_sync: u128, lb: u64) -> u128 {
        (ub_sync & UB_MASK) | (lb as u128)
    }

    pub fn get(&self) -> u128 {
        let ub_read = self.ub_sync;
        let lb_read  = self.lb.load(SeqCst);
        let ub_increment = if Self::ub_outdated(ub_read, lb_read) {UB_INCREMENT} else { 0 };
        Self::compose(ub_read + ub_increment, lb_read)
    }

    pub fn add_and_get(&mut self, increment: u32) -> u128 {
        let ub_read = self.ub_sync;
        let lb_before_add = self.lb.fetch_add(increment as u64, SeqCst);
        let lb_after_add = u64::wrapping_add(lb_before_add, increment as u64);
        let ub_increment = if Self::ub_outdated(ub_read, lb_after_add) {UB_INCREMENT} else { 0 };
        let updated_sync_bits: bool = (lb_after_add & SYNC_MASK) != (lb_before_add & SYNC_MASK);

        if updated_sync_bits {
            self.ub_sync = ((ub_read & UB_MASK) + ub_increment) | (lb_after_add as u128);
            Self::compose(self.ub_sync, lb_after_add)
        } else {
            Self::compose(ub_read + ub_increment, lb_after_add)
        }
    }

    pub fn compare_and_exchange_incremented(&mut self, current : u128, increment: u32) -> Result<u128, u128> {
        /// The LB is good enough to see if the change went through.
        let updated: u128 = current + increment as u128;
        let lb_cas_result = self.lb.compare_exchange(current as u64, updated as u64, SeqCst, SeqCst);
        let ub_read = self.ub_sync; // Current could have been anything. Do not rely on it.
        match lb_cas_result {
            Ok(lb_current) => {
                /// Ensure all of current did match, not just LB
                let ub_increment = if Self::ub_outdated(ub_read, lb_current) {UB_INCREMENT} else { 0 };
                let composed = Self::compose(ub_read + ub_increment, lb_current);
                if composed == current { Ok(composed) } else {Err(composed) }
            },
            Err(lb_swapped) => {
                let ub_increment = if Self::ub_outdated(ub_read, lb_swapped) {UB_INCREMENT} else { 0 };
                Err(Self::compose(ub_read + ub_increment, lb_swapped))
            }
        }
    }
}

pub mod tests {
    use crate::atomic_u128::{AtomicU128, UB_INCREMENT};

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
    }

    #[test]
    fn test_compare_and_exchange_incremented__fail_on_ub() {
        let from: u128 = 0x0123456789abcdef__ffffffff_fedbca98;
        let increment: u32 = 0x11111111;
        let mut t = AtomicU128::new(from);
        let ret = t.compare_and_exchange_incremented(from + UB_INCREMENT, increment);
        assert_eq!(Err(from), ret);
    }
}
