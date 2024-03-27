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

use std::{
    collections::VecDeque,
    error::Error,
    fmt,
    io::Read,
    sync::{
        atomic::{AtomicU64, AtomicU8, AtomicUsize, Ordering},
        Arc, OnceLock, RwLock,
    },
};

use durability::{DurabilityRecord, DurabilityRecordType, SequenceNumber};
use logger::result::ResultExt;
use primitive::u80::U80;
use serde::{Deserialize, Serialize};

use crate::{
    keyspace::keyspace::KeyspaceId,
    snapshot::{buffer::KeyspaceBuffers, write::Write},
};

#[derive(Debug)]
pub(crate) struct IsolationManager {
    timeline: Timeline,
}

impl fmt::Display for IsolationManager {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Timeline[windows={}, next_window_sequence_number={}, watermark={}]",
            self.timeline.window_count(),
            self.timeline.next_window_sequence_number(),
            self.watermark()
        )
    }
}

impl IsolationManager {
    pub(crate) fn new(next_sequence_number: SequenceNumber) -> IsolationManager {
        IsolationManager { timeline: Timeline::new(next_sequence_number) }
    }

    pub(crate) fn opened(&self, open_sequence_number: &SequenceNumber) {
        self.timeline.record_reader(open_sequence_number);
    }

    pub(crate) fn closed(&self, open_sequence_number: &SequenceNumber) {
        self.timeline.remove_reader(open_sequence_number);
    }

    pub(crate) fn try_commit(
        &self,
        commit_sequence_number: SequenceNumber,
        commit_record: CommitRecord,
    ) -> Result<(), IsolationError> {
        let open_sequence_number = commit_record.open_sequence_number;
        let commit_window = self.pending(&commit_sequence_number, commit_record);
        let validation_result =
            self.validate_all_concurrent(&commit_sequence_number, commit_window.get_record(&commit_sequence_number));

        if validation_result.is_ok() {
            self.committed(&commit_sequence_number);
            Ok(())
        } else {
            self.commit_failed(&commit_sequence_number, &open_sequence_number);
            validation_result
        }
    }

    fn commit_failed(&self, commit_sequence_number: &SequenceNumber, open_sequence_number: &SequenceNumber) {
        let self1 = &self.timeline;
        let window = self1.get_window(commit_sequence_number);
        window.set_closed(commit_sequence_number);
        self.timeline.remove_reader(open_sequence_number);
    }

    fn validate_all_concurrent(
        &self,
        commit_sequence_number: &SequenceNumber,
        commit_record: &CommitRecord,
    ) -> Result<(), IsolationError> {
        debug_assert!(commit_record.open_sequence_number() < commit_sequence_number);
        // TODO: decide if we should block until all predecessors finish, allow out of order (non-Calvin model/traditional model)
        //       We could also validate against all predecessors even if they are validating and fail eagerly.

        let mut predecessor_number = commit_sequence_number.number() - 1;
        let mut predecessor_sequence_number = SequenceNumber::new(predecessor_number);
        let Some(mut predecessor_window) = self.timeline.try_get_window(&predecessor_sequence_number) else {
            return Ok(()); // nothing to validate
        };

        let last_predecessor_number = commit_record.open_sequence_number.number() + 1;
        while predecessor_number <= last_predecessor_number {
            if !predecessor_window.contains(&predecessor_sequence_number) {
                predecessor_window = self.timeline.get_window(&predecessor_sequence_number);
            }
            self.validate_concurrent(commit_record, &predecessor_sequence_number, &predecessor_window)?;
            predecessor_number += 1;
            predecessor_sequence_number = SequenceNumber::new(predecessor_number);
        }
        Ok(())
    }

    fn validate_concurrent(
        &self,
        commit_record: &CommitRecord,
        predecessor_sequence_number: &SequenceNumber,
        predecessor_window: &Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>,
    ) -> Result<(), IsolationError> {
        let predecessor_status = predecessor_window.get_status(predecessor_sequence_number);
        match predecessor_status {
            CommitStatus::Empty => {
                unreachable!("A concurrent status should never be empty at commit time")
            }
            CommitStatus::Pending(predecessor_record) => {
                let result = self.validate_isolation(commit_record, predecessor_record);
                if result.is_err() && self.await_pending_status_commits(predecessor_sequence_number, predecessor_window)
                {
                    result
                } else {
                    Ok(())
                }
            }
            CommitStatus::Committed(predecessor_record) => self.validate_isolation(commit_record, predecessor_record),
            CommitStatus::Closed => Ok(()),
        }
    }

    fn await_pending_status_commits(
        &self,
        predecessor_sequence_number: &SequenceNumber,
        predecessor_window: &Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>,
    ) -> bool {
        debug_assert!(!matches!(predecessor_window.get_status(predecessor_sequence_number), CommitStatus::Empty));
        loop {
            let status = predecessor_window.get_status(predecessor_sequence_number);
            match status {
                CommitStatus::Empty => unreachable!("Illegal state - commit status cannot move from pending"),
                CommitStatus::Pending(_) => {
                    // TODO: we can improve the spin lock with async/await
                    // Note we only expect to have long waits in long chains of overlapping transactions that would conflict
                    // could also do a little sleep in the spin lock, for example if the validating is still far away
                    continue;
                }
                CommitStatus::Committed(_) => return true,
                CommitStatus::Closed => return false,
            }
        }
    }

    fn validate_isolation(&self, record: &CommitRecord, predecessor: &CommitRecord) -> Result<(), IsolationError> {
        // TODO: this can be optimised by some kind of bit-wise NAND of two bloom filter-like data structures first, since we assume few clashes this should mostly succeed
        // TODO: can be optimised with an intersection of two sorted iterators instead of iterate + gets
        for (index, buffer) in record.buffers().iter().enumerate() {
            let map = buffer.map().read().unwrap();
            if map.is_empty() {
                continue;
            }

            let predecessor_map = predecessor.buffers.get(KeyspaceId(index as _)).map().read().unwrap();
            if predecessor_map.is_empty() {
                continue;
            }

            for (key, write) in map.iter() {
                let predecessor_write = predecessor_map.get(key.bytes());
                if predecessor_write.is_some() {
                    match write {
                        Write::Insert { .. } => {}
                        Write::InsertPreexisting { reinsert, .. } => {
                            // Re-insert the value if a predecessor has deleted it. This may create extra versions of a key
                            //  in the case that the predecessor ends up failing. However, this will be rare.
                            if matches!(predecessor_write.unwrap(), Write::Delete) {
                                reinsert.store(true, Ordering::SeqCst);
                            }
                        }
                        Write::RequireExists { .. } => {
                            if matches!(predecessor_write.unwrap(), Write::Delete) {
                                return Err(IsolationError { kind: IsolationErrorKind::DeleteRequiredViolation });
                            }
                        }
                        Write::Delete => {
                            // we escalate delete-required to failure, since requires imply dependencies that may be broken
                            // TODO: maybe RequireExists should be RequireDependency to capture this?
                            if matches!(predecessor_write.unwrap(), Write::RequireExists { .. }) {
                                return Err(IsolationError { kind: IsolationErrorKind::RequiredDeleteViolation });
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn pending(
        &self,
        commit_sequence_number: &SequenceNumber,
        commit_record: CommitRecord,
    ) -> Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>> {
        self.timeline.record_pending(commit_sequence_number, commit_record)
    }

    fn committed(&self, commit_sequence_number: &SequenceNumber) {
        self.timeline.record_committed(commit_sequence_number)
    }

    pub(crate) fn watermark(&self) -> SequenceNumber {
        self.timeline.watermark()
    }

    pub(crate) fn apply_to_commit_record<F, T>(&self, sequence_number: &SequenceNumber, function: F) -> T
    where
        F: FnOnce(&CommitRecord) -> T,
    {
        let shared_window = self.timeline.get_window(sequence_number);
        let record = shared_window.get_record(sequence_number);
        function(record)
    }
}

//
// We can adjust the Window size to amortise the cost of the read-write locks to maintain the timeline
//
const TIMELINE_WINDOW_SIZE: usize = 100;

#[derive(Debug)]
struct Timeline {
    next_window_and_windows: RwLock<(SequenceNumber, VecDeque<Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>>)>,
}

///
///
/// Timeline concept:
///   Timeline is made of Windows.
///   Each Window stores a number of Slots.
///
///   Conceptually the timeline is one sequence of Slots, but we cut it into Windows for more efficient allocation/clean up/search.
///
///   The timeline should not clean up old windows while a 'reader' (ie open snapshot) is open on a window or an older window.
///
///   On commit, we
///     1) notify the commit is pending, writing the commit record into the Slot for its commit sequence number.
///     2) when validation has finished, record into the Slot for its commit sequence number the final status.
///   Commit without close just records into its Slot for its commit sequence number the Closed state.
///
///
///
///

impl Timeline {
    fn new(starting_sequence_number: SequenceNumber) -> Timeline {
        debug_assert!(starting_sequence_number.number() > 0);
        let last_sequence_number_value = starting_sequence_number.number() - U80::new(1);
        let initial_window = Arc::new(TimelineWindow::new(SequenceNumber::new(last_sequence_number_value)));
        let next_window_start = *initial_window.end();
        let mut windows = VecDeque::new();
        windows.push_back(initial_window);

        let timeline = Timeline { next_window_and_windows: RwLock::new((next_window_start, windows)) };

        // initialise the one virtual 'predecessor' so snapshots have a sequence number to open against
        let sequence_number = SequenceNumber::new(last_sequence_number_value);
        let window = timeline.get_window(&sequence_number);
        window.set_closed(&sequence_number);
        timeline
    }

    fn watermark(&self) -> SequenceNumber {
        //
        // TODO: we would like to not be a non-locking and constant time operation (probably an Atomic) since every snapshot queries for the watermark.
        //       Issues:
        //         1) Rust does not support an AtomicU128 which could hold a SequenceNumber.
        //             --> Perhaps we want to combine a logically 'unsafe' structure that uses a raw pointer/atomic int & unsafe writes to a pair of slots that are pointed into?
        //             --> Alternative: keep an atomic u64 and keep a 'origin' which is increases over time so we never have to use the entire u128 range.
        //         2) If we just keep a reference to the window containing the current watermark, we still need a lock to update it...
        //             --> The IsolationManager should be able to guarantee that the watermark moves up atomically when the N+1's snapshot closes/commits
        //             --> However this would definitely require a lock over both
        //             --> It should be good enough to order it such that commit/close does: 1) update timeline, then 2) update watermark if possible 3) return control. This will guarantee new snapshots will see this commit in the watermark if it moves up.
        //             --> There is a complexity in updating the watermark - we need to scan commit statuses from the current watermark upwards, then update it. What if two commits do this concurrently and race? Is it possible to not make progress?
        //
        //     We should just re-think what the watermark guarantees actually are...?
        //     1) Because we commit optimistically/at the end of a snapshot only, commit slots are only filled once a transaction goes to commit. This means we can at worst be as behind as the current set of 'processing' commits, which is not many.
        //     2) We do allow pending commits to proceed out of order sometimes - if they have non-intersecting commit records. This means we can't guarantee the watermark is raised after a commit.
        //        --> first hint: maybe we can just bump the watermark when a commit happens that did not skip any commit records/intersected with all concurrent commits? Seems like most cases will not suit this...
        //     3) Side note: If we want to preserve causality between transactions by the same user, a new transaction by the same user must wait for the watermark to rise past the recently committed snapshot.
        //         --> simplest way to do this without retaining causality information on the client is: when a client asks for a snapshot, immediately get _latest_ (possibly pending) commit sequence number. Then wait until watermark rises to meet that and use it.
        //
        let (next_sequence_number, windows) = &*self.next_window_and_windows.read().unwrap_or_log();
        windows
            .iter()
            .find_map(|w| {
                if w.is_finished() {
                    None
                } else {
                    debug_assert!(w.watermark().is_some());
                    w.watermark()
                }
            })
            .unwrap_or_else(|| SequenceNumber::new(next_sequence_number.number() - U80::new(1)))
    }

    fn record_reader(&self, sequence_number: &SequenceNumber) {
        let window = self.get_or_create_window(sequence_number);
        window.increment_readers();
    }

    fn record_pending(
        &self,
        sequence_number: &SequenceNumber,
        commit_record: CommitRecord,
    ) -> Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>> {
        let window = self.get_or_create_window(sequence_number);
        window.set_pending(sequence_number, commit_record);
        window
    }

    fn record_committed(&self, sequence_number: &SequenceNumber) {
        let window = self.get_or_create_window(sequence_number);
        window.set_committed(sequence_number);
        self.remove_window_reader(sequence_number, &window);
    }

    fn remove_reader(&self, reader_sequence_number: &SequenceNumber) {
        let read_window = self.get_window(reader_sequence_number);
        self.remove_window_reader(reader_sequence_number, &read_window);
    }

    fn remove_window_reader(
        &self,
        reader_sequence_number: &SequenceNumber,
        reader_window: &Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>,
    ) {
        debug_assert!(reader_window.contains(reader_sequence_number));
        let _readers_remaining = reader_window.decrement_readers();

        // TODO: clean up windows that no longer need to be retained in memory.
        //      --> see task
    }

    fn last_window(
        windows: &VecDeque<Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>>,
    ) -> Arc<crate::isolation_manager::TimelineWindow<TIMELINE_WINDOW_SIZE>> {
        debug_assert!(!windows.is_empty());
        windows[windows.len() - 1].clone()
    }

    fn get_or_create_window(&self, sequence_number: &SequenceNumber) -> Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>> {
        self.try_get_window(sequence_number).clone().unwrap_or_else(|| self.create_windows_to(sequence_number))
    }

    fn get_window(&self, sequence_number: &SequenceNumber) -> Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>> {
        self.try_get_window(sequence_number).unwrap()
    }

    fn try_get_window(&self, sequence_number: &SequenceNumber) -> Option<Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>> {
        let (_, windows) = &*self.next_window_and_windows.read().unwrap_or_log();
        Self::find_window(sequence_number, windows)
    }

    fn find_window(
        sequence_number: &SequenceNumber,
        windows: &VecDeque<Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>>,
    ) -> Option<Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>>> {
        windows.iter().rev().find(|window| window.contains(sequence_number)).cloned()
    }

    fn create_windows_to(&self, sequence_number: &SequenceNumber) -> Arc<TimelineWindow<TIMELINE_WINDOW_SIZE>> {
        let (next_window, windows) = &mut *self.next_window_and_windows.write().unwrap_or_log();

        // re-check if another thread created required window before we acquired lock
        let window = Self::find_window(sequence_number, windows);
        if let Some(window) = window {
            window.clone()
        } else {
            loop {
                let new_window = TimelineWindow::new(*next_window);
                *next_window = new_window.end_sequence_number;
                let shared_new_window = Arc::new(new_window);
                windows.push_back(shared_new_window.clone());
                if shared_new_window.contains(sequence_number) {
                    break shared_new_window;
                }
            }
        }
    }

    fn window_count(&self) -> usize {
        let (_, windows) = &*self.next_window_and_windows.read().unwrap_or_log();
        windows.len()
    }

    fn next_window_sequence_number(&self) -> SequenceNumber {
        let (next_window_sequence_number, _) = &*self.next_window_and_windows.read().unwrap_or_log();
        *next_window_sequence_number
    }
}

#[derive(Debug)]
struct TimelineWindow<const SIZE: usize> {
    starting_sequence_number: SequenceNumber,
    end_sequence_number: SequenceNumber,
    slots: [AtomicU8; SIZE],
    commit_records: [OnceLock<CommitRecord>; SIZE],
    readers: AtomicU64,
    available_slots: AtomicUsize,
}

impl<const SIZE: usize> TimelineWindow<SIZE> {
    fn new(starting_sequence_number: SequenceNumber) -> TimelineWindow<SIZE> {
        const EMPTY: OnceLock<CommitRecord> = OnceLock::new();
        let commit_data = [EMPTY; SIZE];
        let slots: [AtomicU8; SIZE] = core::array::from_fn(|_| AtomicU8::new(0));
        debug_assert_eq!(slots[0].load(Ordering::SeqCst), SlotMarker::Empty.as_u8());

        TimelineWindow {
            starting_sequence_number,
            end_sequence_number: SequenceNumber::new(starting_sequence_number.number() + U80::new(SIZE as u128)),
            slots,
            commit_records: commit_data,
            readers: AtomicU64::new(0),
            available_slots: AtomicUsize::new(SIZE),
        }
    }

    /// Sequence number start of window (inclusive)
    fn start(&self) -> &SequenceNumber {
        &self.starting_sequence_number
    }

    /// Sequence number end of window (exclusive)
    fn end(&self) -> &SequenceNumber {
        &self.end_sequence_number
    }

    fn contains(&self, sequence_number: &SequenceNumber) -> bool {
        self.starting_sequence_number <= *sequence_number && *sequence_number < self.end_sequence_number
    }

    fn is_finished(&self) -> bool {
        self.available_slots.load(Ordering::SeqCst) == 0
    }

    fn watermark(&self) -> Option<SequenceNumber> {
        self.slots.iter().enumerate().find_map(|(index, status)| {
            let marker = SlotMarker::from(status.load(Ordering::SeqCst));
            match marker {
                SlotMarker::Empty | SlotMarker::Pending => {
                    Some(SequenceNumber::new(self.start().number() + U80::new(index as u128 - 1)))
                }
                SlotMarker::Committed | SlotMarker::Closed => None,
            }
        })
    }

    fn set_pending(&self, sequence_number: &SequenceNumber, commit_record: CommitRecord) {
        debug_assert!(self.contains(sequence_number));
        let index = self.index_of(sequence_number);
        self.commit_records[index].set(commit_record).unwrap_or_log();
        self.slots[index].store(SlotMarker::Pending.as_u8(), Ordering::SeqCst);
    }

    fn set_committed(&self, sequence_number: &SequenceNumber) {
        debug_assert!(self.contains(sequence_number));
        let index = self.index_of(sequence_number);
        self.slots[index].store(SlotMarker::Committed.as_u8(), Ordering::SeqCst);
        self.available_slots.fetch_sub(1, Ordering::SeqCst);
    }

    fn set_closed(&self, sequence_number: &SequenceNumber) {
        debug_assert!(self.contains(sequence_number));
        let index = self.index_of(sequence_number);
        self.slots[index].store(SlotMarker::Closed.as_u8(), Ordering::SeqCst);
        self.available_slots.fetch_sub(1, Ordering::SeqCst);
    }

    fn get_record(&self, sequence_number: &SequenceNumber) -> &CommitRecord {
        debug_assert!(self.contains(sequence_number));
        let index = self.index_of(sequence_number);
        self.commit_records[index].get().unwrap()
    }

    fn get_status<'this>(&'this self, sequence_number: &SequenceNumber) -> CommitStatus<'this> {
        debug_assert!(self.contains(sequence_number));
        let index = self.index_of(sequence_number);
        let status = SlotMarker::from(self.slots[index].load(Ordering::SeqCst));
        match status {
            SlotMarker::Empty => CommitStatus::Empty,
            SlotMarker::Pending => CommitStatus::Pending(self.commit_records[index].get().unwrap()),
            SlotMarker::Committed => CommitStatus::Committed(self.commit_records[index].get().unwrap()),
            SlotMarker::Closed => CommitStatus::Closed,
        }
    }

    fn increment_readers(&self) {
        self.readers.fetch_add(1, Ordering::SeqCst);
    }

    fn decrement_readers(&self) -> u64 {
        self.readers.fetch_sub(1, Ordering::SeqCst)
    }

    fn index_of(&self, sequence_number: &SequenceNumber) -> usize {
        debug_assert!(sequence_number.number() - self.starting_sequence_number.number() < usize::MAX as u128);
        (sequence_number.number() - self.starting_sequence_number.number()).number() as usize
    }
}

#[derive(Debug)]
pub(crate) enum CommitStatus<'a> {
    Empty,
    Pending(&'a CommitRecord),
    Committed(&'a CommitRecord),
    Closed,
}

#[derive(Debug)]
enum SlotMarker {
    Empty,
    Pending,
    Committed,
    Closed,
}

impl SlotMarker {
    const fn as_u8(&self) -> u8 {
        match self {
            SlotMarker::Empty => 0,
            SlotMarker::Pending => 1,
            SlotMarker::Committed => 2,
            SlotMarker::Closed => 3,
        }
    }

    const fn from(value: u8) -> Self {
        match value {
            0 => SlotMarker::Empty,
            1 => SlotMarker::Pending,
            2 => SlotMarker::Committed,
            3 => SlotMarker::Closed,
            _ => unreachable!(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub(crate) struct CommitRecord {
    // TODO: this could read-through to the WAL if we have to save memory?
    buffers: KeyspaceBuffers,
    open_sequence_number: SequenceNumber,
}

impl CommitRecord {
    pub(crate) fn new(buffers: KeyspaceBuffers, open_sequence_number: SequenceNumber) -> CommitRecord {
        CommitRecord { buffers, open_sequence_number }
    }

    pub(crate) fn buffers(&self) -> &KeyspaceBuffers {
        &self.buffers
    }

    pub(crate) fn open_sequence_number(&self) -> &SequenceNumber {
        &self.open_sequence_number
    }

    fn deserialise_from(record_type: DurabilityRecordType, reader: impl Read)
    where
        Self: Sized,
    {
        assert_eq!(Self::RECORD_TYPE, record_type);
        // TODO: handle error with a better message
        bincode::deserialize_from(reader).unwrap_or_log()
    }
}

impl DurabilityRecord for CommitRecord {
    const RECORD_TYPE: DurabilityRecordType = 0;

    const RECORD_NAME: &'static str = "commit_record";

    fn serialise_into(&self, writer: &mut impl std::io::Write) -> bincode::Result<()> {
        debug_assert_eq!(
            bincode::serialize(
                &bincode::deserialize::<CommitRecord>(bincode::serialize(&self).as_ref().unwrap()).unwrap()
            )
            .unwrap(),
            bincode::serialize(self).unwrap()
        );
        bincode::serialize_into(writer, &self)
    }

    fn deserialise_from(reader: &mut impl Read) -> bincode::Result<Self> {
        // https://github.com/bincode-org/bincode/issues/633
        let mut buf = Vec::new();
        reader.read_to_end(&mut buf).unwrap();
        bincode::deserialize(&buf)
    }
}

#[derive(Debug)]
pub struct IsolationError {
    pub kind: IsolationErrorKind,
}

#[derive(Debug)]
pub enum IsolationErrorKind {
    DeleteRequiredViolation,
    RequiredDeleteViolation,
}

impl fmt::Display for IsolationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            IsolationErrorKind::DeleteRequiredViolation => write!(f, "Isolation violation: Delete-Require conflict. A preceding concurrent commit has deleted a key required by this transaction. Please retry."),
            IsolationErrorKind::RequiredDeleteViolation => write!(f, "Isolation violation: Require-Delete conflict. This commit has deleted a key required by a preceding concurrent transaction. Please retry."),
        }
    }
}

impl Error for IsolationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            IsolationErrorKind::DeleteRequiredViolation => None,
            IsolationErrorKind::RequiredDeleteViolation => None,
        }
    }
}
