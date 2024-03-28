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
    collections::HashMap,
    ffi::OsStr,
    fs::{self, File as StdFile, OpenOptions},
    io::{self, BufReader, BufWriter, Read, Seek, Write},
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicU64, Ordering},
        RwLock, RwLockReadGuard,
    },
};

use itertools::Itertools;
use primitive::u80::U80;

use crate::{
    DurabilityRecord, DurabilityRecordType, DurabilityService, RawRecord, RecordHeader, Result, SequenceNumber,
    Sequencer,
};

const MAX_WAL_FILE_SIZE: u64 = 16 * 1024 * 1024;

const FILE_PREFIX: &str = "wal-";

#[derive(Debug)]
pub struct WAL {
    registered_types: HashMap<DurabilityRecordType, &'static str>,
    next_sequence_number: AtomicU64,
    files: RwLock<Files>,
}

impl WAL {
    fn recover_impl(directory: PathBuf) -> io::Result<Self> {
        if !directory.exists() {
            fs::create_dir_all(&directory)?;
        }

        let files = Files::open(directory.clone())?;

        let files = RwLock::new(files);
        let next = RecordIterator::new(files.read().unwrap(), SequenceNumber::MIN)?
            .last()
            .map(|rr| rr.unwrap().sequence_number.number().number() as u64 + 1)
            .unwrap_or(1);

        Ok(Self { registered_types: HashMap::new(), next_sequence_number: AtomicU64::new(next), files })
    }
}

impl Sequencer for WAL {
    fn increment(&self) -> SequenceNumber {
        SequenceNumber::from(self.next_sequence_number.fetch_add(1, Ordering::Relaxed) as u128)
    }

    fn current(&self) -> SequenceNumber {
        SequenceNumber::from(self.next_sequence_number.load(Ordering::Relaxed) as u128)
    }

    fn previous(&self) -> SequenceNumber {
        SequenceNumber::from(self.next_sequence_number.load(Ordering::Relaxed) as u128 - 1)
    }
}

impl DurabilityService for WAL {
    fn recover(directory: impl AsRef<Path>) -> io::Result<Self> {
        Self::recover_impl(directory.as_ref().to_owned())
    }

    fn register_record_type<Record: DurabilityRecord>(&mut self) {
        if self.registered_types.get(&Record::RECORD_TYPE).is_some_and(|name| name != &Record::RECORD_NAME) {
            panic!("Illegal state: two types of WAL records registered with same ID and different names.")
        }
        self.registered_types.insert(Record::RECORD_TYPE, Record::RECORD_NAME);
    }

    fn sequenced_write<Record>(&self, record: &Record) -> Result<SequenceNumber>
    where
        Record: DurabilityRecord,
    {
        debug_assert!(self.registered_types.get(&Record::RECORD_TYPE) == Some(&Record::RECORD_NAME));
        let mut files = self.files.write().unwrap();
        let seq = self.increment();
        files.write_record(record, seq)?;
        Ok(seq)
    }

    fn iter_from(&self, sequence_number: SequenceNumber) -> Result<impl Iterator<Item = io::Result<RawRecord>>> {
        Ok(RecordIterator::new(self.files.read().unwrap(), sequence_number)?)
    }
}

#[derive(Debug)]
struct Files {
    directory: PathBuf,
    writer: BufWriter<StdFile>,
    files: Vec<File>,
}

impl Files {
    fn open(directory: PathBuf) -> io::Result<Self> {
        let mut files: Vec<File> = directory
            .read_dir()?
            .map_ok(|entry| entry.path())
            .filter_ok(|path| {
                path.file_name().and_then(OsStr::to_str).is_some_and(|name| name.starts_with(FILE_PREFIX))
            })
            .map(|path| File::open(path?))
            .try_collect()?;
        files.sort_unstable_by(|lhs, rhs| lhs.path.cmp(&rhs.path));

        if files.is_empty() {
            files.push(File::open_at(directory.clone(), SequenceNumber::from(1))?);
        }

        let writer = files.last().unwrap().writer()?;

        Ok(Self { directory, writer, files })
    }

    fn open_new_file_at(&mut self, start: SequenceNumber) -> io::Result<()> {
        let file = File::open_at(self.directory.clone(), start)?;
        self.writer = file.writer()?;
        self.files.push(file);
        Ok(())
    }

    fn write_record<Record>(&mut self, record: &Record, sequence_number: SequenceNumber) -> Result<()>
    where
        Record: DurabilityRecord,
    {
        if self.files.last().unwrap().len >= MAX_WAL_FILE_SIZE {
            self.open_new_file_at(sequence_number)?;
        }

        // TODO if this proves a bottleneck, encode directly into the file and rewind to write the
        // length into the header after the fact
        let mut buf = Vec::new();

        let mut encoder = lz4::EncoderBuilder::new().build(&mut buf).unwrap();
        record.serialise_into(&mut encoder)?;
        encoder.finish().1.unwrap();

        write_header(
            &mut self.writer,
            RecordHeader { sequence_number, len: buf.len() as u64, record_type: Record::RECORD_TYPE },
        )?;

        self.writer.write_all(&buf)?;
        self.writer.flush()?;

        self.files.last_mut().unwrap().len = self.writer.stream_position()?;
        Ok(())
    }

    fn iter(&self) -> impl Iterator<Item = &File> {
        self.files.iter()
    }
}

fn write_header(file: &mut BufWriter<StdFile>, header: RecordHeader) -> io::Result<()> {
    file.write_all(&header.sequence_number.to_be_bytes())?;
    file.write_all(&header.len.to_be_bytes())?;
    file.write_all(&[header.record_type])?;
    Ok(())
}

#[derive(Clone, Debug)]
struct File {
    start: SequenceNumber,
    len: u64,
    path: PathBuf,
}

impl File {
    fn format_file_name(seq: SequenceNumber) -> String {
        format!("{}{:025}", FILE_PREFIX, seq.number())
    }

    fn open_at(directory: PathBuf, start: SequenceNumber) -> io::Result<Self> {
        let path = directory.join(Self::format_file_name(start));
        let len = fs::metadata(&path).map(|md| md.len()).unwrap_or(0);
        Ok(Self { start, len, path })
    }

    fn open(path: PathBuf) -> io::Result<Self> {
        let num: u128 =
            path.file_name().and_then(|s| s.to_str()).and_then(|s| s.split('-').nth(1)).unwrap().parse().unwrap();
        let len = fs::metadata(&path).map(|md| md.len()).unwrap_or(0);
        Ok(Self { start: SequenceNumber::from(num), len, path })
    }

    fn writer(&self) -> io::Result<BufWriter<StdFile>> {
        Ok(BufWriter::new(OpenOptions::new().read(true).append(true).create(true).open(&self.path)?))
    }
}

#[derive(Debug)]
struct FileReader {
    file: File,
    reader: BufReader<StdFile>,
}

impl FileReader {
    fn new(file: File) -> io::Result<Self> {
        Ok(Self { reader: BufReader::new(StdFile::open(&file.path)?), file })
    }

    fn read_one_record(&mut self) -> io::Result<Option<RawRecord>> {
        if self.reader.stream_position()? == self.file.len {
            return Ok(None);
        }
        let RecordHeader { sequence_number, len, record_type } = self.read_header()?;

        let mut buf = vec![0; len as usize].into_boxed_slice();
        self.reader.read_exact(&mut buf)?;
        let mut bytes = Vec::new();
        lz4::Decoder::new(&mut &*buf).unwrap().read_to_end(&mut bytes)?;
        let bytes = bytes.into_boxed_slice();

        Ok(Some(RawRecord { sequence_number, record_type, bytes }))
    }

    fn read_header(&mut self) -> io::Result<RecordHeader> {
        let mut buf = [0; U80::BYTES];
        self.reader.read_exact(&mut buf)?;
        let sequence_number = SequenceNumber::new(U80::from_be_bytes(&buf));

        let mut buf = [0; std::mem::size_of::<u64>()];
        self.reader.read_exact(&mut buf)?;
        let len = u64::from_be_bytes(buf);

        let mut buf = [0; 1];
        self.reader.read_exact(&mut buf)?;
        let [record_type] = buf;

        Ok(RecordHeader { sequence_number, len, record_type })
    }
}

#[derive(Debug)]
struct RecordIterator<'a> {
    files: RwLockReadGuard<'a, Files>,
    current: usize,
    reader: Option<FileReader>,
}

impl<'a> RecordIterator<'a> {
    fn new(files: RwLockReadGuard<'a, Files>, start: SequenceNumber) -> io::Result<Self> {
        let (current, mut current_start) = files
            .iter()
            .map_while(|file| (file.start <= start).then_some(file.start))
            .enumerate()
            .last()
            .unwrap_or((0, files.files[0].start));
        let mut reader = FileReader::new(files.files[current].clone())?;
        while current_start < start {
            match reader.read_one_record().transpose() {
                None => {
                    // sequence number is past the end
                    return Ok(Self { files, current, reader: None });
                }
                Some(Err(err)) => return Err(err),
                Some(Ok(RawRecord { sequence_number, .. })) => {
                    current_start = SequenceNumber::new(sequence_number.number() + 1)
                }
            }
        }
        Ok(Self { files, current, reader: Some(reader) })
    }

    fn advance_file(&mut self) -> io::Result<Option<()>> {
        self.current += 1;
        if self.current < self.files.files.len() {
            self.reader = Some(FileReader::new(self.files.files[self.current].clone())?);
            Ok(Some(()))
        } else {
            self.reader.take();
            Ok(None)
        }
    }
}

impl<'a> Iterator for RecordIterator<'a> {
    type Item = io::Result<RawRecord>;

    fn next(&mut self) -> Option<Self::Item> {
        let reader = self.reader.as_mut()?;
        match reader.read_one_record().transpose() {
            None => match self.advance_file().transpose()? {
                Ok(()) => self.next(),
                Err(err) => {
                    self.reader = None;
                    Some(Err(err))
                }
            },
            some => some,
        }
    }
}

#[cfg(test)]
mod test {
    use itertools::Itertools;
    use tempdir::TempDir;

    use super::WAL;
    use crate::{DurabilityRecord, DurabilityRecordType, DurabilityService, RawRecord, SequenceNumber};

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    struct TestRecord {
        bytes: [u8; 4],
    }

    impl DurabilityRecord for TestRecord {
        const RECORD_TYPE: DurabilityRecordType = 0;
        const RECORD_NAME: &'static str = "TEST";

        fn serialise_into(&self, writer: &mut impl std::io::Write) -> bincode::Result<()> {
            writer.write_all(&self.bytes).unwrap();
            Ok(())
        }

        fn deserialise_from(reader: &mut impl std::io::Read) -> bincode::Result<Self> {
            let mut bytes = [0; 4];
            reader.read_exact(&mut bytes).unwrap();
            Ok(Self { bytes })
        }
    }

    fn open_wal(directory: &TempDir) -> WAL {
        let mut wal = WAL::recover(directory).unwrap();
        wal.register_record_type::<TestRecord>();
        wal
    }

    #[test]
    fn test_wal_write_read() {
        let directory = TempDir::new("wal-test").unwrap();

        let record = TestRecord { bytes: *b"test" };

        let wal = open_wal(&directory);
        wal.sequenced_write(&record).unwrap();

        let RawRecord { record_type, bytes, .. } = wal.iter_from_start().unwrap().next().unwrap().unwrap();
        assert_eq!(record_type, TestRecord::RECORD_TYPE);

        let read_record = TestRecord::deserialise_from(&mut &*bytes).unwrap();
        assert_eq!(record, read_record);
    }

    #[test]
    fn test_wal_write_read_lots() {
        let directory = TempDir::new("wal-test").unwrap();

        let records = [TestRecord { bytes: *b"test" }; 1024];

        let wal = open_wal(&directory);
        records.iter().try_for_each(|record| wal.sequenced_write(record).map(|_| ())).unwrap();

        let read_records = wal
            .iter_from_start()
            .unwrap()
            .map(|res| {
                let RawRecord { record_type, bytes, .. } = res.unwrap();
                assert_eq!(record_type, TestRecord::RECORD_TYPE);
                TestRecord::deserialise_from(&mut &*bytes).unwrap()
            })
            .collect_vec();

        assert_eq!(records.len(), read_records.len());
        assert_eq!(records, &*read_records);
    }

    #[test]
    fn test_wal_recover() {
        let directory = TempDir::new("wal-test").unwrap();

        let record = TestRecord { bytes: *b"test" };

        let wal = open_wal(&directory);
        wal.sequenced_write(&record).unwrap();
        drop(wal);

        let wal = open_wal(&directory);
        let RawRecord { record_type, bytes, .. } = wal.iter_from_start().unwrap().next().unwrap().unwrap();
        assert_eq!(record_type, TestRecord::RECORD_TYPE);

        let read_record = TestRecord::deserialise_from(&mut &*bytes).unwrap();
        assert_eq!(record, read_record);
    }

    #[test]
    fn test_wal_recover_multiple() {
        let directory = TempDir::new("wal-test").unwrap();

        let records = [TestRecord { bytes: *b"test" }, TestRecord { bytes: *b"abcd" }];

        let wal = open_wal(&directory);
        records.iter().try_for_each(|record| wal.sequenced_write(record).map(|_| ())).unwrap();
        drop(wal);

        let wal = open_wal(&directory);
        let read_records = wal
            .iter_from_start()
            .unwrap()
            .map(|res| {
                let RawRecord { record_type, bytes, .. } = res.unwrap();
                assert_eq!(record_type, TestRecord::RECORD_TYPE);
                TestRecord::deserialise_from(&mut &*bytes).unwrap()
            })
            .collect_vec();

        assert_eq!(records, &*read_records);
    }

    #[test]
    fn test_wal_iterate_from() {
        let directory = TempDir::new("wal-test").unwrap();

        let records = [TestRecord { bytes: *b"test" }, TestRecord { bytes: *b"abcd" }];

        let wal = open_wal(&directory);
        let sequence_numbers: Vec<_> = records.iter().map(|record| wal.sequenced_write(record)).try_collect().unwrap();
        let iter_start = sequence_numbers[1];

        let read_records: Vec<TestRecord> = wal
            .iter_from(iter_start)
            .unwrap()
            .map(|res| {
                let RawRecord { record_type, bytes, .. } = res.unwrap();
                assert_eq!(record_type, TestRecord::RECORD_TYPE);
                TestRecord::deserialise_from(&mut &*bytes).unwrap()
            })
            .collect_vec();
        assert_eq!(&records[1..], &*read_records);

        drop(wal);

        let wal = open_wal(&directory);
        let read_records = wal
            .iter_from(iter_start)
            .unwrap()
            .map(|res| {
                let RawRecord { record_type, bytes, .. } = res.unwrap();
                assert_eq!(record_type, TestRecord::RECORD_TYPE);
                TestRecord::deserialise_from(&mut &*bytes).unwrap()
            })
            .collect_vec();
        assert_eq!(&records[1..], &*read_records);

        let wal = open_wal(&directory);
        let read_records = wal.iter_from(SequenceNumber::MAX).unwrap().map(|res| res.unwrap()).collect_vec();
        assert!(read_records.is_empty());
    }
}
