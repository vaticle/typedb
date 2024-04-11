/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::{
    ffi::c_int,
    fs::File,
    path::Path,
    rc::Rc,
    sync::{Arc, OnceLock},
};
use std::borrow::Cow;

use concept::{
    thing::{thing_manager::ThingManager, value::Value},
    type_::{type_cache::TypeCache, type_manager::TypeManager, OwnerAPI},
};
use criterion::{criterion_group, criterion_main, profiler::Profiler, Criterion};
use durability::wal::WAL;
use encoding::{
    graph::{thing::vertex_generator::ThingVertexGenerator, type_::vertex_generator::TypeVertexGenerator},
    value::{label::Label, value_type::ValueType},
    EncodingKeyspace,
};
use pprof::ProfilerGuard;
use rand::distributions::{Alphanumeric, DistString};
use storage::{MVCCStorage};
use storage::snapshot::{CommittableSnapshot, WriteSnapshot};
use test_utils::{create_tmp_dir, init_logging};

static AGE_LABEL: OnceLock<Label> = OnceLock::new();
static NAME_LABEL: OnceLock<Label> = OnceLock::new();
static PERSON_LABEL: OnceLock<Label> = OnceLock::new();

fn write_entity_attributes(
    storage: &MVCCStorage<WAL>,
    type_vertex_generator: &TypeVertexGenerator,
    thing_vertex_generator: &ThingVertexGenerator,
    schema_cache: Arc<TypeCache>,
) {
    let snapshot = Rc::new(storage.open_snapshot_write());
    {
        let type_manager = Rc::new(TypeManager::new(snapshot.clone(), type_vertex_generator, Some(schema_cache)));
        let thing_manager = ThingManager::new(snapshot.clone(), thing_vertex_generator, type_manager.clone());

        let person_type = type_manager.get_entity_type(PERSON_LABEL.get().unwrap()).unwrap().unwrap();
        let age_type = type_manager.get_attribute_type(AGE_LABEL.get().unwrap()).unwrap().unwrap();
        let name_type = type_manager.get_attribute_type(NAME_LABEL.get().unwrap()).unwrap().unwrap();
        let person = thing_manager.create_entity(person_type).unwrap();

        let random_long: i64 = rand::random();
        let length: u8 = rand::random();
        let random_string: String = Alphanumeric.sample_string(&mut rand::thread_rng(), length as usize);

        let age = thing_manager.create_attribute(age_type, Value::Long(random_long)).unwrap();
        let name = thing_manager.create_attribute(name_type, Value::String(Cow::Owned(random_string.into_boxed_str()))).unwrap();
        person.set_has(&thing_manager, age);
        person.set_has(&thing_manager, name);
    }

    let write_snapshot = Rc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();
}

fn create_schema(storage: &MVCCStorage<WAL>, type_vertex_generator: &TypeVertexGenerator) {
    let snapshot: Rc<WriteSnapshot<'_, WAL>> = Rc::new(storage.open_snapshot_write());
    {
        let type_manager = Rc::new(TypeManager::new(snapshot.clone(), type_vertex_generator, None));
        let age_type = type_manager.create_attribute_type(AGE_LABEL.get().unwrap(), false);
        age_type.set_value_type(&type_manager, ValueType::Long);
        let name_type = type_manager.create_attribute_type(NAME_LABEL.get().unwrap(), false);
        name_type.set_value_type(&type_manager, ValueType::String);
        let person_type = type_manager.create_entity_type(PERSON_LABEL.get().unwrap(), false);
        person_type.set_owns(&type_manager, age_type);
        person_type.set_owns(&type_manager, name_type);
    }
    let write_snapshot = Rc::try_unwrap(snapshot).ok().unwrap();
    write_snapshot.commit().unwrap();
}

fn criterion_benchmark(c: &mut Criterion) {
    AGE_LABEL.set(Label::build("age")).unwrap();
    NAME_LABEL.set(Label::build("name")).unwrap();
    PERSON_LABEL.set(Label::build("person")).unwrap();

    init_logging();
    let storage_path = create_tmp_dir();
    let mut storage = MVCCStorage::<WAL>::recover::<EncodingKeyspace>("storage", &storage_path).unwrap();
    let type_vertex_generator = TypeVertexGenerator::new();
    let thing_vertex_generator = ThingVertexGenerator::new();
    TypeManager::<'_, WriteSnapshot<'_, WAL>>::initialise_types(&mut storage, &type_vertex_generator);

    create_schema(&storage, &type_vertex_generator);
    let schema_cache = Arc::new(TypeCache::new(&storage, storage.read_watermark()).unwrap());

    let mut group = c.benchmark_group("test writes");
    group.bench_function("thing_write", |b| {
        b.iter(|| {
            write_entity_attributes(&storage, &type_vertex_generator, &thing_vertex_generator, schema_cache.clone())
        });
    });
}

pub struct FlamegraphProfiler<'a> {
    frequency: c_int,
    active_profiler: Option<ProfilerGuard<'a>>,
}

impl<'a> FlamegraphProfiler<'a> {
    #[allow(dead_code)]
    pub fn new(frequency: c_int) -> Self {
        Self { frequency, active_profiler: None }
    }
}

impl<'a> Profiler for FlamegraphProfiler<'a> {
    fn start_profiling(&mut self, _benchmark_id: &str, _benchmark_dir: &Path) {
        self.active_profiler = Some(ProfilerGuard::new(self.frequency).unwrap());
    }

    fn stop_profiling(&mut self, _benchmark_id: &str, benchmark_dir: &Path) {
        std::fs::create_dir_all(benchmark_dir).unwrap();
        let flamegraph_path = benchmark_dir.join("flamegraph.svg");
        let flamegraph_file = File::create(&flamegraph_path).expect("File system error while creating flamegraph.svg");
        if let Some(profiler) = self.active_profiler.take() {
            profiler.report().build().unwrap().flamegraph(flamegraph_file).expect("Error writing flamegraph");
        }
    }
}

fn profiled() -> Criterion {
    Criterion::default().with_profiler(FlamegraphProfiler::new(1000))
}

criterion_group!(
    name = benches;
    config= profiled();
    targets = criterion_benchmark
);

criterion_main!(benches);

// TODO: disable profiling when running on mac, since pprof seems to crash
// criterion_group!(benches, criterion_benchmark);
// criterion_main!(benches);
