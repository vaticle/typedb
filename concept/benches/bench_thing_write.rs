/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#![deny(unused_must_use)]

use std::{
    borrow::Cow,
    ffi::c_int,
    fs::File,
    path::Path,
    rc::Rc,
    sync::{Arc, OnceLock},
};

use concept::{
    thing::{object::ObjectAPI, thing_manager::ThingManager},
    type_::{
        type_manager::{type_cache::TypeCache, TypeManager},
        Ordering, OwnerAPI,
    },
};
use criterion::{criterion_group, criterion_main, profiler::Profiler, Criterion, SamplingMode};
use durability::wal::WAL;
use encoding::{
    graph::{
        definition::definition_key_generator::DefinitionKeyGenerator, thing::vertex_generator::ThingVertexGenerator,
        type_::vertex_generator::TypeVertexGenerator,
    },
    value::{label::Label, value::Value, value_type::ValueType},
    EncodingKeyspace,
};
use pprof::ProfilerGuard;
use rand::distributions::{Alphanumeric, DistString};
use storage::{
    durability_client::WALClient,
    snapshot::{CommittableSnapshot, WriteSnapshot},
    MVCCStorage,
};
use test_utils::{create_tmp_dir, init_logging};

static AGE_LABEL: OnceLock<Label> = OnceLock::new();
static NAME_LABEL: OnceLock<Label> = OnceLock::new();
static PERSON_LABEL: OnceLock<Label> = OnceLock::new();

fn write_entity_attributes(
    storage: Arc<MVCCStorage<WALClient>>,
    definition_key_generator: Arc<DefinitionKeyGenerator>,
    type_vertex_generator: Arc<TypeVertexGenerator>,
    thing_vertex_generator: Arc<ThingVertexGenerator>,
    schema_cache: Arc<TypeCache>,
) {
    let mut snapshot = storage.clone().open_snapshot_write();
    {
        let type_manager = Arc::new(TypeManager::new(
            definition_key_generator.clone(),
            type_vertex_generator.clone(),
            Some(schema_cache),
        ));
        let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());

        let person_type = type_manager.get_entity_type(&snapshot, PERSON_LABEL.get().unwrap()).unwrap().unwrap();
        let age_type = type_manager.get_attribute_type(&snapshot, AGE_LABEL.get().unwrap()).unwrap().unwrap();
        let name_type = type_manager.get_attribute_type(&snapshot, NAME_LABEL.get().unwrap()).unwrap().unwrap();
        let person = thing_manager.create_entity(&mut snapshot, person_type).unwrap();

        let random_long: i64 = rand::random();
        let length: u8 = rand::random();
        let random_string: String = Alphanumeric.sample_string(&mut rand::thread_rng(), length as usize);

        let age = thing_manager.create_attribute(&mut snapshot, age_type, Value::Long(random_long)).unwrap();
        let name = thing_manager
            .create_attribute(&mut snapshot, name_type, Value::String(Cow::Borrowed(&random_string)))
            .unwrap();
        person.set_has_unordered(&mut snapshot, &thing_manager, age).unwrap();
        person.set_has_unordered(&mut snapshot, &thing_manager, name).unwrap();
    }

    snapshot.commit().unwrap();
}

fn create_schema(
    storage: Arc<MVCCStorage<WALClient>>,
    definition_key_generator: Arc<DefinitionKeyGenerator>,
    type_vertex_generator: Arc<TypeVertexGenerator>,
) {
    let mut snapshot: WriteSnapshot<WALClient> = storage.clone().open_snapshot_write();
    {
        let type_manager =
            Rc::new(TypeManager::new(definition_key_generator.clone(), type_vertex_generator.clone(), None));
        let age_type = type_manager.create_attribute_type(&mut snapshot, AGE_LABEL.get().unwrap(), false).unwrap();
        age_type.set_value_type(&mut snapshot, &type_manager, ValueType::Long).unwrap();
        let name_type = type_manager.create_attribute_type(&mut snapshot, NAME_LABEL.get().unwrap(), false).unwrap();
        name_type.set_value_type(&mut snapshot, &type_manager, ValueType::String).unwrap();
        let person_type = type_manager.create_entity_type(&mut snapshot, PERSON_LABEL.get().unwrap(), false).unwrap();
        person_type.set_owns(&mut snapshot, &type_manager, age_type, Ordering::Unordered).unwrap();
        person_type.set_owns(&mut snapshot, &type_manager, name_type, Ordering::Unordered).unwrap();
    }
    snapshot.commit().unwrap();
}

fn criterion_benchmark(c: &mut Criterion) {
    AGE_LABEL.set(Label::build("age")).unwrap();
    NAME_LABEL.set(Label::build("name")).unwrap();
    PERSON_LABEL.set(Label::build("person")).unwrap();
    init_logging();

    let mut group = c.benchmark_group("test writes");
    group.sample_size(1000);
    // group.measurement_time(Duration::from_secs(60*5));
    group.sampling_mode(SamplingMode::Linear);
    group.bench_function("thing_write", |b| {
        let storage_path = create_tmp_dir();
        let wal = WAL::create(&storage_path).unwrap();
        let storage = Arc::new(
            MVCCStorage::<WALClient>::create::<EncodingKeyspace>("storage", &storage_path, WALClient::new(wal))
                .unwrap(),
        );
        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        TypeManager::initialise_types(storage.clone(), definition_key_generator.clone(), type_vertex_generator.clone())
            .unwrap();
        create_schema(storage.clone(), definition_key_generator.clone(), type_vertex_generator.clone());
        let schema_cache = Arc::new(TypeCache::new(storage.clone(), storage.read_watermark()).unwrap());
        b.iter(|| {
            write_entity_attributes(
                storage.clone(),
                definition_key_generator.clone(),
                type_vertex_generator.clone(),
                thing_vertex_generator.clone(),
                schema_cache.clone(),
            )
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
        let flamegraph_file = File::create(flamegraph_path).expect("File system error while creating flamegraph.svg");
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
