/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;

use concept::{error::ConceptWriteError, thing::thing_manager::ThingManager, type_::type_manager::TypeManager};
use storage::{
    durability_client::DurabilityClient,
    snapshot::{CommittableSnapshot, ReadSnapshot, SchemaSnapshot, WritableSnapshot, WriteSnapshot},
};

use super::Database;

pub struct TransactionRead<D> {
    database: Arc<Database<D>>,
    pub snapshot: ReadSnapshot<D>,
    pub type_manager: Arc<TypeManager>,
    pub thing_manager: ThingManager,
}

impl<D: DurabilityClient> TransactionRead<D> {
    pub fn open(database: Arc<Database<D>>) -> Self {
        // TODO: when we implement constructor `open_at`, to open a transaction in the past by time/sequence number, we need to check whether
        //       the statistics that is available is "too far" ahead of the version we're opening (100-1000?)
        //          note: this can also be the approximate frequency at which we persist statistics snapshots to the WAL!
        //       this should be a constant defined in constants.rs
        //       If it's too far in the future, we should find a more appropriate statistics snapshot from the WAL

        let snapshot: ReadSnapshot<D> = database.storage.clone().open_snapshot_read();
        let type_manager = Arc::new(TypeManager::new(
            database.definition_key_generator.clone(),
            database.type_vertex_generator.clone(),
            None,
        )); // TODO pass cache
        let thing_manager = ThingManager::new(database.thing_vertex_generator.clone(), type_manager.clone());
        Self { database, snapshot, type_manager, thing_manager }
    }

    pub fn close(self) {
        drop(self.thing_manager);
        drop(self.type_manager);
        self.snapshot.close_resources()
    }
}

pub struct TransactionWrite<D> {
    database: Arc<Database<D>>,
    pub snapshot: WriteSnapshot<D>,
    pub type_manager: Arc<TypeManager>,
    pub thing_manager: ThingManager,
}

impl<D: DurabilityClient> TransactionWrite<D> {
    pub fn open(database: Arc<Database<D>>) -> Self {
        let snapshot: WriteSnapshot<D> = database.storage.clone().open_snapshot_write();
        let type_manager = Arc::new(TypeManager::new(
            database.definition_key_generator.clone(),
            database.type_vertex_generator.clone(),
            None,
        )); // TODO pass cache
        let thing_manager = ThingManager::new(database.thing_vertex_generator.clone(), type_manager.clone());
        Self { database, snapshot, type_manager, thing_manager }
    }

    pub fn commit(mut self) -> Result<(), Vec<ConceptWriteError>> {
        self.thing_manager.finalise(&mut self.snapshot)?;
        drop(self.type_manager);
        // TODO: pass error up
        self.snapshot.commit().unwrap_or_else(|_| panic!("Failed to commit snapshot"));
        Ok(())
    }

    pub fn close(self) {
        drop(self.thing_manager);
        drop(self.type_manager);
        self.snapshot.close_resources();
    }
}

pub struct TransactionSchema<D> {
    database: Arc<Database<D>>,
    pub snapshot: SchemaSnapshot<D>,
    pub type_manager: Arc<TypeManager>, // TODO: krishnan: Should this be an arc or direct ownership?
    pub thing_manager: ThingManager,
}

impl<D: DurabilityClient> TransactionSchema<D> {
    pub fn open(database: Arc<Database<D>>) -> Self {
        let snapshot: SchemaSnapshot<D> = database.storage.clone().open_snapshot_schema();
        let type_manager = Arc::new(TypeManager::new(
            database.definition_key_generator.clone(),
            database.type_vertex_generator.clone(),
            None,
        ));
        let thing_manager = ThingManager::new(database.thing_vertex_generator.clone(), type_manager.clone());

        // TODO: take WRITE schema transaction lock (data write transactions take it as READ) - prevents data txn while schema txn running

        Self { database, snapshot, type_manager, thing_manager }
    }

    pub fn commit(mut self) -> Result<(), Vec<ConceptWriteError>> {
        // TODO: 1. synchronise statistics
        //       2. flush statistics to WAL, guaranteeing a version of statistics is in WAL before schema can change

        self.thing_manager.finalise(&mut self.snapshot)?;
        let type_manager_owned = Arc::try_unwrap(self.type_manager).unwrap_or_else(|_| {
            panic!("Failed to unwrap type_manager arc");
        });
        type_manager_owned.finalise(&self.snapshot)?;

        // TODO: take lock to prevent new read transactions from opening

        self.snapshot.commit().unwrap_or_else(|_| {
            panic!("Failed to commit snapshot");
        });

        // replace Schema cache
        // replace statistics

        Ok(())
    }

    pub fn close(self) {
        drop(self.thing_manager);
        drop(self.type_manager);
        self.snapshot.close_resources();
    }
}
