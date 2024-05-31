/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

package com.vaticle.typedb.core.database;

import com.google.ortools.Loader;
import com.vaticle.typedb.core.TypeDB;
import com.vaticle.typedb.core.common.diagnostics.Diagnostics;
import com.vaticle.typedb.core.common.diagnostics.Metrics;
import com.vaticle.typedb.core.common.exception.ErrorMessage;
import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.parameters.Arguments;
import com.vaticle.typedb.core.common.parameters.Options;
import com.vaticle.typedb.core.concurrent.executor.Executors;
import org.rocksdb.RocksDB;

import java.io.File;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Database.DATABASE_EXISTS;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Database.DATABASE_MANAGER_CLOSED;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Database.DATABASE_NAME_RESERVED;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Database.DATABASE_NOT_FOUND;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.TYPEDB_CLOSED;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.UNKNOWN_ERROR;

public class CoreDatabaseManager implements TypeDB.DatabaseManager {

    static final int MAX_THREADS = Runtime.getRuntime().availableProcessors();

    static {
        RocksDB.loadLibrary();
        Loader.loadNativeLibraries();
        ErrorMessage.loadConstants();
    }

    protected static final String RESERVED_NAME_PREFIX = "_";

    protected static final int DIAGNOSTICS_SYNC_PERIOD_MINUTES = 1;

    private final Options.Database databaseOptions;
    protected final ConcurrentMap<String, CoreDatabase> databases;
    protected final Factory.Database databaseFactory;
    protected final AtomicBoolean isOpen;

    public static CoreDatabaseManager open(Path directory, Factory factory) {
        return open(new Options.Database().dataDir(directory), factory);
    }

    public static CoreDatabaseManager open(Options.Database databaseOptions) {
        return open(databaseOptions, new CoreFactory());
    }

    public static CoreDatabaseManager open(Options.Database databaseOptions, Factory factory) {
        return factory.databaseManager(databaseOptions);
    }

    protected CoreDatabaseManager(Options.Database databaseOptions, Factory.Database databaseFactory) {
        if (!Executors.isInitialised()) Executors.initialise(MAX_THREADS);
        this.databaseOptions = databaseOptions;
        this.databaseFactory = databaseFactory;
        databases = new ConcurrentHashMap<>();
        isOpen = new AtomicBoolean(true);
        loadAll();

        // Send first portion in the same thread to have a guarantee of it being sent before the end of the initialization.
        synchronizeDatabaseDiagnostics();
        Executors.scheduled().scheduleAtFixedRate(
                this::synchronizeDatabaseDiagnostics,
                1,
                15,
                TimeUnit.SECONDS);
    }

    @Override
    public boolean isOpen() {
        return this.isOpen.get();
    }

    protected void loadAll() {
        File[] databaseDirectories = directory().toFile().listFiles(File::isDirectory);
        if (databaseDirectories != null && databaseDirectories.length > 0) {
            List<CompletableFuture<Void>> dbLoads = Arrays.stream(databaseDirectories)
                    .filter(file -> CoreDatabase.isExistingDatabaseDirectory(file.toPath()))
                    .map(directory ->
                            CompletableFuture.runAsync(() -> {
                                String name = directory.getName();
                                CoreDatabase database = databaseFactory.databaseLoadAndOpen(this, name);
                                databases.put(name, database);
                            }, Executors.async1())
                    ).collect(Collectors.toList());
            try {
                // once all future complete, we will catch any exceptions in order to close all databases cleanly
                CompletableFuture.allOf(dbLoads.toArray(new CompletableFuture[0])).join();
            } catch (CompletionException e) {
                close();
                if (e.getCause() instanceof TypeDBException) throw (TypeDBException) e.getCause();
                else throw TypeDBException.of(UNKNOWN_ERROR, e);
            }
        }
    }

    @Override
    public boolean contains(String name) {
        if (!isOpen.get()) throw TypeDBException.of(DATABASE_MANAGER_CLOSED);
        if (isReservedName(name)) throw TypeDBException.of(DATABASE_NAME_RESERVED);
        return databases.containsKey(name);
    }

    @Override
    public CoreDatabase create(String name) {
        if (!isOpen.get()) throw TypeDBException.of(DATABASE_MANAGER_CLOSED);
        if (isReservedName(name)) throw TypeDBException.of(DATABASE_NAME_RESERVED);
        if (databases.containsKey(name)) throw TypeDBException.of(DATABASE_EXISTS, name);

        CoreDatabase database = databaseFactory.databaseCreateAndOpen(this, name);
        databases.put(name, database);
        return database;
    }

    @Override
    public CoreDatabase get(String name) {
        if (!isOpen.get()) throw TypeDBException.of(DATABASE_MANAGER_CLOSED);
        if (isReservedName(name)) throw TypeDBException.of(DATABASE_NAME_RESERVED);
        return databases.get(name);
    }

    @Override
    public Set<CoreDatabase> all() {
        if (!isOpen.get()) throw TypeDBException.of(DATABASE_MANAGER_CLOSED);
        return databases.values().stream().filter(database -> !isReservedName(database.name())).collect(Collectors.toSet());
    }

    void remove(CoreDatabase database) {
        databases.remove(database.name());
    }

    @Override
    public CoreSession session(String database, Arguments.Session.Type type) {
        return session(database, type, new Options.Session());
    }

    @Override
    public CoreSession session(String database, Arguments.Session.Type type, Options.Session options) {
        if (!isOpen.get()) throw TypeDBException.of(TYPEDB_CLOSED);
        if (contains(database)) return get(database).createAndOpenSession(type, options);
        else throw TypeDBException.of(DATABASE_NOT_FOUND, database);
    }

    public Path directory() {
        return databaseOptions.dataDir();
    }

    public Options.Database options() {
        return databaseOptions;
    }

    @Override
    public void close() {
        if (isOpen.compareAndSet(true, false)) {
            databases.values().parallelStream().forEach(CoreDatabase::close);
        }
    }

    protected static boolean isReservedName(String name) {
        return name.startsWith(RESERVED_NAME_PREFIX);
    }

    protected Metrics.DatabaseDiagnostics databaseDiagnostics(
            TypeDB.Database database, Metrics.DatabaseSchemaLoad schemaLoad, Metrics.DatabaseDataLoad dataLoad
    ) {
        return new Metrics.DatabaseDiagnostics(database.name(), schemaLoad, dataLoad, true);
    }

    private void synchronizeDatabaseDiagnostics() {
        Set<Metrics.DatabaseDiagnostics> diagnostics = new HashSet<>();

        for (CoreDatabase database : all()) {
            Metrics.DatabaseSchemaLoad schemaLoad = new Metrics.DatabaseSchemaLoad(database.typeCount());
            Metrics.DatabaseDataLoad dataLoad = new Metrics.DatabaseDataLoad(
                    database.entityCount(),
                    database.relationCount(),
                    database.attributeCount(),
                    database.hasCount(),
                    database.roleCount(),
                    database.storageDataBytesEstimate(),
                    database.storageDataKeysEstimate());

            diagnostics.add(databaseDiagnostics(database, schemaLoad, dataLoad));
        }

        Diagnostics.get().synchronizeDatabaseDiagnostics(diagnostics);
    }
}
