/*
 * Copyright (C) 2021 Grakn Labs
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
 *
 */

package grakn.core.server;

import grabl.tracing.client.GrablTracing;
import grabl.tracing.client.GrablTracingThreadStatic;
import grakn.common.concurrent.NamedThreadFactory;
import grakn.core.Grakn;
import grakn.core.common.exception.GraknException;
import grakn.core.common.parameters.Options;
import grakn.core.concurrent.common.Executors;
import grakn.core.migrator.MigratorClient;
import grakn.core.rocks.Factory;
import grakn.core.rocks.RocksFactory;
import grakn.core.server.common.ServerCommand;
import grakn.core.server.common.ServerDefaults;
import io.grpc.Server;
import io.grpc.netty.NettyServerBuilder;
import io.netty.channel.socket.nio.NioServerSocketChannel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.BindException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.time.Instant;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;

import static grakn.core.common.exception.ErrorMessage.Server.ALREADY_RUNNING;
import static grakn.core.common.exception.ErrorMessage.Server.DATA_DIRECTORY_NOT_FOUND;
import static grakn.core.common.exception.ErrorMessage.Server.DATA_DIRECTORY_NOT_WRITABLE;
import static grakn.core.common.exception.ErrorMessage.Server.EXITED_WITH_ERROR;
import static grakn.core.common.exception.ErrorMessage.Server.FAILED_AT_STOPPING;

import static grakn.core.common.exception.ErrorMessage.Server.UNCAUGHT_EXCEPTION;
import static grakn.core.server.common.Util.parseCommandLine;
import static grakn.core.server.common.Util.parseProperties;
import static grakn.core.server.common.Util.printASCIILogo;


public class GraknServer implements AutoCloseable {

    private static final Logger LOG = LoggerFactory.getLogger(GraknServer.class);

    protected final Factory factory;
    protected final Grakn grakn;
    protected final Server server;
    protected GraknService graknService;
    private MigratorService migratorService;
    protected final ServerCommand.Start command;

    private GraknServer(ServerCommand.Start command) {
        this(command, new RocksFactory());
    }

    protected GraknServer(ServerCommand.Start command, Factory factory) {
        this.command = command;
        configureAndVerifyDataDir();
        configureTracing();

        if (command.debug()) LOG.info("Running {} in debug mode.", name());

        Options.Database options = new Options.Database()
                .graknDir(ServerDefaults.GRAKN_DIR)
                .dataDir(command.dataDir())
                .logsDir(command.logsDir());
        this.factory = factory;
        grakn = factory.grakn(options);
        server = rpcServer();
        Thread.setDefaultUncaughtExceptionHandler(
                (t, e) -> LOG.error(UNCAUGHT_EXCEPTION.message(t.getName() + ": " + e.getMessage()), e)
        );
        Runtime.getRuntime().addShutdownHook(
                NamedThreadFactory.create(GraknServer.class, "shutdown").newThread(this::close)
        );

        initLoggerConfig();
    }

    private void configureAndVerifyDataDir() {
        if (!Files.isDirectory(this.command.dataDir())) {
            if (this.command.dataDir().equals(ServerDefaults.DATA_DIR)) {
                try {
                    Files.createDirectory(this.command.dataDir());
                } catch (IOException e) {
                    throw GraknException.of(e);
                }
            } else {
                throw GraknException.of(DATA_DIRECTORY_NOT_FOUND, this.command.dataDir());
            }
        }

        if (!Files.isWritable(this.command.dataDir())) {
            throw GraknException.of(DATA_DIRECTORY_NOT_WRITABLE, this.command.dataDir());
        }
    }

    private void configureTracing() {
        if (this.command.grablTrace()) {
            GrablTracing grablTracingClient;
            grablTracingClient = GrablTracing.withLogging(GrablTracing.tracing(
                    command.grablURI().toString(),
                    command.grablUsername(),
                    command.grablToken()
            ));
            GrablTracingThreadStatic.setGlobalTracingClient(grablTracingClient);
            LOG.info("Grabl tracing is enabled");
        }
    }

    protected Server rpcServer() {
        assert Executors.isInitialised();

        graknService = new GraknService(grakn);
        migratorService = new MigratorService(grakn);

        return NettyServerBuilder.forPort(command.port())
                .executor(Executors.service())
                .workerEventLoopGroup(Executors.network())
                .bossEventLoopGroup(Executors.network())
                .maxConnectionIdle(1, TimeUnit.HOURS) // TODO: why 1 hour?
                .channelType(NioServerSocketChannel.class)
                .addService(graknService)
                .addService(migratorService)
                .build();
    }

    private void initLoggerConfig() {
        java.util.logging.Logger.getLogger("io.grpc").setLevel(Level.SEVERE);
    }

    protected String name() {
        return "Grakn Core Server";
    }

    private int port() {
        return command.port();
    }

    protected Path dataDir() {
        return command.dataDir();
    }

    protected void start() {
        try {
            server.start();
            LOG.info("{} is now running and will keep this process alive.", name());
            LOG.info("You can press CTRL+C to shutdown this server.");
            LOG.info("");
        } catch (IOException e) {
            if (e.getCause() != null && e.getCause() instanceof BindException) {
                throw GraknException.of(ALREADY_RUNNING, port());
            } else {
                throw new RuntimeException(e);
            }
        }
    }

    protected void serve() {
        try {
            server.awaitTermination();
        } catch (InterruptedException e) {
            // server is terminated
            close();
            Thread.currentThread().interrupt();
        }
    }

    @Override
    public void close() {
        LOG.info("");
        LOG.info("Shutting down {}...", name());
        try {
            assert graknService != null;
            graknService.close();
            server.shutdown();
            server.awaitTermination();
            grakn.close();
            System.runFinalization();
            LOG.info("Grakn Core Server has been shutdown");
        } catch (InterruptedException e) {
            LOG.error(FAILED_AT_STOPPING.message(), e);
            Thread.currentThread().interrupt();
        }
    }

    public static void main(String[] args) {
        try {
            printASCIILogo();
            ServerCommand command = parseCommandLine(parseProperties(), args);
            if (command == null) System.exit(0);

            if (command.isStart()) {
                startGraknServer(command.asStart());
            } else if (command.isImportData()) {
                importData(command.asImportData());
            } else if (command.isExportData()) {
                exportData(command.asExportData());
            } else if (command.isPrintSchema()) {
                ServerCommand.PrintSchema printSchemaCommand = command.asPrintSchema();
                printSchema(printSchemaCommand);
            }
        } catch (Exception e) {
            if (e instanceof GraknException) {
                LOG.error(e.getMessage());
            } else {
                LOG.error(e.getMessage(), e);
                LOG.error(EXITED_WITH_ERROR.message());
            }
            System.exit(1);
        }

        System.exit(0);
    }

    private static void startGraknServer(ServerCommand.Start command) {
        Instant start = Instant.now();
        GraknServer server = new GraknServer(command);
        server.start();
        Instant end = Instant.now();
        LOG.info("- version: {}", Version.VERSION);
        LOG.info("- listening to port: {}", server.port());
        LOG.info("- data directory configured to: {}", server.dataDir());
        LOG.info("- bootup completed in: {} ms", Duration.between(start, end).toMillis());
        LOG.info("...");
        server.serve();
    }

    protected static void printSchema(ServerCommand.PrintSchema printSchemaCommand) {
        MigratorClient migrator = new MigratorClient(printSchemaCommand.port());
        migrator.printSchema(printSchemaCommand.database());
    }

    protected static void exportData(ServerCommand.ExportData exportDataCommand) {
        MigratorClient migrator = new MigratorClient(exportDataCommand.port());
        boolean success = migrator.exportData(exportDataCommand.database(), exportDataCommand.filename());
        System.exit(success ? 0 : 1);
    }

    protected static void importData(ServerCommand.ImportData importDataCommand) {
        MigratorClient migrator = new MigratorClient(importDataCommand.port());
        boolean success = migrator.importData(importDataCommand.database(), importDataCommand.filename(), importDataCommand.remapLabels());
        System.exit(success ? 0 : 1);
    }
}
