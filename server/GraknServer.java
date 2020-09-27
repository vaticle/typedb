/*
 * Copyright (C) 2020 Grakn Labs
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
import grakn.common.collection.Pair;
import grakn.common.concurrent.NamedThreadFactory;
import grakn.core.Grakn;
import grakn.core.common.exception.GraknException;
import grakn.core.rocks.RocksGrakn;
import grakn.core.server.rpc.GraknRPC;
import grakn.core.server.util.ServerDefaults;
import grakn.core.server.util.ServerOptions;
import io.grpc.Server;
import io.grpc.netty.NettyServerBuilder;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioServerSocketChannel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;
import picocli.CommandLine.ParameterException;
import picocli.CommandLine.PropertiesDefaultProvider;
import picocli.CommandLine.UnmatchedArgumentException;

import java.io.FileInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static grakn.core.common.exception.ErrorMessage.Server.DATA_DIRECTORY_NOT_FOUND;
import static grakn.core.common.exception.ErrorMessage.Server.ENV_VAR_NOT_FOUND;
import static grakn.core.common.exception.ErrorMessage.Server.EXITED_WITH_ERROR;
import static grakn.core.common.exception.ErrorMessage.Server.FAILED_AT_STOPPING;
import static grakn.core.common.exception.ErrorMessage.Server.FAILED_PARSE_PROPERTIES;
import static grakn.core.common.exception.ErrorMessage.Server.PROPERTIES_FILE_NOT_FOUND;
import static grakn.core.common.exception.ErrorMessage.Server.UNCAUGHT_EXCEPTION;
import static grakn.core.server.util.ServerDefaults.ASCII_LOGO_FILE;
import static grakn.core.server.util.ServerDefaults.PROPERTIES_FILE;


public class GraknServer implements AutoCloseable {

    private static final Logger LOG = LoggerFactory.getLogger(GraknServer.class);
    private static final int MAX_THREADS = Runtime.getRuntime().availableProcessors();
    private static final int MAX_THREADS_X_2 = MAX_THREADS * 2;

    private Grakn grakn;
    private GraknRPC graknRPC;
    private Server server;
    private ServerOptions options;

    private GraknServer(ServerOptions options) throws IOException {
        this.options = options;
        configureDataDir();
        configureTracing();

        grakn = RocksGrakn.open(options.dataDir());
        graknRPC = new GraknRPC(grakn);
        server = rpcServer();
        Runtime.getRuntime().addShutdownHook(NamedThreadFactory.create(GraknServer.class, "shutdown").newThread(this::close));
        Thread.setDefaultUncaughtExceptionHandler((Thread t, Throwable e) -> LOG.error(UNCAUGHT_EXCEPTION.message(t.getName()), e));
    }

    private void configureDataDir() throws IOException {
        if (!Files.isDirectory(this.options.dataDir())) {
            if (this.options.dataDir().equals(ServerDefaults.DATA_DIR)) {
                Files.createDirectory(this.options.dataDir());
            } else {
                throw new GraknException(DATA_DIRECTORY_NOT_FOUND.message(this.options.dataDir()));
            }
        }
    }

    private void configureTracing() {
        if (this.options.grablTrace()) {
            GrablTracing grablTracingClient;
            grablTracingClient = GrablTracing.withLogging(GrablTracing.tracing(
                    options.grablURI().toString(),
                    options.grablUsername(),
                    options.grablToken()
            ));
            GrablTracingThreadStatic.setGlobalTracingClient(grablTracingClient);
            GraknServer.LOG.info("Grabl tracing is enabled");
        }
    }

    private static void printASCIILogo() throws IOException {
        if (ASCII_LOGO_FILE.exists()) {
            LOG.info(new String(Files.readAllBytes(ASCII_LOGO_FILE.toPath()), StandardCharsets.UTF_8));
        }
    }

    private static Properties parseProperties() {
        Properties properties = new Properties();
        boolean error = false;

        try {
            properties.load(new FileInputStream(PROPERTIES_FILE));
        } catch (IOException e) {
            LOG.error(PROPERTIES_FILE_NOT_FOUND.message(PROPERTIES_FILE.toString()));
            error = true;
        }

        for (Map.Entry<Object, Object> entry : properties.entrySet()) {
            String val = (String) entry.getValue();
            if (val.startsWith("$")) {
                String envVarName = val.substring(1);
                if (System.getenv(envVarName) == null) {
                    LOG.error(ENV_VAR_NOT_FOUND.message(val));
                    error = true;
                } else {
                    properties.put(entry.getKey(), System.getenv(envVarName));
                }
            }
        }

        if (error) throw new GraknException(FAILED_PARSE_PROPERTIES);
        else return properties;
    }

    private static Pair<Boolean, ServerOptions> parseCommandLine(Properties properties, String[] args) {
        ServerOptions options = new ServerOptions();
        boolean proceed;
        CommandLine command = new CommandLine(options);
        command.setDefaultValueProvider(new PropertiesDefaultProvider(properties));

        try {
            command.parseArgs(args);
            if (command.isUsageHelpRequested()) {
                command.usage(command.getOut());
                proceed = false;
            } else if (command.isVersionHelpRequested()) {
                command.printVersionHelp(command.getOut());
                proceed = false;
            } else {
                proceed = true;
            }
        } catch (ParameterException ex) {
            command.getErr().println(ex.getMessage());
            if (!UnmatchedArgumentException.printSuggestions(ex, command.getErr())) {
                ex.getCommandLine().usage(command.getErr());
            }
            proceed = false;
        }

        return new Pair<>(proceed, options);
    }

    public static void main(String[] args) {
        try {
            long start = System.nanoTime();

            printASCIILogo();
            Pair<Boolean, ServerOptions> result = parseCommandLine(parseProperties(), args);
            if (!result.first()) System.exit(0);

            GraknServer server = new GraknServer(result.second());
            server.start();

            long end = System.nanoTime();
            LOG.info("Grakn Core version: {}", Version.VERSION);
            LOG.info("Grakn Core Server has been started (in {} ms)",
                     String.format("%.3f", (end - start) / 1_000_000.00));

            server.serve();
        } catch (Exception e) {
            LOG.error(e.getMessage());
            LOG.error(EXITED_WITH_ERROR.message());
            System.exit(1);
        }

        System.exit(0);
    }

    private Server rpcServer() {
        NioEventLoopGroup workerELG = new NioEventLoopGroup(MAX_THREADS, NamedThreadFactory.create(GraknServer.class, "worker"));
        return NettyServerBuilder.forPort(options.port())
                .executor(Executors.newFixedThreadPool(MAX_THREADS_X_2, NamedThreadFactory.create(GraknServer.class, "executor")))
                .workerEventLoopGroup(workerELG)
                .bossEventLoopGroup(workerELG)
                .maxConnectionIdle(1, TimeUnit.HOURS) // TODO: why 1 hour?
                .channelType(NioServerSocketChannel.class)
                .addService(graknRPC)
                .build();
    }

    @Override
    public void close() {
        LOG.info("");
        LOG.info("Shutting down Grakn Core Server...");
        try {
            graknRPC.close();
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

    private void start() throws IOException {
        try {
            server.start();
        } catch (Exception e) {
            LOG.error(e.getMessage(), e);
            throw e;
        }
    }

    private void serve() {
        try {
            server.awaitTermination();
        } catch (InterruptedException e) {
            // grakn server stop is called
            close();
            Thread.currentThread().interrupt();
        }
    }

}
