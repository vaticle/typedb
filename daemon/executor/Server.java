/*
 * GRAKN.AI - THE KNOWLEDGE GRAPH
 * Copyright (C) 2019 Grakn Labs Ltd
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

package grakn.core.daemon.executor;

import grakn.core.common.config.Config;
import grakn.core.common.config.ConfigKey;
import grakn.core.common.config.SystemProperty;
import grakn.core.daemon.exception.GraknDaemonException;
import grakn.core.server.Grakn;

import java.io.File;
import java.io.IOException;
import java.net.Socket;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.stream.Stream;

import static grakn.core.daemon.executor.Executor.WAIT_INTERVAL_SECOND;

/**
 * A class responsible for managing the Server process,
 * including starting, stopping, and performing status checks
 */
public class Server {
    private static final String DISPLAY_NAME = "Grakn Core Server";
    private static final long SERVER_STARTUP_TIMEOUT_S = 300;
    private static final Path SERVER_PIDFILE = Paths.get(System.getProperty("java.io.tmpdir"), "grakn-core-server.pid");
    private static final String JAVA_OPTS = SystemProperty.SERVER_JAVAOPTS.value();
    private static final String LOCALHOST = "127.0.0.1";

    private final Path graknHome;
    private final Path graknPropertiesPath;
    private final Config graknProperties;

    private Executor executor;

    public Server(Executor executor, Path graknHome, Path graknPropertiesPath) {
        this.executor = executor;
        this.graknHome = graknHome;
        this.graknPropertiesPath = graknPropertiesPath;
        this.graknProperties = Config.read(graknPropertiesPath);
    }

    /**
     * @return the main class for Grakn Server. In KGMS, this method will be overridden to return a different class.
     */
    private Class getServerMainClass() {
        return Grakn.class;
    }

    public void startIfNotRunning(String benchmarkFlag) {
        boolean isProcessRunning = executor.isProcessRunning(SERVER_PIDFILE);
        boolean isGraknProcess = executor.isAGraknProcess(SERVER_PIDFILE, Grakn.class.getName());

        if (isProcessRunning && isGraknProcess) {
            System.out.println(DISPLAY_NAME + " is already running");
        } else {
            start(benchmarkFlag);
        }
    }

    public void stop() {
        executor.stopProcessIfRunning(SERVER_PIDFILE, DISPLAY_NAME);
    }

    public void status() {
        executor.processStatus(SERVER_PIDFILE, DISPLAY_NAME, Grakn.class.getName());
    }

    public void clean() {
        System.out.print("Cleaning " + DISPLAY_NAME + "...");
        System.out.flush();
        Path rootPath = graknHome.resolve("logs");
        try (Stream<Path> files = Files.walk(rootPath)) {
            files.sorted(Comparator.reverseOrder())
                    .map(Path::toFile)
                    .forEach(File::delete);
            Files.createDirectories(graknHome.resolve("logs"));
            System.out.println("SUCCESS");
        } catch (IOException e) {
            System.out.println("FAILED!");
            System.out.println("Unable to clean " + DISPLAY_NAME);
        }
    }

    public boolean isRunning() {
        return executor.isProcessRunning(SERVER_PIDFILE);
    }

    private void start(String benchmarkFlag) {
        System.out.print("Starting " + DISPLAY_NAME + "...");
        System.out.flush();

        Future<Executor.Result> startServerAsync = executor.executeAsync(serverCommand(benchmarkFlag), graknHome.toFile());

        LocalDateTime timeout = LocalDateTime.now().plusSeconds(SERVER_STARTUP_TIMEOUT_S);

        while (LocalDateTime.now().isBefore(timeout) && !startServerAsync.isDone()) {
            System.out.print(".");
            System.out.flush();

            int port = graknProperties.getProperty(ConfigKey.GRPC_PORT);

            if (executor.isProcessRunning(SERVER_PIDFILE) && isServerReady(port)) {
                System.out.println("SUCCESS");
                return;
            }
            try {
                Thread.sleep(WAIT_INTERVAL_SECOND * 1000);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        System.out.println("FAILED!");
        System.err.println("Unable to start " + DISPLAY_NAME + ".");
        try {
            String errorMessage = "Process exited with code '" + startServerAsync.get().exitCode() + "': '" + startServerAsync.get().stderr() + "'";
            System.err.println(errorMessage);
            throw new GraknDaemonException(errorMessage);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new GraknDaemonException(e.getMessage(), e);
        } catch (ExecutionException e) {
            throw new GraknDaemonException(e.getMessage(), e);
        }
    }

    private List<String> serverCommand(String benchmarkFlag) {
        ArrayList<String> serverCommand = new ArrayList<>();
        serverCommand.add("java");
        serverCommand.add("-cp");
        serverCommand.add(getServerClassPath());
        serverCommand.add("-Dgrakn.dir=" + graknHome);
        serverCommand.add("-Dgrakn.conf=" + graknPropertiesPath);
        serverCommand.add("-Dgrakn.pidfile=" + SERVER_PIDFILE);
        // This is because https://wiki.apache.org/hadoop/WindowsProblems
        serverCommand.add("-Dhadoop.home.dir=" + graknHome.resolve("server").resolve("services").resolve("hadoop"));
        if (JAVA_OPTS != null && JAVA_OPTS.length() > 0) {//split JAVA OPTS by space and add them to the command
            serverCommand.addAll(Arrays.asList(JAVA_OPTS.split(" ")));
        }
        serverCommand.add(getServerMainClass().getName());

        // benchmarking flag
        serverCommand.add(benchmarkFlag);
        return serverCommand;
    }

    private String getServerClassPath() {
        return graknHome.resolve("server").resolve("services").resolve("lib").toString() + File.separator + "*"
                + File.pathSeparator + graknHome.resolve("server").resolve("conf");
    }

    /**
     * This method is used to make sure that the gRPC server is ready to serve requests.
     * It checks if the gRPC port is used on localhost (this method is only used by grakn startup script
     * which only works on a local machine, it cannot be used to remotely start Grakn)
     */
    private static boolean isServerReady(int port) {
        try {
            Socket s = new Socket(LOCALHOST, port);
            s.close();
            return true;
        } catch (IOException e) {
            return false;
        }
    }
}
