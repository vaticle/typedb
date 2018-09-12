/*
 * GRAKN.AI - THE KNOWLEDGE GRAPH
 * Copyright (C) 2018 Grakn Labs Ltd
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

package ai.grakn.engine.bootup;

import ai.grakn.GraknConfigKey;
import ai.grakn.GraknSystemProperty;
import ai.grakn.engine.GraknConfig;
import ai.grakn.util.ErrorMessage;
import ai.grakn.util.REST;
import ai.grakn.util.SimpleURI;

import javax.ws.rs.core.UriBuilder;
import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.net.HttpURLConnection;
import java.net.URL;
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
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static ai.grakn.engine.bootup.BootupProcessExecutor.WAIT_INTERVAL_SECOND;

/**
 * A class responsible for managing the Engine process,
 * including starting, stopping, and performing status checks
 *
 * @author Ganeshwara Herawan Hananda
 * @author Michele Orsi
 */
public class EngineBootup {
    private static final String DISPLAY_NAME = "Engine";
    private static final long ENGINE_STARTUP_TIMEOUT_S = 300;
    private static final Path ENGINE_PIDFILE = Paths.get(System.getProperty("java.io.tmpdir"), "grakn-engine.pid");
    private static final String JAVA_OPTS = GraknSystemProperty.ENGINE_JAVAOPTS.value();

    protected final Path graknHome;
    protected final Path graknPropertiesPath;
    private final GraknConfig graknProperties;

    private BootupProcessExecutor bootupProcessExecutor;

    public EngineBootup(BootupProcessExecutor bootupProcessExecutor, Path graknHome, Path graknPropertiesPath) {
        this.bootupProcessExecutor = bootupProcessExecutor;
        this.graknHome = graknHome;
        this.graknPropertiesPath = graknPropertiesPath;
        this.graknProperties = GraknConfig.read(graknPropertiesPath.toFile());
    }

    /**
     * @return the main class of Engine. In KGMS, this method will be overridden to return a different class.
     */
    public Class getEngineMainClass() {
        return Grakn.class;
    }

    public void startIfNotRunning() {
        boolean isEngineRunning = bootupProcessExecutor.isProcessRunning(ENGINE_PIDFILE);
        if (isEngineRunning) {
            System.out.println(DISPLAY_NAME + " is already running");
        } else {
            start();
        }
    }

    public void stop() {
        bootupProcessExecutor.stopProcessIfRunning(ENGINE_PIDFILE, DISPLAY_NAME);
    }

    public void status() {
        bootupProcessExecutor.processStatus(ENGINE_PIDFILE, DISPLAY_NAME);
    }

    public void statusVerbose() {
        System.out.println(DISPLAY_NAME + " pid = '" + bootupProcessExecutor.getPidFromFile(ENGINE_PIDFILE).orElse("") + "' (from " + ENGINE_PIDFILE + "), '" + bootupProcessExecutor.getPidFromPsOf(getEngineMainClass().getName()) + "' (from ps -ef)");
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
        return bootupProcessExecutor.isProcessRunning(ENGINE_PIDFILE);
    }

    private void start() {
        System.out.print("Starting " + DISPLAY_NAME + "...");
        System.out.flush();

        Future<BootupProcessResult> startEngineAsync = bootupProcessExecutor.executeAsync(engineCommand(), graknHome.toFile());

        LocalDateTime timeout = LocalDateTime.now().plusSeconds(ENGINE_STARTUP_TIMEOUT_S);

        while (LocalDateTime.now().isBefore(timeout) && !startEngineAsync.isDone()) {
            System.out.print(".");
            System.out.flush();

            String host = graknProperties.getProperty(GraknConfigKey.SERVER_HOST_NAME);
            int port = graknProperties.getProperty(GraknConfigKey.SERVER_PORT);

            if (bootupProcessExecutor.isProcessRunning(ENGINE_PIDFILE) && isEngineReady(host, port, REST.WebPath.STATUS)) {
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
            String errorMessage = "Process exited with code '" + startEngineAsync.get().exitCode() + "': '" + startEngineAsync.get().stderr() + "'";
            System.err.println(errorMessage);
            throw new BootupException(errorMessage);
        } catch (InterruptedException | ExecutionException e) {
            throw new BootupException(e);
        }

    }

    private List<String> engineCommand() {
        //   java -cp <classpath> -Dgrakn.dir=<path-to-grakn-home>
        //    -Dgrakn.conf=<path-to-grakn-properties -Dgrakn.pidFile=<path-to-engine-pidfile> <java-opts> <engine-main-class>'
        String classpath = graknHome.resolve("services").resolve("lib").toString() + File.separator + "*";
        ArrayList<String> engineCommand = new ArrayList<>();
        engineCommand.add("java");
        engineCommand.add("-cp");
        engineCommand.add(classpath);
        engineCommand.add("-Dgrakn.dir=" + graknHome);
        engineCommand.add("-Dgrakn.conf=" + graknPropertiesPath);
        engineCommand.add("-Dgrakn.pidfile=" + ENGINE_PIDFILE);
        if (JAVA_OPTS != null) { engineCommand.addAll(Arrays.asList(JAVA_OPTS.split(" ")));} //split JAVA OPTS by space and add them to the command
        engineCommand.add(getEngineMainClass().getName());
        return engineCommand;
    }

    private boolean isEngineReady(String host, int port, String path) {
        try {
            URL engineUrl = UriBuilder.fromUri(new SimpleURI(host, port).toURI()).path(path).build().toURL();
            HttpURLConnection connection = (HttpURLConnection) engineUrl.openConnection();
            connection.setRequestMethod("GET");
            connection.connect();

            int code = connection.getResponseCode();
            return code == 200;
        } catch (IOException e) {
            return false;
        }
    }

    /**
     * Build the classpath from the following folders:
     * - services/lib/*.jar
     * - conf/
     * - services/grakn/server/
     * Any slf4J-log4j12 Jars are excluded.
     *
     * @return a classpath to be supplied to Java, ie., java -cp <classpath>
     */
    private String getEngineJavaClassPath() {
        FilenameFilter filterForJarFiles = (dir, name) -> name.toLowerCase().endsWith(".jar");
        File servicesLibDir = Paths.get("services", "lib").toFile();
        File[] jarFiles = servicesLibDir.listFiles(filterForJarFiles);
        if (jarFiles == null) {
            throw new RuntimeException(ErrorMessage.UNABLE_TO_START_ENGINE_JAR_NOT_FOUND.getMessage());
        }
        Stream<File> jars = Stream.of(jarFiles);
        File conf = Paths.get("./conf").toFile(); // $GRAKN_HOME/conf
        File graknLogback = Paths.get("services", "grakn", "server").toFile(); // $GRAKN_HOME/services/grakn/server lib
        String classPath = ":" + Stream.concat(jars, Stream.of(conf, graknLogback))
                .filter(f -> !f.getName().contains("slf4j-log4j12"))
                .map(f -> f.toPath().toString())
                .sorted() // we need to sort otherwise it doesn't load logback configuration properly
                .collect(Collectors.joining(":"));
        return classPath;
    }
}
