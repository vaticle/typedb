/*
 * Grakn - A Distributed Semantic Database
 * Copyright (C) 2016  Grakn Labs Limited
 *
 * Grakn is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Grakn is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Grakn. If not, see <http://www.gnu.org/licenses/gpl.txt>.
 */

package ai.grakn.test.rule;

import ai.grakn.GraknConfigKey;
import ai.grakn.GraknSystemProperty;
import ai.grakn.client.Client;
import ai.grakn.engine.Grakn;
import ai.grakn.engine.GraknConfig;
import ai.grakn.util.GraknVersion;
import ai.grakn.util.SimpleURI;
import com.google.common.collect.ImmutableList;
import net.lingala.zip4j.core.ZipFile;
import net.lingala.zip4j.exception.ZipException;
import org.apache.commons.io.IOUtils;
import org.junit.Assert;
import org.junit.rules.TestRule;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Stream;

import static java.lang.System.currentTimeMillis;
import static java.util.stream.Collectors.joining;

/**
 * Start a GraknEngineServer from the packaged distribution Zip.
 * The class is responsible for unzipping and starting the distribution.
 * The location of the distribution must be at $GRAKN_HOME/grakn-dist/target/grakn-dist-$GRAKN_VERSION.zip
 *
 * This context can be used for integration tests.
 *
 * @author alexandraorth
 */
public class DistributionContext extends CompositeTestRule {

    public static final Logger LOG = LoggerFactory.getLogger(DistributionContext.class);

    private static final FilenameFilter jarFiles = (dir, name) -> name.toLowerCase().endsWith(".jar");
    private static final String ZIP_FILENAME = "grakn-dist-" + GraknVersion.VERSION + ".zip";
    private static final Path GRAKN_BASE_DIRECTORY = Paths.get(GraknSystemProperty.PROJECT_RELATIVE_DIR.value());
    private static final Path TARGET_DIRECTORY = Paths.get(GRAKN_BASE_DIRECTORY.toString(), "grakn-dist", "target");
    private static final Path ZIP_FULLPATH = Paths.get(TARGET_DIRECTORY.toString(), ZIP_FILENAME);
    private static final Path EXTRACTED_DISTRIBUTION_DIRECTORY = Paths.get(TARGET_DIRECTORY.toString(), "grakn-dist-" + GraknVersion.VERSION);

    private Process engineProcess;
    private int port = 4567;
    private boolean inheritIO = true;
    private int redisPort = 6379;

    // prevent initialization with the default constructor
    private DistributionContext() {
    }

    public static DistributionContext create(){
        return new DistributionContext();
    }

    public DistributionContext inheritIO(boolean inheritIO) {
        this.inheritIO = inheritIO;
        return this;
    }

    public SimpleURI uri(){
        return new SimpleURI("localhost", port);
    }

    @Override
    protected List<TestRule> testRules() {
        return ImmutableList.of(
                SessionContext.create(),
                InMemoryRedisContext.create(redisPort)
        );
    }

    @Override
    public void before() throws Throwable {
        assertPackageBuilt();
        unzipDistribution();
        engineProcess = newEngineProcess(port, redisPort);
        waitForEngine();
    }

    @Override
    public void after() {
        engineProcess.destroy();
    }

    private void assertPackageBuilt() throws IOException {
        boolean packaged = Files.exists(ZIP_FULLPATH);

        if(!packaged) {
            Assert.fail("Grakn distribution '" + ZIP_FULLPATH.toString() + "' could not be found. Please ensure it has been packaged (ie. run `mvn package`) in order to build  before running tests with the distribution context.");
        }
    }

    private void unzipDistribution() throws ZipException, IOException {
        // Unzip the distribution
        ZipFile zipped = new ZipFile( ZIP_FULLPATH.toFile());
        zipped.extractAll(TARGET_DIRECTORY.toAbsolutePath().toString());
    }

    private Process newEngineProcess(Integer port, Integer redisPort) throws IOException {
        // Set correct port & task manager
        GraknConfig config = GraknConfig.create();
        config.setConfigProperty(GraknConfigKey.SERVER_PORT, port);
        config.setConfigProperty(GraknConfigKey.REDIS_HOST, ImmutableList.of(new SimpleURI("localhost", redisPort).toString()));
        // To speed up tests of failure cases
        config.setConfigProperty(GraknConfigKey.TASKS_RETRY_DELAY, 60);

        // Write new properties to disk
        File propertiesFile = new File("grakn-engine-" + port + ".properties");
        propertiesFile.deleteOnExit();
        config.write(propertiesFile);

        // Java commands to start Engine process
        String[] commands = {"java",
                "-cp", getClassPath(),
                "-Dgrakn.dir=" + EXTRACTED_DISTRIBUTION_DIRECTORY,
                "-Dgrakn.conf=" + propertiesFile.getAbsolutePath(),
                Grakn.class.getName(), "&"};

        // Start process
        ProcessBuilder processBuilder = new ProcessBuilder(commands);
        if (inheritIO) processBuilder.inheritIO();
        return processBuilder.start();
    }

    /**
     * Get the class path of all the jars in the /lib folder
     */
    private String getClassPath(){
        Path servicesLibDir = Paths.get(EXTRACTED_DISTRIBUTION_DIRECTORY.toString(), "services", "lib");
        Path confDir = Paths.get(EXTRACTED_DISTRIBUTION_DIRECTORY.toString(), "conf");
        Path graknLogback = Paths.get(EXTRACTED_DISTRIBUTION_DIRECTORY.toString(), "services", "grakn");

        Stream<File> jars = Stream.of(servicesLibDir.toFile().listFiles(jarFiles));
        return Stream.concat(jars, Stream.of(confDir.toFile(), graknLogback.toFile()))
                .filter(f -> !f.getName().contains("slf4j-log4j12"))
                .map(File::getAbsolutePath)
                .collect(joining(":"));
    }

    /**
     * Wait for the engine REST API to be available
     */
    private void waitForEngine() {
        long endTime = currentTimeMillis() + 120000;
        while (currentTimeMillis() < endTime) {
            if (Client.serverIsRunning(uri())) {
                return;
            }
            try {
                Thread.sleep(100);
            } catch (InterruptedException e) {
                LOG.error("Thread sleep interrupted. ", e);
            }
        }

        LOG.error("Engine stdout = '" + inputStreamToString(engineProcess.getInputStream()) + "'");
        LOG.error("Engine stderr = '" + inputStreamToString(engineProcess.getErrorStream()) + "'");
        throw new RuntimeException("Could not start engine within expected time");
    }

    private String inputStreamToString(InputStream output) {
        String engineStdout;
        try {
            engineStdout = IOUtils.toString(output, StandardCharsets.UTF_8);
        } catch (IOException e) {
            engineStdout = "Unable to get output from Engine: " + e.getMessage();
        }

        return engineStdout;
    }
}