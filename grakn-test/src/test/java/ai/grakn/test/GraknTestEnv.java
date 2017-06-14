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
package ai.grakn.test;

import ai.grakn.GraknGraph;
import ai.grakn.GraknTxType;
import ai.grakn.engine.GraknEngineConfig;
import ai.grakn.engine.GraknEngineServer;
import ai.grakn.engine.factory.EngineGraknGraphFactory;
import ai.grakn.engine.tasks.TaskState;
import ai.grakn.engine.util.JWTHandler;
import ai.grakn.factory.SystemKeyspace;
import ai.grakn.util.CassandraHelper;
import com.jayway.restassured.RestAssured;
import info.batey.kafka.unit.KafkaUnit;
import org.slf4j.LoggerFactory;
import spark.Service;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.HashSet;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.atomic.AtomicInteger;

import static ai.grakn.engine.GraknEngineConfig.JWT_SECRET_PROPERTY;
import static ai.grakn.engine.GraknEngineServer.configureSpark;
import static ai.grakn.graql.Graql.var;

/**
 * <p>
 * Contains utility methods and statically initialized environment variables to control
 * Grakn unit tests. 
 * </p>
 * 
 * @author borislav
 *
 */
public abstract class GraknTestEnv {

    private static final org.slf4j.Logger LOG = LoggerFactory.getLogger(GraknTestEnv.class);

    private static String CONFIG = System.getProperty("grakn.test-profile");
    private static AtomicInteger KAFKA_COUNTER = new AtomicInteger(0);

    private static KafkaUnit kafkaUnit = new KafkaUnit(2181, 9092);

    public static void ensureCassandraRunning() throws Exception {
        if (usingTitan()) {
            CassandraHelper.startEmbedded();
        }
    }

    /**
     * Create a configuration for use in tests, using random ports.
     */
    static GraknEngineConfig createTestConfig() {
        GraknEngineConfig config = GraknEngineConfig.create();

        Integer serverPort = getEphemeralPort();

        config.setConfigProperty(GraknEngineConfig.SERVER_PORT_NUMBER, String.valueOf(serverPort));

        return config;
    }

    /**
     * To run engine we must ensure Cassandra, the Grakn HTTP endpoint, Kafka & Zookeeper are running
     */
    static GraknEngineServer startEngine(GraknEngineConfig config) throws Exception {
        // To ensure consistency b/w test profiles and configuration files, when not using Titan
        // for a unit tests in an IDE, add the following option:
        // -Dgrakn.conf=../conf/test/tinker/grakn.properties
        //
        // When using titan, add -Dgrakn.test-profile=titan
        //
        // The reason is that the default configuration of Grakn uses the Titan factory while the default
        // test profile is tinker: so when running a unit test within an IDE without any extra parameters,
        // we end up wanting to use the TitanFactory but without starting Cassandra first.
        LOG.info("starting engine...");

        ensureCassandraRunning();

        // start engine
        setRestAssuredUri(config);
        GraknEngineServer server = GraknEngineServer.start(config);

        LOG.info("engine started.");

        return server;
    }

    static void startKafka(GraknEngineConfig config) throws Exception {
        // Clean-up ironically uses a lot of memory
        if (KAFKA_COUNTER.getAndIncrement() == 0) {
            LOG.info("Starting kafka...");
            kafkaUnit.setKafkaBrokerConfig("log.cleaner.enable", "false");
            kafkaUnit.startup();
            kafkaUnit.createTopic(TaskState.Priority.HIGH.queue(), config.getAvailableThreads() * 2);
            kafkaUnit.createTopic(TaskState.Priority.LOW.queue(), config.getAvailableThreads() * 2);
            LOG.info("Kafka started.");
        }
    }

    static void stopKafka() throws Exception {
        if (KAFKA_COUNTER.decrementAndGet() == 0) {
            LOG.info("Stopping kafka...");
            kafkaUnit.shutdown();
            LOG.info("Kafka stopped.");
        }
    }

    static void stopEngine(GraknEngineServer server) throws Exception {
        LOG.info("stopping engine...");

        server.close();
        clearGraphs(server.factory());

        LOG.info("engine stopped.");

        // There is no way to stop the embedded Casssandra, no such API offered.
    }

    static Service startSpark(GraknEngineConfig config) {
        LOG.info("starting spark on port " + config.uri());

        Service spark = Service.ignite();
        configureSpark(spark, config, JWTHandler.create(config.getProperty(JWT_SECRET_PROPERTY)));
        setRestAssuredUri(config);
        return spark;
    }

    public static GraknGraph emptyGraph(EngineGraknGraphFactory factory) {
        return factory.getGraph(randomKeyspace(), GraknTxType.WRITE);
    }

    private static void clearGraphs(EngineGraknGraphFactory engineGraknGraphFactory) {
        // Drop all keyspaces
        final Set<String> keyspaceNames = new HashSet<String>();
        try(GraknGraph systemGraph = engineGraknGraphFactory.getGraph(SystemKeyspace.SYSTEM_GRAPH_NAME, GraknTxType.WRITE)) {
            systemGraph.graql().match(var("x").isa("keyspace-name"))
                    .execute()
                    .forEach(x -> x.values().forEach(y -> {
                        keyspaceNames.add(y.asResource().getValue().toString());
                    }));
        }
        keyspaceNames.forEach(name -> {
            GraknGraph graph = engineGraknGraphFactory.getGraph(name, GraknTxType.WRITE);
            graph.admin().delete();            
        });
        engineGraknGraphFactory.refreshConnections();
    }

    static String getUri(GraknEngineConfig config) {
        return config.getProperty("server.host") + ":" + config.getProperty("server.port");
    }

    static String getHost(GraknEngineConfig config) {
        return config.getProperty("server.host");
    }

    static String getPort(GraknEngineConfig config) {
        return config.getProperty("server.port");
    }

    static void setRestAssuredUri(GraknEngineConfig config) {
        RestAssured.baseURI = "http://" + config.uri();
    }

    public static String randomKeyspace(){
        // Embedded Casandra has problems dropping keyspaces that start with a number
        return "a"+ UUID.randomUUID().toString().replaceAll("-", "");
    }

    public static boolean usingTinker() {
        return "tinker".equals(CONFIG);
    }

    public static boolean usingTitan() {
        return "titan".equals(CONFIG);
    }

    public static boolean usingOrientDB() {
        return "orientdb".equals(CONFIG);
    }

    private static int getEphemeralPort() {
        try (ServerSocket socket = new ServerSocket(0)) {
            return socket.getLocalPort();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
