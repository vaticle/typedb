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

import ai.grakn.Grakn;
import ai.grakn.GraknConfigKey;
import ai.grakn.GraknSession;
import ai.grakn.engine.GraknEngineConfig;
import ai.grakn.engine.GraknEngineServer;
import ai.grakn.engine.postprocessing.RedisCountStorage;
import ai.grakn.engine.tasks.manager.TaskManager;
import ai.grakn.engine.tasks.mock.MockBackgroundTask;
import ai.grakn.util.EmbeddedRedis;
import ai.grakn.util.MockRedisRule;
import ai.grakn.util.SimpleURI;
import com.codahale.metrics.MetricRegistry;
import com.google.common.collect.Iterables;
import com.jayway.restassured.RestAssured;
import org.junit.rules.TestRule;
import org.junit.runner.Description;
import org.junit.runners.model.Statement;
import redis.clients.jedis.JedisPool;
import redis.clients.jedis.JedisPoolConfig;

import static ai.grakn.engine.util.ExceptionWrapper.noThrow;
import static ai.grakn.test.GraknTestEngineSetup.startEngine;
import static ai.grakn.test.GraknTestEngineSetup.stopEngine;
import static ai.grakn.util.SampleKBLoader.randomKeyspace;


/**
 * <p>
 * Start the Grakn Engine server before each test class and stop after.
 * </p>
 *
 * @author alexandraorth
 */
public class EngineContext implements TestRule {

    private GraknEngineServer server;

    private final GraknEngineConfig config = GraknTestEngineSetup.createTestConfig();
    private JedisPool jedisPool;
    private MetricRegistry metricRegistry;

    private final TestRule redis;

    private EngineContext(boolean inMemoryRedis){
        SimpleURI redisURI = new SimpleURI(Iterables.getOnlyElement(config.getProperty(GraknConfigKey.REDIS_HOST)));
        int redisPort = redisURI.getPort();

        if (inMemoryRedis) {
            redis = MockRedisRule.create(redisPort);
        } else {
            redis = EmbeddedRedis.create(redisPort);
        }
    }

    /**
     * Creates a {@link EngineContext} for testing which uses a real embedded redis.
     * This should only be used for benchmark testing where performance and memory usage matters.
     *
     * @return a new {@link EngineContext} for testing
     */
    public static EngineContext createWithEmbeddedRedis(){
        return new EngineContext(false);
    }

    /**
     * Creates a {@link EngineContext} for testing which uses an in-memory redis mock.
     * This is the default test environment which should be used because starting an embedded redis is a costly process.
     *
     * @return a new {@link EngineContext} for testing
     */
    public static EngineContext createWithInMemoryRedis(){
        return new EngineContext(true);
    }

    public int port() {
        return config.getProperty(GraknConfigKey.SERVER_PORT);
    }

    public GraknEngineServer server() {
        return server;
    }

    public GraknEngineConfig config() {
        return config;
    }

    public RedisCountStorage redis() {
        return redis(Iterables.getOnlyElement(config.getProperty(GraknConfigKey.REDIS_HOST)));
    }

    public RedisCountStorage redis(String uri) {
        SimpleURI simpleURI = new SimpleURI(uri);
        return redis(simpleURI.getHost(), simpleURI.getPort());
    }

    public RedisCountStorage redis(String host, int port) {
        JedisPoolConfig poolConfig = new JedisPoolConfig();
        this.jedisPool = new JedisPool(poolConfig, host, port);
        this.metricRegistry = new MetricRegistry();
        return RedisCountStorage.create(jedisPool, metricRegistry);
    }

    public TaskManager getTaskManager(){
        return server.getTaskManager();
    }

    public String uri() {
        return config.uri();
    }

    public GraknSession sessionWithNewKeyspace() {
        return Grakn.session(uri(), randomKeyspace());
    }

    @Override
    public Statement apply(Statement base, Description description) {
        Statement statement = new Statement() {
            @Override
            public void evaluate() throws Throwable {
                before();
                try {
                    base.evaluate();
                } finally {
                    after();
                }
            }
        };

        // Start redis
        return redis.apply(statement, description);
    }

    public void before() throws Throwable {
        RestAssured.baseURI = "http://" + config.uri();
        if (!config.getProperty(GraknConfigKey.TEST_START_EMBEDDED_COMPONENTS)) {
            return;
        }

        SimpleURI redisURI = new SimpleURI(Iterables.getOnlyElement(config.getProperty(GraknConfigKey.REDIS_HOST)));

        jedisPool = new JedisPool(redisURI.getHost(), redisURI.getPort());

        server = startEngine(config);
    }

    public void after() {
        if (!config.getProperty(GraknConfigKey.TEST_START_EMBEDDED_COMPONENTS)) {
            return;
        }
        noThrow(MockBackgroundTask::clearTasks, "Error clearing tasks");

        try {
            noThrow(() -> stopEngine(server), "Error closing engine");
            getJedisPool().close();
        } catch (Exception e){
            throw new RuntimeException("Could not shut down ", e);
        }
    }

    public JedisPool getJedisPool() {
        return jedisPool;
    }

    public MetricRegistry getMetricRegistry() {
        return metricRegistry;
    }
}
