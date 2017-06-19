/*
 * Grakn - A Distributed Semantic Database
 * Copyright (C) 2016  Grakn Labs Ltd
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

package ai.grakn.test.engine;

import ai.grakn.engine.GraknEngineServer;
import ai.grakn.engine.tasks.manager.StandaloneTaskManager;
import ai.grakn.engine.tasks.manager.singlequeue.SingleQueueTaskManager;
import ai.grakn.engine.GraknEngineConfig;
import ai.grakn.test.EngineContext;
import ai.grakn.test.GraknTestSetup;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import static ai.grakn.engine.GraknEngineConfig.TASK_MANAGER_IMPLEMENTATION;
import static ai.grakn.engine.GraknEngineConfig.ZK_CONNECTION_TIMEOUT;
import static junit.framework.TestCase.assertNotNull;
import static junit.framework.TestCase.assertTrue;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.IsInstanceOf.instanceOf;

public class GraknEngineServerTest {

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Rule
    public final EngineContext kafka = EngineContext.startKafkaServer();

    @Test
    public void whenEnginePropertiesIndicatesStandaloneTM_StandaloneTmIsStarted() {
        // Should start engine with in-memory server
        GraknEngineConfig conf = GraknEngineConfig.create();
        conf.setConfigProperty(TASK_MANAGER_IMPLEMENTATION, StandaloneTaskManager.class.getName());

        // Start Engine
        try (GraknEngineServer server = GraknEngineServer.start(conf)) {
            assertTrue(server.getTaskManager() instanceof StandaloneTaskManager);
        }
    }

    @Test
    public void whenEnginePropertiesIndicatesSingleQueueTM_SingleQueueTmIsStarted() {
        // Should start engine with distributed server, which means we will get a cannot
        // connect to Zookeeper exception (that has not been started)
        GraknEngineConfig conf = GraknEngineConfig.create();
        conf.setConfigProperty(ZK_CONNECTION_TIMEOUT, "1000");
        conf.setConfigProperty(TASK_MANAGER_IMPLEMENTATION, SingleQueueTaskManager.class.getName());

        // Start Engine
        try (GraknEngineServer server = GraknEngineServer.start(conf)) {
            assertThat(server.getTaskManager(), instanceOf(SingleQueueTaskManager.class));
        }
    }

    @Test
    public void whenEngineServerIsStarted_SystemKeyspaceIsLoaded(){
        GraknTestSetup.startCassandraIfNeeded();

        GraknEngineConfig conf = GraknEngineConfig.create();
        try (GraknEngineServer server = GraknEngineServer.start(conf)) {
            assertNotNull(server.systemKeyspace());

            // init a random keyspace
            String keyspaceName = "thisisarandomwhalekeyspace";
            server.systemKeyspace().ensureKeyspaceInitialised(keyspaceName);

            assertTrue(server.systemKeyspace().containsKeyspace(keyspaceName));
        }
    }
}
