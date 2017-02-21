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

package ai.grakn.test.engine.tasks.storage;

import ai.grakn.engine.tasks.TaskStateStorage;
import ai.grakn.engine.tasks.TaskState;
import ai.grakn.engine.tasks.manager.ZookeeperConnection;
import ai.grakn.engine.tasks.storage.TaskStateZookeeperStore;
import ai.grakn.test.EngineContext;
import ai.grakn.test.engine.tasks.TestTask;
import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import org.junit.Before;
import org.junit.ClassRule;
import org.junit.Test;

import java.util.Set;
import java.util.UUID;
import java.util.stream.Collectors;

import static ai.grakn.engine.TaskStatus.CREATED;
import static ai.grakn.engine.TaskStatus.SCHEDULED;
import static ai.grakn.engine.tasks.config.ConfigHelper.client;
import static java.time.Instant.now;
import static junit.framework.TestCase.assertEquals;
import static org.hamcrest.Matchers.is;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertTrue;

public class TaskStateZookeeperStoreTest {
    private static ZookeeperConnection connection;
    private static TaskStateStorage stateStorage;

    @ClassRule
    public static final EngineContext engine = EngineContext.startKafkaServer();

    @Before
    public void setUp() throws Exception {
        connection = new ZookeeperConnection(client());
        stateStorage = new TaskStateZookeeperStore(connection);
    }

    @Test
    public void testStoreRetrieve() throws Exception {
        String id = stateStorage.newState(task());

        // Retrieve
        TaskState state = stateStorage.getState(id);
        assertNotNull(state);
        assertEquals(CREATED, state.status());
        assertEquals(TestTask.class, state.taskClass());
        assertEquals(this.getClass().getName(), state.creator());
    }

    @Test
    public void whenUpdatingTask_StateChanges() throws Exception {
        String id = stateStorage.newState(task());

        // Change
        String engineID = UUID.randomUUID().toString();
        String checkpoint = "test checkpoint";
        TaskState state = stateStorage.getState(id)
                .status(SCHEDULED)
                .engineID(engineID)
                .checkpoint(checkpoint);

        // Update
        stateStorage.updateState(state);

        // Retrieve the task and check properties correct
        state = stateStorage.getState(id);
        assertEquals(SCHEDULED, state.status());
        assertEquals(engineID, state.engineID());
        assertEquals(checkpoint, state.checkpoint());
    }

    @Test
    public void whenUpdatingTaskWithPreviousEngineAndNoNewEngine_ThereIsNoEnginePath() throws Exception {
        TaskState task = task();
        stateStorage.newState(task);

        // Update previous
        stateStorage.updateState(task.engineID("Engine1"));
        assertThat(pathExists("/engine/Engine1/" + task.getId()), is(true));

        // Check that getting engine-task path is not there
        stateStorage.updateState(task.engineID(null));
        assertThat(pathExists("/engine/Engine1/" + task.getId()), is(false));
    }

    @Test
    public void whenUpdatingTaskWithNoPreviousEngineAndNewEngine_ThereIsEnginePath() throws Exception {
        TaskState task = task();
        stateStorage.newState(task);

        // Set engine id to null
        stateStorage.updateState(task.engineID(null));
        assertThat(pathExists("/engine/Engine1/" + task.getId()), is(false));

        // Check that getting engine-task path is there
        stateStorage.updateState(task.engineID("Engine1"));
        assertThat(pathExists("/engine/Engine1/" + task.getId()), is(true));
    }

    @Test
    public void whenUpdatingTaskWithPreviousEngineAndNewEngine_ThereIsEnginePath() throws Exception {
        TaskState task = task();
        stateStorage.newState(task);

        stateStorage.updateState(task.engineID("Engine1"));
        assertThat(pathExists("/engine/Engine1/" + task.getId()), is(true));

        // Check that getting engine-task path is not there
        stateStorage.updateState(task.engineID("Engine2"));
        assertThat(pathExists("/engine/Engine1/" + task.getId()), is(false));
        assertThat(pathExists("/engine/Engine2/" + task.getId()), is(true));
    }

    @Test
    public void whenUpdatingTaskWithNoPreviousEngineAndNoNewEngine_ThereIsNoEnginePath() throws Exception {
        TaskState task = task();
        stateStorage.newState(task);

        stateStorage.updateState(task.engineID(null));
        assertThat(pathExists("/engine/Engine1/" + task.getId()), is(false));

        // Check that getting engine-task path is not there
        stateStorage.updateState(task.engineID(null));
        assertThat(pathExists("/engine/Engine2/" + task.getId()), is(false));
    }

    @Test
    public void testUpdateInvalid() throws Exception {
        String id = stateStorage.newState(task());

        // update
        String engineID = UUID.randomUUID().toString();
        String checkpoint = "test checkpoint";

        TaskState state = stateStorage.getState(id);
        stateStorage.updateState(state.engineID(engineID).checkpoint(checkpoint));

        // get again
        state = stateStorage.getState(id);
        assertEquals(CREATED, state.status());
        assertEquals(engineID, state.engineID());
        assertEquals(checkpoint, state.checkpoint());
    }


    @Test
    public void testGetTasksByStatus() {
        String id = stateStorage.newState(task());
        stateStorage.newState(task().status(SCHEDULED));
        Set<TaskState> res = stateStorage.getTasks(CREATED, null, null, 0, 0);

        assertTrue(res.parallelStream()
                .map(TaskState::getId)
                .filter(x -> x.equals(id))
                .collect(Collectors.toList())
                .size() == 1);
    }

    @Test
    public void testGetTasksByCreator() {
        String id = stateStorage.newState(task());
        stateStorage.newState(task().creator("another"));
        Set<TaskState> res = stateStorage.getTasks(null, null, this.getClass().getName(), 0, 0);

        assertTrue(res.parallelStream()
                .map(TaskState::getId)
                .filter(x -> x.equals(id))
                .collect(Collectors.toList())
                .size() == 1);
    }

    @Test
    public void testGetTasksByClassName() {
        String id = stateStorage.newState(task());
        Set<TaskState> res = stateStorage.getTasks(null, TestTask.class.getName(), null, 0, 0);

        assertTrue(res.parallelStream()
                .map(TaskState::getId)
                .filter(x -> x.equals(id))
                .collect(Collectors.toList())
                .size() == 1);
    }

    @Test
    public void testGetAllTasks() {
        String id = stateStorage.newState(task());
        Set<TaskState> res = stateStorage.getTasks(null, null, null, 0, 0);

        assertTrue(res.parallelStream()
                .map(TaskState::getId)
                .filter(x -> x.equals(id))
                .collect(Collectors.toList())
                .size() == 1);
    }

    @Test
    public void testTaskPagination() {
        for (int i = 0; i < 20; i++) {
            stateStorage.newState(task());
        }

        Set<TaskState> setA = stateStorage.getTasks(null, null, null, 10, 0);
        Set<TaskState> setB = stateStorage.getTasks(null, null, null, 10, 10);

        setA.forEach(x -> assertFalse(setB.contains(x)));
    }

    public TaskState task(){
        return new TaskState(TestTask.class)
                .creator(this.getClass().getName())
                .statusChangedBy(this.getClass().getName())
                .runAt(now())
                .isRecurring(false)
                .interval(0)
                .configuration(null);
    }

    /**
     * Returns true when the given path exists in zookeeper
     */
    private boolean pathExists(String path) throws Exception {
        return connection.connection().checkExists().forPath(path) != null;
    }
}
