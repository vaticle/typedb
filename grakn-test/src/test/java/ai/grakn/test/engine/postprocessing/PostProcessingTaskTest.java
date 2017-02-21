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

package ai.grakn.test.engine.postprocessing;

import ai.grakn.engine.tasks.TaskState;
import ai.grakn.engine.tasks.manager.StandaloneTaskManager;
import ai.grakn.engine.postprocessing.PostProcessingTask;
import ai.grakn.test.EngineContext;
import org.junit.Assert;
import org.junit.ClassRule;
import org.junit.Test;

import java.time.Instant;
import java.time.temporal.ChronoUnit;
import java.util.Date;

import static ai.grakn.engine.TaskStatus.COMPLETED;
import static ai.grakn.engine.TaskStatus.CREATED;
import static ai.grakn.engine.TaskStatus.STOPPED;

public class PostProcessingTaskTest {
    private StandaloneTaskManager taskManager = new StandaloneTaskManager();

    @ClassRule
    public static final EngineContext engine = EngineContext.startDistributedServer();

    @Test
    public void testStart() throws Exception {
        TaskState task = new TaskState(PostProcessingTask.class);
        taskManager.addTask(task);
        Assert.assertNotEquals(CREATED, taskManager.storage().getState(task.getId()).status());

        // Wait for supervisor thread to mark task as completed
        final long initial = new Date().getTime();

        while ((new Date().getTime())-initial < 10000) {
            if (taskManager.storage().getState(task.getId()).status() == COMPLETED)
                break;

            Thread.sleep(100);
        }

        // Check that task has ran
        Assert.assertEquals(COMPLETED, taskManager.storage().getState(task.getId()).status());
    }

    @Test
    public void testStop() {
        TaskState task = new TaskState(PostProcessingTask.class).runAt(Instant.now().plus(10, ChronoUnit.SECONDS));
        taskManager.stopTask(task.getId(), this.getClass().getName());
        Assert.assertEquals(STOPPED, taskManager.storage().getState(task.getId()).status());
    }
}
