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
 *
 */

package ai.grakn.generator;

import ai.grakn.engine.TaskStatus;
import ai.grakn.engine.tasks.BackgroundTask;
import ai.grakn.engine.tasks.TaskId;
import ai.grakn.engine.tasks.TaskSchedule;
import ai.grakn.engine.tasks.TaskState;
import ai.grakn.test.engine.tasks.FailingTestTask;
import ai.grakn.test.engine.tasks.LongExecutionTestTask;
import ai.grakn.test.engine.tasks.ShortExecutionTestTask;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.generator.GeneratorConfiguration;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import mjson.Json;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static ai.grakn.engine.TaskStatus.CREATED;
import static java.lang.annotation.ElementType.ANNOTATION_TYPE;
import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.PARAMETER;
import static java.lang.annotation.ElementType.TYPE_USE;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

public class TaskStates extends Generator<TaskState> {

    private boolean newTask = false;

    public TaskStates() {
        super(TaskState.class);
    }

    @Override
    public TaskState generate(SourceOfRandomness random, GenerationStatus status) {
        // TODO: make this generate more classes
        Class<? extends BackgroundTask> taskClass = random.choose(ImmutableList.of(LongExecutionTestTask.class, ShortExecutionTestTask.class, FailingTestTask.class));

        TaskId taskId;
        TaskStatus taskStatus;

        if (newTask) {
            taskId = TaskId.generate();
            taskStatus = CREATED;
        } else {
            taskId = TaskId.of(random.choose(ImmutableSet.of("A", "B", "C")));
            taskStatus = gen().type(TaskStatus.class).generate(random, status);
        }

        String creator = gen().type(String.class).generate(random, status);

        // TODO: generate all the other params of a task state

        Json configuration = Json.object();
        TaskState taskState = TaskState.of(taskClass, creator, TaskSchedule.now(), configuration, taskId);
        configuration.set("id", taskState.getId().getValue());
        return taskState.status(taskStatus);
    }

    public void configure(NewTask newTask) {
        this.newTask = newTask.value();
    }

    @Target({PARAMETER, FIELD, ANNOTATION_TYPE, TYPE_USE})
    @Retention(RUNTIME)
    @GeneratorConfiguration
    public @interface NewTask {
        boolean value() default true;
    }
}
