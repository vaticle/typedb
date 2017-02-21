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

package ai.grakn.engine.tasks.manager.singlequeue;

import ai.grakn.engine.TaskStatus;
import ai.grakn.engine.tasks.BackgroundTask;
import ai.grakn.engine.tasks.TaskState;
import ai.grakn.engine.tasks.TaskStateStorage;
import org.apache.kafka.clients.consumer.Consumer;
import org.apache.kafka.clients.consumer.ConsumerRecord;
import org.apache.kafka.common.TopicPartition;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.atomic.AtomicBoolean;

import static ai.grakn.engine.TaskStatus.COMPLETED;
import static ai.grakn.engine.TaskStatus.CREATED;
import static ai.grakn.engine.TaskStatus.FAILED;

/**
 * The {@link SingleQueueTaskRunner} is used by the {@link SingleQueueTaskManager} to execute tasks from a Kafka queue.
 *
 * @author aelred, alexandrorth
 */
public class SingleQueueTaskRunner implements Runnable, AutoCloseable {

    private final static Logger LOG = LoggerFactory.getLogger(SingleQueueTaskRunner.class);

    private final Consumer<String, String> consumer;
    private final TaskStateStorage storage;

    private final AtomicBoolean wakeUp = new AtomicBoolean(false);
    private final CountDownLatch countDownLatch = new CountDownLatch(1);
    private final ExecutorService executor;
    private final Set<String> currentlyRunningTasks = ConcurrentHashMap.newKeySet();

    /**
     * Create a {@link SingleQueueTaskRunner} which retrieves tasks from the given {@param consumer} and uses the given
     * {@param storage} to store and retrieve information about tasks.
     *
     * @param storage a place to store and retrieve information about tasks.
     * @param consumer a Kafka consumer from which to poll for tasks
     */
    public SingleQueueTaskRunner(
            TaskStateStorage storage, Consumer<String, String> consumer, ExecutorService executor) {
        this.storage = storage;
        this.consumer = consumer;
        this.executor = executor;
    }

    /**
     * Poll Kafka for any new tasks. Will not return until {@link SingleQueueTaskRunner#close()} is called.
     * After receiving tasks, accept as many as possible, up to the maximum allowed number of tasks (TODO).
     * For each task, follow the workflow based on its type:
     *  - If not created or not in storage:
     *    - Record that this engine is running this task
     *      Record that this task is running
     *    - Send to thread pool for execution:
     *       - Use reflection to retrieve task
     *       - Start from checkpoint if necessary, or from beginning (TODO)
     *       - Record that this engine is no longer running this task
     *         Mark as completed or failed
     *  - Acknowledge message in queue
     */
    @Override
    public void run() {
        LOG.debug("started");

        try {
            while (!wakeUp.get()) {
                consumer.poll(100).forEach(this::handleRecord);
            }
        } finally {
            countDownLatch.countDown();
            LOG.debug("stopped");
        }
    }

    /**
     * Close connection to Kafka and thread pool.
     *
     * Inform {@link SingleQueueTaskRunner#run()} method to stop and block until it returns.
     */
    @Override
    public void close() throws Exception {
        wakeUp.set(true);
        countDownLatch.await();
    }

    private void handleRecord(ConsumerRecord<String, String> record) {
        TaskState task = TaskState.deserialize(record.value());

        LOG.debug("{}\thandling", task);

        if (shouldExecuteTask(task)) {
            task.status(TaskStatus.RUNNING);

            LOG.debug("{}\tmarked as running", task);

            storage.updateState(task);
            currentlyRunningTasks.add(task.getId());

            LOG.debug("{}\trecorded", task);

            executor.submit(() -> executeTask(task));
        }

        consumer.seek(new TopicPartition(record.topic(), record.partition()), record.offset() + 1);
        consumer.commitSync();

        LOG.debug("{}\tacknowledged", task);
    }

    private boolean shouldExecuteTask(TaskState task) {
        String taskId = task.getId();

        // Don't run tasks that are already running on this machine right now
        if (currentlyRunningTasks.contains(taskId)) return false;

        if (task.status().equals(CREATED)) {
            // Only run created tasks if they are not being retried
            return !storage.containsState(taskId);
        } else {
            // Only run retried tasks if they are not marked completed or failed
            TaskStatus status = storage.getState(taskId).status();
            return !status.equals(COMPLETED) && !status.equals(FAILED);
        }
    }

    private void executeTask(TaskState task) {
        BackgroundTask backgroundTask;
        try {
            backgroundTask = task.taskClass().newInstance();
        } catch (InstantiationException | IllegalAccessException e) {
            throw new RuntimeException(e);
        }

        try {
            backgroundTask.start(null, task.configuration());
            task.status(TaskStatus.COMPLETED);
            LOG.debug("{}\tmarked as completed", task);
        } catch (Exception e) {
            task.status(FAILED);
            LOG.debug("{}\tmarked as failed", task);
        }
        currentlyRunningTasks.remove(task.getId());
        storage.updateState(task);

        LOG.debug("{}\trecorded", task);
    }
}
