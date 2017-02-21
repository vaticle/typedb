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
import ai.grakn.engine.tasks.TaskId;
import ai.grakn.engine.tasks.TaskState;
import ai.grakn.engine.tasks.TaskStateStorage;
import org.apache.kafka.clients.consumer.Consumer;
import org.apache.kafka.clients.consumer.ConsumerRecord;
import org.apache.kafka.clients.consumer.ConsumerRecords;
import org.apache.kafka.common.TopicPartition;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.atomic.AtomicBoolean;

import static ai.grakn.engine.TaskStatus.COMPLETED;
import static ai.grakn.engine.TaskStatus.CREATED;
import static ai.grakn.engine.TaskStatus.FAILED;
import static org.apache.commons.lang.exception.ExceptionUtils.getFullStackTrace;

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
    private final Set<TaskId> currentlyRunningTasks = ConcurrentHashMap.newKeySet();

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
     * After receiving tasks, accept as many as possible, up to the maximum allowed number of tasks.
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
                ConsumerRecords<String, String> records = consumer.poll(100);

                LOG.debug("polled, got {} records", records.count());

                for (ConsumerRecord<String, String> record : records) {
                    if (handleRecord(record)) {
                        consumer.seek(new TopicPartition(record.topic(), record.partition()), record.offset() + 1);
                        consumer.commitSync();

                        LOG.debug("acknowledged");
                    } else {
                        // When executor is full, don't consume any further records
                        break;
                    }
                }
            }
        } catch (Throwable throwable){
            //todo do we need to re-throw, figure out
            LOG.error(getFullStackTrace(throwable));
            throw new RuntimeException(throwable);
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

    /**
     * Returns false if cannot handle record because the executor is full
     * @param record
     * @return
     */
    private boolean handleRecord(ConsumerRecord<String, String> record) {
        TaskState task = TaskState.deserialize(record.value());

        LOG.debug("{}\thandling", task);

        boolean handled = true;

        if (shouldExecuteTask(task)) {
            task.status(TaskStatus.RUNNING);

            LOG.debug("{}\tmarked as running", task);

            if(storage.containsTask(task.getId())) {
                storage.updateState(task);
            } else {
                storage.newState(task);
            }

            currentlyRunningTasks.add(task.getId());

            LOG.debug("{}\trecorded", task);

            try {
                executor.submit(() -> executeTask(task));
            } catch (RejectedExecutionException e) {
                LOG.debug("{}\trejected by executor", task);
                handled = false;
                currentlyRunningTasks.remove(task.getId());
            }
        }

        return handled;
    }

    private boolean shouldExecuteTask(TaskState task) {
        TaskId taskId = task.getId();

        // Don't run tasks that are already running on this machine right now
        if (currentlyRunningTasks.contains(taskId)) return false;

        if (task.status().equals(CREATED)) {
            // Only run created tasks if they are not being retried
            return !storage.containsTask(taskId);
        } else {
            // Only run retried tasks if they are not marked completed or failed
            // TODO: what if another task runner is running this task? (due to rebalance)
            TaskStatus status = storage.getState(taskId).status();
            return !status.equals(COMPLETED) && !status.equals(FAILED);
        }
    }

    private void executeTask(TaskState task) {
        try {
            task.taskClass().newInstance().start(null, task.configuration());
            task.status(TaskStatus.COMPLETED);
            LOG.debug("{}\tmarked as completed", task);
        } catch (Exception e) {
            task.status(FAILED);
            LOG.debug("{}\tmarked as failed", task);
        } finally {
            currentlyRunningTasks.remove(task.getId());
            storage.updateState(task);
            LOG.debug("{}\trecorded", task);
        }
    }
}
