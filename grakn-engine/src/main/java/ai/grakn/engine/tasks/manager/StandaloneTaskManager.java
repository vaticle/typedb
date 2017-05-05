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

package ai.grakn.engine.tasks.manager;

import ai.grakn.engine.GraknEngineConfig;
import ai.grakn.engine.TaskId;
import ai.grakn.engine.TaskStatus;
import ai.grakn.engine.lock.LockProvider;
import ai.grakn.engine.lock.NonReentrantLock;
import ai.grakn.engine.postprocessing.PostProcessingTask;
import ai.grakn.engine.postprocessing.UpdatingInstanceCountTask;
import ai.grakn.engine.tasks.BackgroundTask;
import ai.grakn.engine.tasks.TaskCheckpoint;
import ai.grakn.engine.tasks.TaskConfiguration;
import ai.grakn.engine.tasks.TaskManager;
import ai.grakn.engine.tasks.TaskSchedule;
import ai.grakn.engine.tasks.TaskState;
import ai.grakn.engine.tasks.TaskStateStorage;
import ai.grakn.engine.tasks.storage.TaskStateInMemoryStore;
import ai.grakn.engine.util.EngineID;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Duration;
import java.time.Instant;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.locks.Lock;
import java.util.function.Consumer;

/**
 * <p>
 * In-memory task manager to schedule and execute tasks. By default this task manager uses an in-memory
 * state storage.
 * </p>
 *
 * <p>
 * If engine fails while using this task manager, there will be no possibility for task recovery.
 * </p>
 *
 * @author Denis Lobanov, alexandraorth
 */
public class StandaloneTaskManager implements TaskManager {
    private final Logger LOG = LoggerFactory.getLogger(StandaloneTaskManager.class);

    private final Map<TaskId, ScheduledFuture> scheduledTasks;
    private final Map<TaskId, BackgroundTask> runningTasks;

    private final TaskStateStorage storage;
    private final Lock stateUpdateLock;

    private final ExecutorService executorService;
    private final ScheduledExecutorService schedulingService;
    private final EngineID engineID;

    public StandaloneTaskManager(EngineID engineId) {
        this.engineID = engineId;

        runningTasks = new ConcurrentHashMap<>();
        scheduledTasks = new ConcurrentHashMap<>();

        storage = new TaskStateInMemoryStore();
        stateUpdateLock = new NonReentrantLock();

        GraknEngineConfig properties = GraknEngineConfig.getInstance();
        schedulingService = Executors.newScheduledThreadPool(1);
        executorService = Executors.newFixedThreadPool(properties.getAvailableThreads());

        Lock postProcessingLock = new NonReentrantLock();
        Lock countUpdateLock = new NonReentrantLock();
        LockProvider.add(PostProcessingTask.LOCK_KEY, () -> postProcessingLock);
        LockProvider.add(UpdatingInstanceCountTask.LOCK_KEY, () -> countUpdateLock);
    }

    @Override
    public void close(){
        executorService.shutdown();
        schedulingService.shutdownNow();
        scheduledTasks.clear();
        runningTasks.clear();
        LockProvider.clear();
    }

    @Override
    public void addLowPriorityTask(TaskState taskState, TaskConfiguration configuration){
        addTask(taskState, configuration);
    }

    //TODO IMPLEMENT HIGH AND LOW PRIORITY IN STANDALONE MODE
    @Override
    public void addHighPriorityTask(TaskState taskState, TaskConfiguration configuration){
        LOG.info("Standalone mode only has a single priority.");
        addTask(taskState, configuration);
    }

    public void stopTask(TaskId id) {
        TaskState state = storage.getState(id);

        try {

            // Task has not been run- Mark the task as stopped and it will not run when picked up by the executor
            if (taskShouldRun(state)) {
                LOG.info("Stopping a currently scheduled task {}", id);

                state.markStopped();
            }

            // Kill the currently running task if it is running
            else if (state.status() == TaskStatus.RUNNING && runningTasks.containsKey(id)) {
                LOG.info("Stopping running task {}", id);

                // Stop the task
                runningTasks.get(id).stop();

                state.markStopped();
            }

            // Nothing was stopped, warn the user
            else {
                LOG.warn("Task not running {}, was not stopped", id);
            }
        } finally {
            saveState(state);
            cancelTask(state);
        }
    }

    public TaskStateStorage storage() {
        return storage;
    }

    private void addTask(TaskState taskState, TaskConfiguration taskConfiguration){
        storage.newState(taskState);

        // Schedule task to run.
        Instant now = Instant.now();
        TaskSchedule schedule = taskState.schedule();
        long delay = Duration.between(now, taskState.schedule().runAt()).toMillis();

        Runnable taskExecution = submitTaskForExecution(taskState, taskConfiguration);

        ScheduledFuture future;
        if(schedule.isRecurring()){
            future = schedulingService.scheduleAtFixedRate(taskExecution, delay, schedule.interval().get().toMillis(), TimeUnit.MILLISECONDS);
        } else {
            future = schedulingService.schedule(taskExecution, delay, TimeUnit.MILLISECONDS);
        }

        scheduledTasks.put(taskState.getId(), future);
    }

    private Runnable executeTask(TaskState task, TaskConfiguration configuration) {
        return () -> {
            try {
                BackgroundTask runningTask = task.taskClass().newInstance();
                runningTasks.put(task.getId(), runningTask);

                boolean completed;

                if(taskShouldResume(task)){
                    completed = runningTask.resume(saveCheckpoint(task), task.checkpoint());
                } else {
                    //Mark as running
                    task.markRunning(engineID);

                    saveState(task);

                    completed = runningTask.start(saveCheckpoint(task), configuration);
                }

                if (completed) {
                    task.markCompleted();
                } else {
                    task.markStopped();
                }
            } catch (Throwable throwable) {
                LOG.error(throwable.getMessage());
                task.markFailed(throwable);
            } finally {
                saveState(task);
                runningTasks.remove(task.getId());

                cancelTask(task);
            }
        };
    }

    private Runnable submitTaskForExecution(TaskState taskState, TaskConfiguration configuration) {
        return () -> {
            TaskState stateFromStorage = storage.getState(taskState.getId());
            if (taskShouldRun(stateFromStorage) || taskShouldResume(taskState)) {
                executorService.submit(executeTask(taskState, configuration));
            }
        };
    }

    /**
     * Determine if the task should be run. Tasks should run from the beginning
     * when they are CREATED or recurring and COMPLETED
     * @param task Task that should be checked
     * @return If the given task can run
     */
    private boolean taskShouldRun(TaskState task){
        return task.status() == TaskStatus.CREATED || task.schedule().isRecurring() && task.status() == TaskStatus.COMPLETED;
    }

    /**
     * Tasks should resume from the last checkpoint when they are in the RUNNING state.
     * This status should be taken from the latest snapshot of task state in storage.
     *
     * Recurring tasks should
     * @param task Task that should be checked
     * @return If the given task can resume
     */
    private boolean taskShouldResume(TaskState task){
        return task.status() == TaskStatus.RUNNING;
    }

    private Consumer<TaskCheckpoint> saveCheckpoint(TaskState state) {
        return checkpoint -> saveState(state.checkpoint(checkpoint));
    }

    private void cancelTask(TaskState task){
        // If stopped or failed, always cancel and clear the task
        if(task.status() == TaskStatus.STOPPED || task.status() == TaskStatus.FAILED){
            scheduledTasks.get(task.getId()).cancel(true);
            scheduledTasks.remove(task.getId());
        }

        // Only clear COMPLETED tasks if they are not recurring
        if(task.status() == TaskStatus.COMPLETED && !task.schedule().isRecurring()){
            scheduledTasks.remove(task.getId());
        }
    }

    private void saveState(TaskState taskState){
        stateUpdateLock.lock();
        try {
            storage.updateState(taskState);
        } finally {
            stateUpdateLock.unlock();
        }
    }
}
