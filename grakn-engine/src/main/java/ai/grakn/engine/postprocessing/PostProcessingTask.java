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

package ai.grakn.engine.postprocessing;

import ai.grakn.GraknGraph;
import ai.grakn.concept.ConceptId;
import ai.grakn.engine.GraknEngineConfig;
import ai.grakn.engine.tasks.TaskCheckpoint;
import ai.grakn.engine.tasks.TaskConfiguration;
import ai.grakn.util.Schema;
import java.util.Optional;
import mjson.Json;
import org.apache.tinkerpop.gremlin.util.function.TriFunction;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Duration;
import java.time.Instant;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;

import static ai.grakn.engine.GraknEngineConfig.POST_PROCESSING_DELAY;
import static ai.grakn.util.REST.Request.COMMIT_LOG_FIXING;
import static java.time.Instant.now;
import static java.util.stream.Collectors.toSet;

/**
 * <p>
 *     Task that control when postprocessing starts.
 * </p>
 *
 * <p>
 *     This task begins only if enough time has passed (configurable) since the last time a job was added.
 * </p>
 *
 * @author Denis Lobanov, alexandraorth
 */
public class PostProcessingTask extends AbstractGraphMutationTask {
    public static final String LOCK_KEY = "post-processing-lock";

    private static final Logger LOG = LoggerFactory.getLogger(PostProcessingTask.class);

    private long maxTimeLapse = GraknEngineConfig.getInstance().getPropertyAsLong(POST_PROCESSING_DELAY);

    //TODO MAJOR Make this distributed in distributed environment
    public static final AtomicLong lastPPTaskCreated = new AtomicLong(System.currentTimeMillis());

    /**
     * Run postprocessing only if enough time has passed since the last job was added
     */
    @Override
    public boolean start(Consumer<TaskCheckpoint> saveCheckpoint, TaskConfiguration configuration) {
        Instant lastJobAdded = Instant.ofEpochMilli(lastPPTaskCreated.get());
        long timeElapsed = Duration.between(lastJobAdded, now()).toMillis();

        LOG.trace("Checking post processing should run: " + (timeElapsed >= maxTimeLapse));

        // Only try to run if enough time has passed
        if(timeElapsed >= maxTimeLapse){
            return super.start(saveCheckpoint, configuration);
        }

        return true;
    }

    @Override
    public boolean runGraphMutatingTask(GraknGraph graph, Consumer<TaskCheckpoint> saveCheckpoint, TaskConfiguration configuration) {
        applyPPToMapEntry(graph, configuration, Schema.BaseType.CASTING.name(), PostProcessingTask::runCastingFix);
        applyPPToMapEntry(graph, configuration, Schema.BaseType.RESOURCE.name(), PostProcessingTask::runResourceFix);

        graph.admin().commitNoLogs();

        return false;
    }


    /**
     * Main method which attempts to run all post processing jobs.
     *
     * @param postProcessingMethod The post processing job.
     *                      Either {@link ai.grakn.engine.postprocessing.PostProcessingTask#runResourceFix(GraknGraph, String, Set)} or
     *                      {@link ai.grakn.engine.postprocessing.PostProcessingTask#runCastingFix(GraknGraph, String, Set)}.
     *                      This then returns a function which will complete the job after going through validation

     */
    private void applyPPToMapEntry(GraknGraph graph, TaskConfiguration configuration, String type,
                                   TriFunction<GraknGraph, String, Set<ConceptId>, Boolean> postProcessingMethod){
        Json innerConfig = configuration.json().at(COMMIT_LOG_FIXING);

        Map<String, Json> conceptsByIndex = innerConfig.at(type).asJsonMap();
        for(Map.Entry<String, Json> castingIndex:conceptsByIndex.entrySet()){
            // Turn json
            Set<ConceptId> conceptIds = castingIndex.getValue().asList().stream().map(ConceptId::of).collect(toSet());

            if(postProcessingMethod.apply(graph, castingIndex.getKey(), conceptIds)) {
                validateMerged(graph, castingIndex.getKey(), conceptIds).
                        ifPresent(message -> {
                            throw new RuntimeException(message);
                        });
            }
        }
    }

    public void setTimeLapse(long time){
        this.maxTimeLapse = time;
    }

    /**
     * Checks that post processing was done successfully by doing two things:
     *  1. That there is only 1 valid conceptID left
     *  2. That the concept Index does not return null
     * @param graph A grakn graph to run the checks against.
     * @param conceptIndex The concept index which MUST return a valid concept
     * @param conceptIds The concpet ids which should only return 1 valid concept
     * @return An error if one of the above rules are not satisfied.
     */
    private Optional<String> validateMerged(GraknGraph graph, String conceptIndex, Set<ConceptId> conceptIds){
        //Check number of valid concept Ids
        int numConceptFound = 0;
        for (ConceptId conceptId : conceptIds) {
            if (graph.getConcept(conceptId) != null) {
                numConceptFound++;
                if (numConceptFound > 1) {
                    StringBuilder conceptIdValues = new StringBuilder();
                    for (ConceptId id : conceptIds) {
                        conceptIdValues.append(id.getValue()).append(",");
                    }
                    return Optional.of("Not all concept were merged. The set of concepts [" + conceptIds.size() + "] with IDs [" + conceptIdValues.toString() + "] matched more than one concept");
                }
            }
        }

        //Check index
        if(graph.admin().getConcept(Schema.ConceptProperty.INDEX, conceptIndex) == null){
            return Optional.of("The concept index [" + conceptIndex + "] did not return any concept");
        }

        return Optional.empty();
    }

    /**
     * Run a a resource duplication merge on the provided concepts
     * @param graph Graph on which to apply the fixes
     * @param index The unique index of the concept which must exist at the end
     * @param conceptIds The conceptIds which effectively need to be merged.
     */
    private static boolean runResourceFix(GraknGraph graph, String index, Set<ConceptId> conceptIds) {
        return graph.admin().fixDuplicateResources(index, conceptIds);
    }


    /**
     * Run a casting duplication merge job on the provided concepts
     * @param graph Graph on which to apply the fixes
     * @param index The unique index of the concept which must exist at the end
     * @param conceptIds The conceptIds which effectively need to be merged.
     */
    private static boolean runCastingFix(GraknGraph graph, String index, Set<ConceptId> conceptIds) {
        return graph.admin().fixDuplicateCastings(index, conceptIds);
    }
}