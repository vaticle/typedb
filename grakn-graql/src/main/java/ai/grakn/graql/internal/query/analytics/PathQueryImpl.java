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

package ai.grakn.graql.internal.query.analytics;

import ai.grakn.GraknTx;
import ai.grakn.concept.Concept;
import ai.grakn.concept.ConceptId;
import ai.grakn.concept.Label;
import ai.grakn.concept.LabelId;
import ai.grakn.concept.Thing;
import ai.grakn.exception.GraqlQueryException;
import ai.grakn.graql.analytics.PathQuery;
import ai.grakn.graql.internal.analytics.NoResultException;
import ai.grakn.graql.internal.analytics.ShortestPathVertexProgram;
import org.apache.tinkerpop.gremlin.process.computer.ComputerResult;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static ai.grakn.graql.internal.analytics.Utility.getResourceEdgeId;
import static ai.grakn.graql.internal.util.StringConverter.idToString;

class PathQueryImpl extends AbstractComputeQuery<List<List<Concept>>> implements PathQuery {

    private ConceptId sourceId = null;
    private ConceptId destinationId = null;

    PathQueryImpl(Optional<GraknTx> graph) {
        this.tx = graph;
    }

    @Override
    public List<List<Concept>> execute() {
        LOGGER.info("ShortestPathVertexProgram is called");
        long startTime = System.currentTimeMillis();

        if (sourceId == null) throw GraqlQueryException.noPathSource();
        if (destinationId == null) throw GraqlQueryException.noPathDestination();
        initSubGraph();
        getAllSubTypes();

        if (!verticesExistInSubgraph(sourceId, destinationId)) {
            throw GraqlQueryException.instanceDoesNotExist();
        }
        if (sourceId.equals(destinationId)) {
            return Collections.singletonList(Collections.singletonList(tx.get().getConcept(sourceId)));
        }

        ComputerResult result;
        Set<LabelId> subLabelIds = convertLabelsToIds(subLabels);
        try {
            result = getGraphComputer().compute(
                    new ShortestPathVertexProgram(sourceId, destinationId), null, subLabelIds);
        } catch (NoResultException e) {
            LOGGER.info("ShortestPathVertexProgram is done in " + (System.currentTimeMillis() - startTime) + " ms");
            return Collections.emptyList();
        }

        Map<String, Set<String>> predecessorMapFromSource = getPredecessorMap(result);
        List<List<Concept>> allPaths = getAllPaths(predecessorMapFromSource);
        if (includeAttribute) { // this can be slow
            return getExtendedPaths(allPaths);
        }

        LOGGER.info("Number of paths: " + allPaths.size());
        LOGGER.info("ShortestPathVertexProgram is done in " + (System.currentTimeMillis() - startTime) + " ms");
        return allPaths;
    }

    // If the sub graph contains attributes, we may need to add implicit relations to the paths
    private List<List<Concept>> getExtendedPaths(List<List<Concept>> allPaths) {
        List<List<Concept>> extendedPaths = new ArrayList<>();
        for (List<Concept> currentPath : allPaths) {
            boolean hasAttribute = false;
            for (Concept concept : currentPath) {
                if (concept.isAttribute()) {
                    hasAttribute = true;
                    break;
                }
            }
            if (!hasAttribute) {
                extendedPaths.add(currentPath);
            }
        }

        // If there exist a path without attributes, we don't need to expand any path
        // as paths contain attributes would be longer after implicit relations are added
        int numExtensionAllowed = extendedPaths.isEmpty() ? Integer.MAX_VALUE : 0;
        for (List<Concept> currentPath : allPaths) {
            List<Concept> extendedPath = new ArrayList<>();
            int numExtension = 0;
            for (int j = 0; j < currentPath.size() - 1; j++) {
                extendedPath.add(currentPath.get(j));
                ConceptId resourceRelationId = getResourceEdgeId(tx.get(),
                        currentPath.get(j).getId(), currentPath.get(j + 1).getId());
                if (resourceRelationId != null) {
                    numExtension++;
                    if (numExtension > numExtensionAllowed) break;
                    extendedPath.add(getConcept(tx, resourceRelationId));
                }
            }
            if (numExtension == numExtensionAllowed) {
                extendedPath.add(currentPath.get(currentPath.size() - 1));
                extendedPaths.add(extendedPath);
            } else if (numExtension < numExtensionAllowed) {
                extendedPath.add(currentPath.get(currentPath.size() - 1));
                extendedPaths.clear();
                extendedPaths.add(extendedPath);
                numExtensionAllowed = numExtension;
            }
        }
        return extendedPaths;
    }

    private static Map<String, Set<String>> getPredecessorMap(ComputerResult result) {
        Map<String, Set<String>> predecessorMapFromSource =
                result.memory().get(ShortestPathVertexProgram.PREDECESSORS_FROM_SOURCE);
        Map<String, Set<String>> predecessorMapFromDestination =
                result.memory().get(ShortestPathVertexProgram.PREDECESSORS_FROM_DESTINATION);
        predecessorMapFromDestination.forEach((key, value) -> value.forEach(id -> {
            predecessorMapFromSource.putIfAbsent(id, new HashSet<>());
            predecessorMapFromSource.get(id).add(key);
        }));
        return predecessorMapFromSource;
    }

    private List<List<Concept>> getAllPaths(Map<String, Set<String>> predecessorMapFromSource) {
        Map<Concept, Set<String>> predecessorMap = new HashMap<>(predecessorMapFromSource.size());
        predecessorMapFromSource.forEach((key, value) -> predecessorMap.put(getConcept(tx, key), value));

        List<List<Concept>> allPaths = new ArrayList<>();
        List<Concept> firstPath = new ArrayList<>();
        firstPath.add(getConcept(tx, sourceId.getValue()));

        Deque<List<Concept>> queue = new ArrayDeque<>();
        queue.addLast(firstPath);
        while (!queue.isEmpty()) {
            List<Concept> currentPath = queue.pollFirst();
            if (predecessorMap.containsKey(currentPath.get(currentPath.size() - 1))) {
                Set<String> successors = predecessorMap.get(currentPath.get(currentPath.size() - 1));
                Iterator<String> iterator = successors.iterator();
                for (int i = 0; i < successors.size() - 1; i++) {
                    List<Concept> extendedPath = new ArrayList<>(currentPath);
                    extendedPath.add(getConcept(tx, iterator.next()));
                    queue.addLast(extendedPath);
                }
                currentPath.add(getConcept(tx, iterator.next()));
                queue.addLast(currentPath);
            } else {
                allPaths.add(currentPath);
            }
        }
        return allPaths;
    }

    private static Thing getConcept(Optional<GraknTx> tx, String conceptId) {
        return tx.get().getConcept(ConceptId.of(conceptId));
    }

    private static Thing getConcept(Optional<GraknTx> tx, ConceptId conceptId) {
        return tx.get().getConcept(conceptId);
    }

    @Override
    public PathQuery from(ConceptId sourceId) {
        this.sourceId = sourceId;
        return this;
    }

    @Override
    public PathQuery to(ConceptId destinationId) {
        this.destinationId = destinationId;
        return this;
    }

    @Override
    public PathQuery includeAttribute() {
        return (PathQuery) super.includeAttribute();
    }

    @Override
    public boolean isReadOnly() {
        return true;
    }

    @Override
    public PathQuery in(String... subTypeLabels) {
        return (PathQuery) super.in(subTypeLabels);
    }

    @Override
    public PathQuery in(Collection<Label> subLabels) {
        return (PathQuery) super.in(subLabels);
    }

    @Override
    String graqlString() {
        return "path from " + idToString(sourceId) + " to " + idToString(destinationId) + subtypeString();
    }

    @Override
    public PathQuery withTx(GraknTx tx) {
        return (PathQuery) super.withTx(tx);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        PathQueryImpl pathQuery = (PathQueryImpl) o;

        return sourceId.equals(pathQuery.sourceId) && destinationId.equals(pathQuery.destinationId);
    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + sourceId.hashCode();
        result = 31 * result + destinationId.hashCode();
        return result;
    }
}
