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

package ai.grakn.graql.internal.analytics;

import ai.grakn.concept.TypeId;
import ai.grakn.util.Schema;
import org.apache.commons.configuration.Configuration;
import org.apache.tinkerpop.gremlin.process.computer.Memory;
import org.apache.tinkerpop.gremlin.process.computer.MessageScope;
import org.apache.tinkerpop.gremlin.process.computer.Messenger;
import org.apache.tinkerpop.gremlin.structure.Graph;
import org.apache.tinkerpop.gremlin.structure.Vertex;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * The vertex program for computing the degree.
 * <p>
 *
 * @author Jason Liu
 * @author Sheldon Hall
 */

public class DegreeVertexProgram extends GraknVertexProgram<Long> {

    // element key
    public static final String DEGREE = "degreeVertexProgram.degree";
    private static final String OF_TYPE_LABELS = "degreeVertexProgram.ofTypeIds";

    Set<TypeId> ofTypeIds = new HashSet<>();

    String degree;

    // Needed internally for OLAP tasks
    public DegreeVertexProgram() {
    }

    public DegreeVertexProgram(Set<TypeId> types, Set<TypeId> ofTypeIds, String randomId) {
        selectedTypes = types;
        degree = DEGREE + randomId;
        this.ofTypeIds = ofTypeIds;
        this.persistentProperties.put(DEGREE, degree);
    }

    @Override
    public void storeState(final Configuration configuration) {
        super.storeState(configuration);
        ofTypeIds.forEach(type -> configuration.addProperty(OF_TYPE_LABELS + "." + type, type));
    }

    @Override
    public void loadState(final Graph graph, final Configuration configuration) {
        super.loadState(graph, configuration);
        configuration.subset(OF_TYPE_LABELS).getKeys().forEachRemaining(key ->
                ofTypeIds.add(TypeId.of(configuration.getInt(OF_TYPE_LABELS + "." + key))));
        degree = (String) this.persistentProperties.get(DEGREE);
    }

    @Override
    public Set<String> getElementComputeKeys() {
        return Collections.singleton(degree);
    }

    @Override
    public Set<MessageScope> getMessageScopes(final Memory memory) {
        switch (memory.getIteration()) {
            case 0:
                return messageScopeSetInstance;
            case 1:
                return messageScopeSetCasting;
            default:
                return Collections.emptySet();
        }
    }

    @Override
    public void safeExecute(final Vertex vertex, Messenger<Long> messenger, final Memory memory) {
        switch (memory.getIteration()) {

            case 0:
                if (selectedTypes.contains(Utility.getVertexTypeId(vertex))) {
                    degreeStepInstance(vertex, messenger);
                }
                break;

            case 1:
                if (vertex.label().equals(Schema.BaseType.CASTING.name())) {
                    degreeStepCasting(messenger);
                }
                break;

            case 2:
                TypeId typeId = Utility.getVertexTypeId(vertex);
                if (selectedTypes.contains(typeId) && ofTypeIds.contains(typeId)) {
                    vertex.property(degree, getMessageCount(messenger));
                }
                break;

            default:
                throw new RuntimeException("unreachable");
        }
    }

    @Override
    public boolean terminate(final Memory memory) {
        LOGGER.debug("Finished Degree Iteration " + memory.getIteration());
        return memory.getIteration() == 2;
    }

}
