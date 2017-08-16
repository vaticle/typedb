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

package ai.grakn.graql.internal.query.match;

import ai.grakn.GraknTx;
import ai.grakn.concept.OntologyConcept;
import ai.grakn.exception.GraqlQueryException;
import ai.grakn.graql.admin.Answer;

import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Modifier that specifies the graph to execute the match query with.
 */
class MatchQueryGraph extends MatchQueryModifier {

    private final GraknTx graph;

    MatchQueryGraph(GraknTx graph, AbstractMatchQuery inner) {
        super(inner);
        this.graph = graph;
    }

    @Override
    public Stream<Answer> stream(Optional<GraknTx> graph) {
        if (graph.isPresent()) {
            throw GraqlQueryException.multipleGraphs();
        }

        return inner.stream(Optional.of(this.graph));
    }

    @Override
    public Optional<GraknTx> getGraph() {
        return Optional.of(graph);
    }

    @Override
    public Set<OntologyConcept> getOntologyConcepts() {
        return inner.getOntologyConcepts(graph);
    }

    @Override
    protected String modifierString() {
        return "";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        MatchQueryGraph maps = (MatchQueryGraph) o;

        return graph.equals(maps.graph);
    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + graph.hashCode();
        return result;
    }
}
