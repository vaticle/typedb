/*
 * GRAKN.AI - THE KNOWLEDGE GRAPH
 * Copyright (C) 2018 Grakn Labs Ltd
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package grakn.core.graql.internal.gremlin.fragment;

import com.google.auto.value.AutoValue;
import grakn.core.graql.internal.Schema;
import grakn.core.graql.internal.gremlin.spanningtree.graph.DirectedEdge;
import grakn.core.graql.internal.gremlin.spanningtree.graph.Node;
import grakn.core.graql.internal.gremlin.spanningtree.graph.NodeId;
import grakn.core.graql.internal.gremlin.spanningtree.util.Weighted;
import grakn.core.graql.query.statement.Variable;
import grakn.core.server.session.TransactionOLTP;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.GraphTraversal;
import org.apache.tinkerpop.gremlin.structure.Element;
import org.apache.tinkerpop.gremlin.structure.Vertex;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import static grakn.core.graql.internal.Schema.EdgeLabel.PLAYS;

@AutoValue
abstract class InPlaysFragment extends Fragment {

    @Override
    public abstract Variable end();

    abstract boolean required();

    @Override
    public GraphTraversal<Vertex, ? extends Element> applyTraversalInner(
            GraphTraversal<Vertex, ? extends Element> traversal, TransactionOLTP graph, Collection<Variable> vars) {
        GraphTraversal<Vertex, Vertex> vertexTraversal = Fragments.isVertex(traversal);
        if (required()) {
            vertexTraversal.inE(PLAYS.getLabel()).has(Schema.EdgeProperty.REQUIRED.name()).otherV();
        } else {
            vertexTraversal.in(PLAYS.getLabel());
        }

        return Fragments.inSubs(vertexTraversal);
    }

    @Override
    public String name() {
        if (required()) {
            return "<-[plays:required]-";
        } else {
            return "<-[plays]-";
        }
    }

    @Override
    public double internalFragmentCost() {
        return COST_TYPES_PER_ROLE;
    }

    @Override
    public Set<Weighted<DirectedEdge<Node>>> directedEdges(Map<NodeId, Node> nodes,
                                                           Map<Node, Map<Node, Fragment>> edges) {
        return directedEdges(NodeId.NodeType.PLAYS, nodes, edges);
    }
}
