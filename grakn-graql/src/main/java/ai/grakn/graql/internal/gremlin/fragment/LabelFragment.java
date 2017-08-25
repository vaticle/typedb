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

package ai.grakn.graql.internal.gremlin.fragment;

import ai.grakn.GraknTx;
import ai.grakn.concept.Label;
import ai.grakn.graql.Var;
import ai.grakn.graql.admin.VarProperty;
import com.google.common.collect.ImmutableSet;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.GraphTraversal;
import org.apache.tinkerpop.gremlin.structure.Element;

import java.util.Optional;

import static ai.grakn.graql.internal.util.StringConverter.typeLabelToString;
import static ai.grakn.util.Schema.VertexProperty.LABEL_ID;

class LabelFragment extends Fragment {

    private final Label label;
    private final Var start;
    private final Optional<Var> end = Optional.empty();
    private final ImmutableSet<Var> otherVarNames = ImmutableSet.of();
    private VarProperty varProperty; // For reasoner to map fragments to atoms

    LabelFragment(VarProperty varProperty, Var start, Label label) {
        super();
        this.varProperty = varProperty;
        this.start = start;
        this.label = label;
    }

    @Override
    public GraphTraversal<Element, ? extends Element> applyTraversal(
            GraphTraversal<Element, ? extends Element> traversal, GraknTx graph) {

        return traversal.has(LABEL_ID.name(), graph.admin().convertToId(label).getValue());
    }

    @Override
    public String getName() {
        return "[label:" + typeLabelToString(label) + "]";
    }

    @Override
    public double fragmentCost() {
        return COST_INDEX;
    }

    @Override
    public boolean hasFixedFragmentCost() {
        return true;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        LabelFragment that = (LabelFragment) o;

        return label != null ? label.equals(that.label) : that.label == null;

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + (label != null ? label.hashCode() : 0);
        return result;
    }

    /**
     * Get the corresponding property
     */
    public VarProperty getVarProperty() {
        return varProperty;
    }

    /**
     * @return the variable name that this fragment starts from in the query
     */
    @Override
    public final Var getStart() {
        return start;
    }

    /**
     * @return the variable name that this fragment ends at in the query, if this query has an end variable
     */
    @Override
    public final Optional<Var> getEnd() {
        return end;
    }

    @Override
    ImmutableSet<Var> otherVarNames() {
        return otherVarNames;
    }
}
