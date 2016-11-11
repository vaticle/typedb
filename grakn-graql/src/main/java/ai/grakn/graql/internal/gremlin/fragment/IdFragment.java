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

import ai.grakn.graql.internal.gremlin.FragmentPriority;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.GraphTraversal;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.__;
import org.apache.tinkerpop.gremlin.structure.Vertex;

import static ai.grakn.graql.internal.util.StringConverter.idToString;
import static ai.grakn.util.Schema.BaseType.CASTING;
import static ai.grakn.util.Schema.ConceptProperty.ITEM_IDENTIFIER;

class IdFragment extends AbstractFragment {

    private final String id;

    IdFragment(String start, String id) {
        super(start);
        this.id = id;
    }

    @Override
    public void applyTraversal(GraphTraversal<Vertex, Vertex> traversal) {
        // Whenever looking up by ID, we have to confirm this is not a casting
        traversal.has(ITEM_IDENTIFIER.name(), id).not(__.hasLabel(CASTING.name()));
    }

    @Override
    public String getName() {
        return "[id:" + idToString(id) + "]";
    }

    @Override
    public FragmentPriority getPriority() {
        return FragmentPriority.ID;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        IdFragment that = (IdFragment) o;

        return id != null ? id.equals(that.id) : that.id == null;

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + (id != null ? id.hashCode() : 0);
        return result;
    }

    @Override
    public long fragmentCost(long previousCost) {
        return 1;
    }
}
