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

package ai.grakn.graphs;

import ai.grakn.GraknGraphFactory;

import java.util.function.Consumer;

public class SNBGraph extends TestGraph{

    public static Consumer<GraknGraphFactory> get() {
        return new SNBGraph().build();
    }

    @Override
    protected void buildOntology(GraknGraphFactory factory) {
        loadFromFile(factory, "ldbc-snb-ontology.gql");
        loadFromFile(factory, "ldbc-snb-product-ontology.gql");
    }

    @Override
    protected void buildRules(GraknGraphFactory factory) {
        loadFromFile(factory, "ldbc-snb-rules.gql");
    }

    @Override
    protected void buildInstances(GraknGraphFactory factory) {
        loadFromFile(factory, "ldbc-snb-data.gql");
    }
}
