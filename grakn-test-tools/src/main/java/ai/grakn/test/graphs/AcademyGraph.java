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

package ai.grakn.test.graphs;

import ai.grakn.GraknTx;
import ai.grakn.test.SampleKBContext;

import java.util.function.Consumer;

/**
 *
 * @author Kasper Piskorski
 *
 */
public class AcademyGraph extends TestGraph {

    final private static String schemaFile = "academy/schema.gql";
    final private static String dataFile = "academy/data.gql";
    final private static String rulesFile = "academy/rules.gql";

    public static Consumer<GraknTx> get() {
        return new AcademyGraph().build();
    }

    @Override
    public Consumer<GraknTx> build() {
        return (GraknTx graph) -> {
            SampleKBContext.loadFromFile(graph, schemaFile);
            SampleKBContext.loadFromFile(graph, dataFile);
            SampleKBContext.loadFromFile(graph, rulesFile);
        };
    }
}
