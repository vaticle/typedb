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

package ai.grakn.dist;

import ai.grakn.Grakn;
import ai.grakn.GraknTx;
import ai.grakn.GraknTxType;
import ai.grakn.graql.Query;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

import static ai.grakn.graql.Graql.var;
import static ai.grakn.util.GraqlTestUtil.assertExists;
import static java.util.stream.Collectors.joining;

public class ExamplesTest {
    private GraknTx tx;

    @Before
    public void setUp() {
        tx = Grakn.session(Grakn.IN_MEMORY, "mypokemongraph").transaction(GraknTxType.WRITE);
    }

    @After
    public void close(){
        tx.commit();
        tx.close();
    }

    @Test
    public void afterLoadingModernExample_MarkoIsInTheKB() throws IOException {
        runInsertQuery("src/examples/modern.gql");
        assertExists(tx, var().has("name", "marko").isa("person"));
    }

    @Test
    public void afterLoadingPokemonExample_PikachuIsInTheKB() throws IOException {
        runInsertQuery("src/examples/pokemon.gql");
        assertExists(tx, var().rel(var().has("name", "Pikachu")).rel(var().has("name", "electric")).isa("has-type"));
    }

    @Test
    public void afterLoadingGenealogyExample_MaryIsInTheKB() throws IOException {
        runInsertQuery("src/examples/basic-genealogy.gql");
        assertExists(tx, var().has("identifier", "Mary Guthrie"));
    }

    private void runInsertQuery(String path) throws IOException {
        String query = Files.readAllLines(Paths.get(path)).stream().collect(joining("\n"));
        tx.graql().parser().parseList(query).forEach(Query::execute);
    }
}
