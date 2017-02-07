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

package ai.grakn.test.client;

import ai.grakn.Grakn;
import ai.grakn.GraknGraph;
import ai.grakn.concept.Entity;
import ai.grakn.concept.EntityType;
import ai.grakn.concept.ResourceType;
import ai.grakn.client.LoaderClient;
import ai.grakn.exception.GraknValidationException;
import ai.grakn.graql.Graql;
import ai.grakn.graql.InsertQuery;
import ai.grakn.test.EngineContext;
import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import mjson.Json;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.UUID;

import static ai.grakn.graql.Graql.var;
import static org.junit.Assert.assertEquals;

public class LoaderClientTest {

    private LoaderClient loader;
    private GraknGraph graph;

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Rule
    public final EngineContext engine = EngineContext.startDistributedServer();

    @Before
    public void setup() {
        ((Logger) org.slf4j.LoggerFactory.getLogger(LoaderClient.class)).setLevel(Level.DEBUG);

        graph = engine.graphWithNewKeyspace();
        loader = new LoaderClient(graph.getKeyspace(), Grakn.DEFAULT_URI);
        loadOntology(graph.getKeyspace());
    }

    @Test
    public void loaderDefaultBatchSizeTest() {
        loadAndTime();
    }

    @Test
    public void loaderNewBatchSizeTest() {
        loader.setBatchSize(20);
        loadAndTime();
    }

    @Test
    public void loadWithSmallNumberActiveTasksToBlockTest(){
        loader.setNumberActiveTasks(1);
        loadAndTime();
    }

    public static void loadOntology(String keyspace){
        GraknGraph graph = Grakn.factory(Grakn.DEFAULT_URI, keyspace).getGraph();

        EntityType nameTag = graph.putEntityType("name_tag");
        ResourceType<String> nameTagString = graph.putResourceType("name_tag_string", ResourceType.DataType.STRING);
        ResourceType<String> nameTagId = graph.putResourceType("name_tag_id", ResourceType.DataType.STRING);

        nameTag.hasResource(nameTagString);
        nameTag.hasResource(nameTagId);

        try {
            graph.commit();
        } catch (GraknValidationException e){
            throw new RuntimeException(e);
        }
    }

    private long loadAndTime(){
        long startTime = System.currentTimeMillis();

        Collection<String> ids = new ArrayList<>();

        for(int i = 0; i < 50; i++){
            String id = UUID.randomUUID().toString();

            ids.add(id);

            InsertQuery query = Graql.insert(
                    var().isa("name_tag")
                            .has("name_tag_string", UUID.randomUUID().toString())
                            .has("name_tag_id", id));

            loader.add(query);
        }

        loader.waitToFinish();

        long duration = System.currentTimeMillis() - startTime;
        System.out.println("Time to load: " + duration);

        Collection<Entity> nameTags = graph.getEntityType("name_tag").instances();

        assertEquals(50, nameTags.size());
        ids.stream().map(graph::getResourcesByValue).forEach(Assert::assertNotNull);

        return duration;
    }
}
