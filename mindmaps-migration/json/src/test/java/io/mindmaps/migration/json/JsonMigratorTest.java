/*
 * MindmapsDB - A Distributed Semantic Database
 * Copyright (C) 2016  Mindmaps Research Ltd
 *
 * MindmapsDB is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * MindmapsDB is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with MindmapsDB. If not, see <http://www.gnu.org/licenses/gpl.txt>.
 */

package io.mindmaps.migration.json;

import com.google.common.collect.Sets;
import com.google.common.io.Files;
import io.mindmaps.MindmapsGraph;
import io.mindmaps.concept.*;
import io.mindmaps.engine.MindmapsEngineServer;
import io.mindmaps.engine.loader.BlockingLoader;
import io.mindmaps.engine.util.ConfigProperties;
import io.mindmaps.exception.MindmapsValidationException;
import io.mindmaps.factory.GraphFactory;
import io.mindmaps.graql.Graql;
import io.mindmaps.graql.internal.util.GraqlType;
import org.junit.*;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.toSet;
import static junit.framework.TestCase.assertEquals;
import static org.junit.Assert.assertTrue;

public class JsonMigratorTest {

    private MindmapsGraph graph;
    private JsonMigrator migrator;

    @BeforeClass
    public static void start(){
        System.setProperty(ConfigProperties.CONFIG_FILE_SYSTEM_PROPERTY,ConfigProperties.TEST_CONFIG_FILE);
        System.setProperty(ConfigProperties.CURRENT_DIR_SYSTEM_PROPERTY, System.getProperty("user.dir")+"/../");

        MindmapsEngineServer.start();
    }

    @AfterClass
    public static void stop(){
//        MindmapsEngineServer.stop();
    }

    @Before
    public void setup(){
        String GRAPH_NAME = ConfigProperties.getInstance().getProperty(ConfigProperties.DEFAULT_GRAPH_NAME_PROPERTY);

        graph = GraphFactory.getInstance().getGraphBatchLoading(GRAPH_NAME);
        BlockingLoader loader = new BlockingLoader(GRAPH_NAME);
        loader.setExecutorSize(1);

        migrator = new JsonMigrator(loader);
    }

    @After
    public void shutdown(){
        graph.clear();
    }

    @Test
    public void testMigrateSimpleSchemaData() {
        load(get("simple-schema/schema.gql"));

        String template = "  \n" +
                "$person isa person;\n" +
                " \n" +
                "$address isa address\n" +
                "  has city <address.city>;\n" +
                "\n" +
                "$street isa street-address\n" +
                "   has street <address.streetAddress.street>\n" +
                "   has number <address.streetAddress.number>;\n" +
                "\n" +
                "(address-with-street: $address, street-of-address: $street) isa address-has-street;\n" +
                "\n" +
                "(person-with-address: $person, address-of-person: $address) isa has-address;\n" +
                "\n" +
                "for { phoneNumber } do {\n" +
                "  $phone isa phone-number\n" +
                "    has location <location>\n" +
                "    has code <code>;\n" +
                "  \n" +
                "  (person-with-phone: $person, phone-of-person: $phone) isa has-phone;\n" +
                "  \n" +
                "} ";

        migrate(template, get("simple-schema/data.json"));

        EntityType personType = graph.getEntityType("person");
        assertEquals(1, personType.instances().size());

        Entity person = personType.instances().iterator().next();

        Entity address = getProperty(person, "has-address").asEntity();

        Entity streetAddress = getProperty(address, "address-has-street").asEntity();

        Resource number = getResource(streetAddress, "number").asResource();
        assertEquals(21L, number.getValue());

        Resource street = getResource(streetAddress, "street").asResource();
        assertEquals("2nd Street", street.getValue());

        Resource city = getResource(address, "city").asResource();
        assertEquals("New York", city.getValue());

        Collection<Instance> phoneNumbers = getProperties(person, "has-phone");
        assertEquals(2, phoneNumbers.size());

        boolean phoneNumbersCorrect = phoneNumbers.stream().allMatch(phoneNumber -> {
            Object location = getResource(phoneNumber, "location").getValue();
            Object code = getResource(phoneNumber, "code").getValue();
            return ((location.equals("home") && code.equals(44L)) || (location.equals("work") && code.equals(45L)));
        });

        assertTrue(phoneNumbersCorrect);
    }

    @Test
    public void testMigrateAllTypesData() {
        load(get("all-types/schema.gql"));

        String template = "" +
                "$x isa thing\n" +
                "  has a-boolean <a-boolean>\n" +
                "  has a-number  <a-number>\n" +
                "  for { array-of-ints } do {\n" +
                "  has a-int <.>\n" +
                "  }\n" +
                "  has a-string <a-string>\n" +
                "  if {a-null} do {has a-null <a-null>};";

        migrate(template, get("all-types/data.json"));

        EntityType rootType = graph.getEntityType("thing");
        Collection<Entity> things = rootType.instances();
        assertEquals(1, things.size());

        Entity thing = things.iterator().next();

        Collection<Object> integers = getResources(thing, "a-int").map(r -> r.asResource().getValue()).collect(toSet());
        assertEquals(Sets.newHashSet(1L, 2L, 3L), integers);

        Resource aBoolean = getResource(thing, "a-boolean");
        assertEquals(true, aBoolean.getValue());

        Resource aNumber = getResource(thing, "a-number");
        assertEquals(42.1, aNumber.getValue());

        Resource aString = getResource(thing, "a-string");
        assertEquals("hi", aString.getValue());

        assertEquals(0, graph.getResourceType("a-null").instances().size());
    }

    @Test
    public void testMigrateDirectory(){
        load(get("string-or-object/schema.gql"));

        String template = "\n" +
                "$thing isa the-thing\n" +
                "        has a-string if {the-thing.a-string} do {<the-thing.a-string>}\n" +
                "        else {<the-thing>} ;";

        migrate(template, get("string-or-object/data"));

        EntityType theThing = graph.getEntityType("the-thing");
        assertEquals(2, theThing.instances().size());

        Collection<Entity> things = theThing.instances();
        boolean thingsCorrect = things.stream().allMatch(thing -> {
            Object string = getResource(thing, "a-string").getValue();
            return string.equals("hello") || string.equals("goodbye");
        });

        assertTrue(thingsCorrect);
    }

    @Test
    public void testStringOrObject(){
        load(get("string-or-object/schema.gql"));

        String template = "\n" +
                "$thing isa the-thing\n" +
                "        has a-string if {the-thing.a-string} do {<the-thing.a-string>}\n" +
                "        else {<the-thing>} ;";

        migrate(template, get("string-or-object/data"));

        EntityType theThing = graph.getEntityType("the-thing");
        assertEquals(2, theThing.instances().size());


    }

    private Instance getProperty(Instance instance, String name) {
        assertEquals(1, getProperties(instance, name).size());
        return getProperties(instance, name).iterator().next();
    }

    private Collection<Instance> getProperties(Instance instance, String name) {
        RelationType relation = graph.getRelationType(name);

        Set<Instance> instances = new HashSet<>();

        relation.instances().stream()
                .filter(i -> i.rolePlayers().values().contains(instance))
                .forEach(i -> instances.addAll(i.rolePlayers().values()));

        instances.remove(instance);
        return instances;
    }

    private Resource getResource(Instance instance, String name) {
        assertEquals(1, getResources(instance, name).count());
        return getResources(instance, name).findAny().get();
    }

    private Stream<Resource> getResources(Instance instance, String name) {
        RoleType roleOwner = graph.getRoleType(GraqlType.HAS_RESOURCE_OWNER.getId(name));
        RoleType roleOther = graph.getRoleType(GraqlType.HAS_RESOURCE_VALUE.getId(name));

        Collection<Relation> relations = instance.relations(roleOwner);
        return relations.stream().map(r -> r.rolePlayers().get(roleOther).asResource());
    }

    private File get(String fileName){
        return new File(JsonMigratorTest.class.getClassLoader().getResource(fileName).getPath());
    }

    // common class
    private void migrate(String template, File file){
        migrator.migrate(template, file);
    }

    private void load(File ontology) {
        try {
            Graql.withGraph(graph)
                    .parseInsert(Files.readLines(ontology, StandardCharsets.UTF_8).stream().collect(joining("\n")))
                    .execute();

            graph.commit();
        } catch (IOException|MindmapsValidationException e){
            throw new RuntimeException(e);
        }
    }
}
