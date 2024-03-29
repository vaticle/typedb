/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

package com.vaticle.typedb.core.test.integration;

import com.vaticle.typedb.core.TypeDB;
import com.vaticle.typedb.core.common.diagnostics.Diagnostics;
import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.parameters.Arguments;
import com.vaticle.typedb.core.common.parameters.Options;
import com.vaticle.typedb.core.concept.ConceptManager;
import com.vaticle.typedb.core.concept.thing.Attribute;
import com.vaticle.typedb.core.concept.type.AttributeType;
import com.vaticle.typedb.core.concept.type.EntityType;
import com.vaticle.typedb.core.concept.type.RelationType;
import com.vaticle.typedb.core.concept.type.RoleType;
import com.vaticle.typedb.core.concept.type.ThingType;
import com.vaticle.typedb.core.database.CoreDatabaseManager;
import com.vaticle.typedb.core.logic.LogicManager;
import com.vaticle.typedb.core.logic.Rule;
import com.vaticle.typedb.core.test.integration.util.Util;
import com.vaticle.typeql.lang.TypeQL;
import com.vaticle.typeql.lang.pattern.Pattern;
import com.vaticle.typeql.lang.pattern.statement.ThingStatement;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.LocalDateTime;
import java.util.Random;
import java.util.function.Consumer;
import java.util.stream.Stream;

import static com.vaticle.typedb.core.common.collection.Bytes.MB;
import static com.vaticle.typedb.core.concept.type.AttributeType.ValueType.BOOLEAN;
import static com.vaticle.typedb.core.concept.type.AttributeType.ValueType.DATETIME;
import static com.vaticle.typedb.core.concept.type.AttributeType.ValueType.DOUBLE;
import static com.vaticle.typedb.core.concept.type.AttributeType.ValueType.LONG;
import static com.vaticle.typedb.core.concept.type.AttributeType.ValueType.STRING;
import static com.vaticle.typedb.core.test.integration.util.Util.assertNotNulls;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class BasicTest {

    private static final String database = "basic-test";
    private static final Path dataDir = Paths.get(System.getProperty("user.dir")).resolve(database);
    private static final Path logDir = dataDir.resolve("logs");
    private static final Options.Database options = new Options.Database().dataDir(dataDir).reasonerDebuggerDir(logDir)
            .storageIndexCacheSize(500 * MB).storageDataCacheSize(500 * MB);

    @BeforeClass
    public static void beforeClass() {
        Diagnostics.Noop.initialise();
    }

    @Test
    public void single_threaded_attr_ownership_test() throws IOException {
        Util.resetDirectory(dataDir);
        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            typedb.create(database);
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.SCHEMA)) {
                try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.WRITE)) {
                    var personType = transaction.concepts().putEntityType("person");
                    var ageType = transaction.concepts().putAttributeType("age", LONG);
                    var nameType = transaction.concepts().putAttributeType("name", STRING);
                    personType.setOwns(ageType);
                    personType.setOwns(nameType);
                    transaction.commit();
                }
            }

            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.DATA)) {
                long start = System.currentTimeMillis();
                var iterations = 50_000;
                for (int i = 0; i < iterations; i++) {
                    try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.WRITE)) {
                        var personType = transaction.concepts().getEntityType("person");
                        var nameType = transaction.concepts().getAttributeType("name");
                        var ageType = transaction.concepts().getAttributeType("age");

                        var person = personType.create();
                        var name = nameType.asString().put(random_string());
                        var age = ageType.asLong().put(random.nextLong());
                        person.setHas(name);
                        person.setHas(age);

                        transaction.commit();
                    }
                }

                long end = System.currentTimeMillis();
                long duration_micros = (end - start) * 1000;
                double micros_per_iteration = (double) duration_micros / iterations;

                System.out.println("--- Micros per iteration: " + micros_per_iteration);
            }
        }
    }

    private static Random random = new Random(0);

    private static String random_string() {
        int leftLimit = 48; // numeral '0'
        int rightLimit = 122; // letter 'z'
        int targetStringLength = 10;

        int length = random.nextInt(255);

        String generatedString = random.ints(leftLimit, rightLimit + 1)
                .filter(i -> (i <= 57 || i >= 65) && (i <= 90 || i >= 97))
                .limit(length)
                .collect(StringBuilder::new, StringBuilder::appendCodePoint, StringBuilder::append)
                .toString();

        return generatedString;
    }

    private static void assert_transaction_read(TypeDB.Transaction transaction) {
        assertTrue(transaction.isOpen());
        assertTrue(transaction.type().isRead());

        ThingType rootType = transaction.concepts().getRootThingType();
        EntityType rootEntityType = transaction.concepts().getRootEntityType();
        RelationType rootRelationType = transaction.concepts().getRootRelationType();
        AttributeType rootAttributeType = transaction.concepts().getRootAttributeType();
        Util.assertNotNulls(rootType, rootEntityType, rootRelationType, rootAttributeType);

        Stream<Consumer<TypeDB.Transaction>> typeAssertions = Stream.of(
                tx -> {
                    AttributeType.String name = tx.concepts().getAttributeType("name").asString();
                    Util.assertNotNulls(name);
                    assertEquals(rootAttributeType, name.getSupertype());
                },
                tx -> {
                    AttributeType.Long age = tx.concepts().getAttributeType("age").asLong();
                    Util.assertNotNulls(age);
                    assertEquals(rootAttributeType, age.getSupertype());
                },
                tx -> {
                    RelationType marriage = tx.concepts().getRelationType("marriage");
                    RoleType husband = marriage.getRelates("husband");
                    RoleType wife = marriage.getRelates("wife");
                    Util.assertNotNulls(marriage, husband, wife);
                    assertEquals(rootRelationType, marriage.getSupertype());
                    assertEquals(rootRelationType.getRelates("role"), husband.getSupertype());
                    assertEquals(rootRelationType.getRelates("role"), wife.getSupertype());
                },
                tx -> {
                    RelationType employment = tx.concepts().getRelationType("employment");
                    RoleType employee = employment.getRelates("employee");
                    RoleType employer = employment.getRelates("employer");
                    Util.assertNotNulls(employment, employee, employer);
                    assertEquals(rootRelationType, employment.getSupertype());
                },
                tx -> {
                    EntityType person = tx.concepts().getEntityType("person");
                    Util.assertNotNulls(person);
                    assertEquals(rootEntityType, person.getSupertype());

                    Stream<Consumer<TypeDB.Transaction>> subPersonAssertions = Stream.of(
                            tx2 -> {
                                EntityType man = tx2.concepts().getEntityType("man");
                                Util.assertNotNulls(man);
                                assertEquals(person, man.getSupertype());
                            },
                            tx2 -> {
                                EntityType woman = tx2.concepts().getEntityType("woman");
                                Util.assertNotNulls(woman);
                                assertEquals(person, woman.getSupertype());
                            }
                    );
                    subPersonAssertions.parallel().forEach(assertions -> assertions.accept(tx));
                },
                tx -> {
                    EntityType company = tx.concepts().getEntityType("company");
                    Util.assertNotNulls(company);
                    assertEquals(rootEntityType, company.getSupertype());
                }
        );

        typeAssertions.parallel().forEach(assertion -> assertion.accept(transaction));
    }

    @Test
    public void write_types_concurrently_repeatedly() throws IOException, InterruptedException {
        for (int i = 0; i < 20; i++) {
            System.out.println(i + " ---- ");
            write_types_concurrently();
        }
    }

    @Test
    public void write_types_concurrently() throws IOException, InterruptedException {
        Util.resetDirectory(dataDir);
        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            typedb.create(database);

            assertTrue(typedb.isOpen());
            assertEquals(1, typedb.all().size());
            assertEquals(database, typedb.all().iterator().next().name());

            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.SCHEMA)) {

                assertTrue(session.isOpen());
                assertEquals(database, session.database().name());

                try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.READ)) {
                    assertTrue(transaction.isOpen());
                    assertTrue(transaction.type().isRead());

                    Stream<Consumer<TypeDB.Transaction>> rootTypeAssertions = Stream.of(
                            tx -> {
                                ThingType rootType = tx.concepts().getRootThingType();
                                assertNotNull(rootType);
                            },
                            tx -> {
                                EntityType rootEntityType = tx.concepts().getRootEntityType();
                                assertNotNull(rootEntityType);
                            },
                            tx -> {
                                RelationType rootRelationType = tx.concepts().getRootRelationType();
                                assertNotNull(rootRelationType);
                            },
                            tx -> {
                                AttributeType rootAttributeType = tx.concepts().getRootAttributeType();
                                assertNotNull(rootAttributeType);
                            }
                    );

                    rootTypeAssertions.parallel().forEach(assertion -> assertion.accept(transaction));
                }

                try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.WRITE)) {
                    assertTrue(transaction.isOpen());
                    assertTrue(transaction.type().isWrite());

                    ThingType rootType = transaction.concepts().getRootThingType();
                    EntityType rootEntityType = transaction.concepts().getRootEntityType();
                    RelationType rootRelationType = transaction.concepts().getRootRelationType();
                    AttributeType rootAttributeType = transaction.concepts().getRootAttributeType();
                    Util.assertNotNulls(rootType, rootEntityType, rootRelationType, rootAttributeType);

                    Stream<Consumer<TypeDB.Transaction>> typeAssertions = Stream.of(
                            tx -> {
                                AttributeType name = tx.concepts().putAttributeType("name", STRING).asString();
                                Util.assertNotNulls(name);
                                assertEquals(rootAttributeType, name.getSupertype());
                            },
                            tx -> {
                                AttributeType.Long age = tx.concepts().putAttributeType("age", LONG).asLong();
                                Util.assertNotNulls(age);
                                assertEquals(rootAttributeType, age.getSupertype());
                            },
                            tx -> {
                                RelationType marriage = tx.concepts().putRelationType("marriage");
                                marriage.setRelates("husband");
                                marriage.setRelates("wife");
                                Util.assertNotNulls(marriage);
                                assertEquals(rootRelationType, marriage.getSupertype());
                            },
                            tx -> {
                                RelationType employment = tx.concepts().putRelationType("employment");
                                employment.setRelates("employee");
                                employment.setRelates("employer");
                                Util.assertNotNulls(employment);
                                assertEquals(rootRelationType, employment.getSupertype());
                            },
                            tx -> {
                                EntityType person = tx.concepts().putEntityType("person");
                                Util.assertNotNulls(person);
                                assertEquals(rootEntityType, person.getSupertype());

                                Stream<Consumer<TypeDB.Transaction>> subPersonAssertions = Stream.of(
                                        tx2 -> {
                                            EntityType man = tx2.concepts().putEntityType("man");
                                            man.setSupertype(person);
                                            Util.assertNotNulls(man);
                                            assertEquals(person, man.getSupertype());
                                        },
                                        tx2 -> {
                                            EntityType woman = tx2.concepts().putEntityType("woman");
                                            woman.setSupertype(person);
                                            Util.assertNotNulls(woman);
                                            assertEquals(person, woman.getSupertype());
                                        }
                                );
                                subPersonAssertions.parallel().forEach(assertions -> assertions.accept(tx));
                            },
                            tx -> {
                                EntityType company = tx.concepts().putEntityType("company");
                                Util.assertNotNulls(company);
                                assertEquals(rootEntityType, company.getSupertype());
                            }
                    );

                    typeAssertions.parallel().forEach(assertion -> assertion.accept(transaction));
                    transaction.commit();
                }

                try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.READ)) {
                    assert_transaction_read(transaction);
                }
            }
        }


        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            assertTrue(typedb.isOpen());
            assertEquals(1, typedb.all().size());
            assertEquals(database, typedb.all().iterator().next().name());

            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.SCHEMA)) {

                assertTrue(session.isOpen());
                assertEquals(database, session.database().name());

                try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.READ)) {
                    assert_transaction_read(transaction);
                }

                try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.WRITE)) {
                    AttributeType.String gender = transaction.concepts().putAttributeType("gender", STRING).asString();
                    EntityType school = transaction.concepts().putEntityType("school");
                    RelationType teaching = transaction.concepts().putRelationType("teaching");
                    teaching.setRelates("teacher");
                    teaching.setRelates("student");
                    RoleType teacher = teaching.getRelates("teacher");
                    RoleType student = teaching.getRelates("student");
                    Util.assertNotNulls(gender, school, teaching, teacher, student);
                    transaction.commit();
                }

                try (TypeDB.Transaction transaction = session.transaction(Arguments.Transaction.Type.READ)) {
                    assert_transaction_read(transaction);
                    AttributeType.String gender = transaction.concepts().getAttributeType("gender").asString();
                    EntityType school = transaction.concepts().getEntityType("school");
                    RelationType teaching = transaction.concepts().getRelationType("teaching");
                    RoleType teacher = teaching.getRelates("teacher");
                    RoleType student = teaching.getRelates("student");
                    Util.assertNotNulls(gender, school, teaching, teacher, student);
                }
            }
        }
    }

    private void reset_directory_and_create_attribute_types() throws IOException {
        Util.resetDirectory(dataDir);

        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            typedb.create(database);
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.SCHEMA)) {
                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.WRITE)) {
                    txn.concepts().putAttributeType("is-alive", BOOLEAN);
                    txn.concepts().putAttributeType("age", LONG);
                    txn.concepts().putAttributeType("score", DOUBLE);
                    txn.concepts().putAttributeType("name", STRING);
                    txn.concepts().putAttributeType("birth-date", DATETIME);

                    txn.commit();
                }
            }
        }
    }

    @Test
    public void write_and_retrieve_attribute_ownership_rule() throws IOException {
        Util.resetDirectory(dataDir);

        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            typedb.create(database);
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.SCHEMA)) {
                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.WRITE)) {
                    ConceptManager conceptMgr = txn.concepts();
                    LogicManager logicMgr = txn.logic();
                    AttributeType name = conceptMgr.putAttributeType("name", STRING);
                    EntityType person = conceptMgr.putEntityType("person");
                    RelationType friendship = conceptMgr.putRelationType("friendship");
                    friendship.setRelates("friend");
                    person.setPlays(friendship.getRelates("friend"));
                    person.setOwns(name);
                    logicMgr.putRule(
                            "people-have-names",
                            TypeQL.parsePattern("{$x isa person; }").asConjunction(),
                            TypeQL.parseStatement("$x has name \"i have a name\"").asThing());
                    txn.commit();
                }
                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    ConceptManager conceptMgr = txn.concepts();
                    LogicManager logicMgr = txn.logic();

                    Rule rule = logicMgr.getRule("people-have-names");
                    Pattern when = rule.getWhenPreNormalised();
                    ThingStatement<?> then = rule.getThenPreNormalised();
                    assertEquals(TypeQL.parsePattern("{$x isa person;}"), when);
                    assertEquals(TypeQL.parseStatement("$x has name \"i have a name\""), then);
                }
            }
        }
    }

    @Test
    public void write_and_retrieve_relation_rule() throws IOException {
        Util.resetDirectory(dataDir);

        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            typedb.create(database);
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.SCHEMA)) {
                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.WRITE)) {
                    ConceptManager conceptMgr = txn.concepts();
                    LogicManager logicMgr = txn.logic();

                    EntityType person = conceptMgr.putEntityType("person");
                    RelationType friendship = conceptMgr.putRelationType("friendship");
                    friendship.setRelates("friend");
                    RelationType marriage = conceptMgr.putRelationType("marriage");
                    marriage.setRelates("spouse");
                    person.setPlays(friendship.getRelates("friend"));
                    person.setPlays(marriage.getRelates("spouse"));
                    logicMgr.putRule(
                            "marriage-is-friendship",
                            TypeQL.parsePattern("{$x isa person; $y isa person; (spouse: $x, spouse: $y) isa marriage; }").asConjunction(),
                            TypeQL.parseStatement("(friend: $x, friend: $y) isa friendship").asThing());
                    txn.commit();
                }
                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    ConceptManager conceptMgr = txn.concepts();
                    LogicManager logicMgr = txn.logic();
                    EntityType person = conceptMgr.getEntityType("person");
                    RelationType friendship = conceptMgr.getRelationType("friendship");
                    RoleType friend = friendship.getRelates("friend");
                    RelationType marriage = conceptMgr.getRelationType("marriage");
                    RoleType spouse = marriage.getRelates("spouse");

                    Rule rule = logicMgr.getRule("marriage-is-friendship");
                    Pattern when = rule.getWhenPreNormalised();
                    ThingStatement<?> then = rule.getThenPreNormalised();
                    assertEquals(TypeQL.parsePattern("{$x isa person; $y isa person; (spouse: $x, spouse: $y) isa marriage; }"), when);
                    assertEquals(TypeQL.parseStatement("(friend: $x, friend: $y) isa friendship"), then);
                }
            }
        }
    }

    private AttributeType.Boolean isAlive(TypeDB.Transaction txn) {
        return txn.concepts().getAttributeType("is-alive").asBoolean();
    }

    private AttributeType.Long age(TypeDB.Transaction txn) {
        return txn.concepts().getAttributeType("age").asLong();
    }

    private AttributeType.Double score(TypeDB.Transaction txn) {
        return txn.concepts().getAttributeType("score").asDouble();
    }

    private AttributeType.String name(TypeDB.Transaction txn) {
        return txn.concepts().getAttributeType("name").asString();
    }

    private AttributeType.DateTime dob(TypeDB.Transaction txn) {
        return txn.concepts().getAttributeType("birth-date").asDateTime();
    }

    @Test
    public void write_attributes_successfully_repeatedly() throws IOException {
        for (int i = 0; i < 20; i++) {
            System.out.println(i + " ---- ");
            write_attributes_successfully();
        }
    }

    @Test
    public void write_attributes_successfully() throws IOException {
        LocalDateTime date_1991_1_1_0_0 = LocalDateTime.of(1991, 1, 1, 0, 0);
        reset_directory_and_create_attribute_types();

        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.DATA)) {
                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.WRITE)) {
                    isAlive(txn).put(true);
                    age(txn).put(18);
                    score(txn).put(90.5);
                    name(txn).put("alice");
                    dob(txn).put(date_1991_1_1_0_0);

                    assertEquals(1, isAlive(txn).getInstances().count());
                    assertTrue(isAlive(txn).getInstances().anyMatch(att -> att.getValue().equals(true)));

                    assertEquals(1, age(txn).getInstances().count());
                    assertTrue(age(txn).getInstances().anyMatch(att -> att.getValue() == 18));

                    assertEquals(1, score(txn).getInstances().count());
                    assertTrue(score(txn).getInstances().anyMatch(att -> att.getValue() == 90.5));

                    assertEquals(1, name(txn).getInstances().count());
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("alice")));

                    assertEquals(1, dob(txn).getInstances().count());
                    assertTrue(dob(txn).getInstances().anyMatch(att -> att.getValue().equals(date_1991_1_1_0_0)));

                    txn.commit();
                }

                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    LocalDateTime dateTime = LocalDateTime.of(1991, 1, 1, 0, 0);

                    Attribute.Boolean isAlive = isAlive(txn).get(true);
                    Attribute.Long age = age(txn).get(18);
                    Attribute.Double score = score(txn).get(90.5);
                    Attribute.String name = name(txn).get("alice");
                    Attribute.DateTime dob = dob(txn).get(dateTime);

                    assertNotNulls(isAlive, age, score, name, dob);
                    assertEquals(true, isAlive.getValue());
                    assertEquals(18, age.getValue().longValue());
                    assertEquals(90.5, score.getValue(), 0.001);
                    assertEquals("alice", name.getValue());
                    assertEquals(dateTime, dob.getValue());

                    assertEquals(1, isAlive(txn).getInstances().count());
                    assertTrue(isAlive(txn).getInstances().anyMatch(att -> att.getValue().equals(true)));

                    assertEquals(1, age(txn).getInstances().count());
                    assertTrue(age(txn).getInstances().anyMatch(att -> att.getValue() == 18));

                    assertEquals(1, score(txn).getInstances().count());
                    assertTrue(score(txn).getInstances().anyMatch(att -> att.getValue() == 90.5));

                    assertEquals(1, name(txn).getInstances().count());
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("alice")));

                    assertEquals(1, dob(txn).getInstances().count());
                    assertTrue(dob(txn).getInstances().anyMatch(att -> att.getValue().equals(date_1991_1_1_0_0)));
                }
            }
        }
    }

    @Test
    public void write_different_attributes_in_parallel_successfully_repeatedly() throws IOException {
        for (int i = 0; i < 20; i++) {
            System.out.println(i + " ---- ");
            write_different_attributes_in_parallel_successfully();
        }
    }

    @Test
    public void write_different_attributes_in_parallel_successfully() throws IOException {
        LocalDateTime date_1991_2_3_4_5 = LocalDateTime.of(1991, 2, 3, 4, 5);
        LocalDateTime date_1992_3_4_5_6 = LocalDateTime.of(1992, 3, 4, 5, 6);
        LocalDateTime date_1993_4_5_6_7 = LocalDateTime.of(1993, 4, 5, 6, 7);

        reset_directory_and_create_attribute_types();

        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.DATA)) {
                TypeDB.Transaction txn1 = session.transaction(Arguments.Transaction.Type.WRITE);
                TypeDB.Transaction txn2 = session.transaction(Arguments.Transaction.Type.WRITE);
                TypeDB.Transaction txn3 = session.transaction(Arguments.Transaction.Type.WRITE);

                isAlive(txn1).put(true);
                isAlive(txn2).put(false);
                age(txn1).put(17);
                age(txn2).put(18);
                age(txn3).put(19);
                score(txn1).put(70.5);
                score(txn2).put(80.6);
                score(txn3).put(90.7);
                name(txn1).put("alice");
                name(txn2).put("bob");
                name(txn3).put("charlie");
                dob(txn1).put(date_1991_2_3_4_5);
                dob(txn2).put(date_1992_3_4_5_6);
                dob(txn3).put(date_1993_4_5_6_7);

                assertEquals(1, isAlive(txn1).getInstances().count());
                assertTrue(isAlive(txn1).getInstances().anyMatch(att -> att.getValue().equals(true)));
                assertEquals(1, isAlive(txn2).getInstances().count());
                assertTrue(isAlive(txn2).getInstances().anyMatch(att -> att.getValue().equals(false)));

                assertEquals(1, age(txn1).getInstances().count());
                assertTrue(age(txn1).getInstances().anyMatch(att -> att.getValue() == 17));
                assertEquals(1, age(txn2).getInstances().count());
                assertTrue(age(txn2).getInstances().anyMatch(att -> att.getValue() == 18));
                assertEquals(1, age(txn3).getInstances().count());
                assertTrue(age(txn3).getInstances().anyMatch(att -> att.getValue() == 19));

                assertEquals(1, score(txn1).getInstances().count());
                assertTrue(score(txn1).getInstances().anyMatch(att -> att.getValue() == 70.5));
                assertEquals(1, score(txn2).getInstances().count());
                assertTrue(score(txn2).getInstances().anyMatch(att -> att.getValue() == 80.6));
                assertEquals(1, score(txn3).getInstances().count());
                assertTrue(score(txn3).getInstances().anyMatch(att -> att.getValue() == 90.7));

                assertEquals(1, name(txn1).getInstances().count());
                assertTrue(name(txn1).getInstances().anyMatch(att -> att.getValue().equals("alice")));
                assertEquals(1, name(txn2).getInstances().count());
                assertTrue(name(txn2).getInstances().anyMatch(att -> att.getValue().equals("bob")));
                assertEquals(1, name(txn3).getInstances().count());
                assertTrue(name(txn3).getInstances().anyMatch(att -> att.getValue().equals("charlie")));

                assertEquals(1, dob(txn1).getInstances().count());
                assertTrue(dob(txn1).getInstances().anyMatch(att -> att.getValue().equals(date_1991_2_3_4_5)));
                assertEquals(1, dob(txn2).getInstances().count());
                assertTrue(dob(txn2).getInstances().anyMatch(att -> att.getValue().equals(date_1992_3_4_5_6)));
                assertEquals(1, dob(txn3).getInstances().count());
                assertTrue(dob(txn3).getInstances().anyMatch(att -> att.getValue().equals(date_1993_4_5_6_7)));

                txn1.commit();
                txn2.commit();
                txn3.commit();

                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    LocalDateTime d1 = LocalDateTime.of(1991, 2, 3, 4, 5);
                    LocalDateTime d2 = LocalDateTime.of(1992, 3, 4, 5, 6);
                    LocalDateTime d3 = LocalDateTime.of(1993, 4, 5, 6, 7);

                    assertEquals(true, isAlive(txn).get(true).getValue());
                    assertEquals(false, isAlive(txn).get(false).getValue());
                    assertEquals(17, age(txn).get(17).getValue().longValue());
                    assertEquals(18, age(txn).get(18).getValue().longValue());
                    assertEquals(19, age(txn).get(19).getValue().longValue());
                    assertEquals(70.5, score(txn).get(70.5).getValue(), 0.001);
                    assertEquals(80.6, score(txn).get(80.6).getValue(), 0.001);
                    assertEquals(90.7, score(txn).get(90.7).getValue(), 0.001);
                    assertEquals("alice", name(txn).get("alice").getValue());
                    assertEquals("bob", name(txn).get("bob").getValue());
                    assertEquals("charlie", name(txn).get("charlie").getValue());
                    assertEquals(d1, dob(txn).get(d1).getValue());
                    assertEquals(d2, dob(txn).get(d2).getValue());
                    assertEquals(d3, dob(txn).get(d3).getValue());

                    assertEquals(2, isAlive(txn).getInstances().count());
                    assertTrue(isAlive(txn).getInstances().anyMatch(att -> att.getValue().equals(true)));
                    assertTrue(isAlive(txn).getInstances().anyMatch(att -> att.getValue().equals(false)));

                    assertEquals(3, age(txn).getInstances().count());
                    assertTrue(age(txn).getInstances().anyMatch(att -> att.getValue() == 17));
                    assertTrue(age(txn).getInstances().anyMatch(att -> att.getValue() == 18));
                    assertTrue(age(txn).getInstances().anyMatch(att -> att.getValue() == 19));

                    assertEquals(3, score(txn).getInstances().count());
                    assertTrue(score(txn).getInstances().anyMatch(att -> att.getValue() == 70.5));
                    assertTrue(score(txn).getInstances().anyMatch(att -> att.getValue() == 80.6));
                    assertTrue(score(txn).getInstances().anyMatch(att -> att.getValue() == 90.7));

                    assertEquals(3, name(txn).getInstances().count());
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("alice")));
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("bob")));
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("charlie")));

                    assertEquals(3, dob(txn).getInstances().count());
                    assertTrue(dob(txn).getInstances().anyMatch(att -> att.getValue().equals(date_1991_2_3_4_5)));
                    assertTrue(dob(txn).getInstances().anyMatch(att -> att.getValue().equals(date_1992_3_4_5_6)));
                    assertTrue(dob(txn).getInstances().anyMatch(att -> att.getValue().equals(date_1993_4_5_6_7)));
                }
            }
        }
    }

    @Test
    public void write_identical_attributes_in_parallel_successfully_repeatedly() throws IOException {
        for (int i = 0; i < 20; i++) {
            System.out.println(i + " ---- ");
            write_identical_attributes_in_parallel_successfully();
        }
    }

    @Test
    public void write_identical_attributes_in_parallel_successfully() throws IOException {
        reset_directory_and_create_attribute_types();

        LocalDateTime date_1992_2_3_4_5 = LocalDateTime.of(1991, 2, 3, 4, 5);

        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.DATA)) {
                TypeDB.Transaction txn1 = session.transaction(Arguments.Transaction.Type.WRITE);
                TypeDB.Transaction txn2 = session.transaction(Arguments.Transaction.Type.WRITE);
                TypeDB.Transaction txn3 = session.transaction(Arguments.Transaction.Type.WRITE);

                isAlive(txn1).put(true);
                isAlive(txn2).put(true);
                isAlive(txn3).put(true);
                age(txn1).put(17);
                age(txn2).put(17);
                age(txn3).put(17);
                score(txn1).put(70.5);
                score(txn2).put(70.5);
                score(txn3).put(70.5);
                name(txn1).put("alice");
                name(txn2).put("alice");
                name(txn3).put("alice");
                dob(txn1).put(date_1992_2_3_4_5);
                dob(txn2).put(date_1992_2_3_4_5);
                dob(txn3).put(date_1992_2_3_4_5);

                assertEquals(1, isAlive(txn1).getInstances().count());
                assertTrue(isAlive(txn1).getInstances().anyMatch(att -> att.getValue().equals(true)));
                assertEquals(1, isAlive(txn2).getInstances().count());
                assertTrue(isAlive(txn2).getInstances().anyMatch(att -> att.getValue().equals(true)));
                assertEquals(1, isAlive(txn3).getInstances().count());
                assertTrue(isAlive(txn2).getInstances().anyMatch(att -> att.getValue().equals(true)));

                assertEquals(1, age(txn1).getInstances().count());
                assertTrue(age(txn1).getInstances().anyMatch(att -> att.getValue() == 17));
                assertEquals(1, age(txn2).getInstances().count());
                assertTrue(age(txn2).getInstances().anyMatch(att -> att.getValue() == 17));
                assertEquals(1, age(txn3).getInstances().count());
                assertTrue(age(txn3).getInstances().anyMatch(att -> att.getValue() == 17));

                assertEquals(1, score(txn1).getInstances().count());
                assertTrue(score(txn1).getInstances().anyMatch(att -> att.getValue() == 70.5));
                assertEquals(1, score(txn2).getInstances().count());
                assertTrue(score(txn2).getInstances().anyMatch(att -> att.getValue() == 70.5));
                assertEquals(1, score(txn3).getInstances().count());
                assertTrue(score(txn3).getInstances().anyMatch(att -> att.getValue() == 70.5));

                assertEquals(1, name(txn1).getInstances().count());
                assertTrue(name(txn1).getInstances().anyMatch(att -> att.getValue().equals("alice")));
                assertEquals(1, name(txn2).getInstances().count());
                assertTrue(name(txn2).getInstances().anyMatch(att -> att.getValue().equals("alice")));
                assertEquals(1, name(txn3).getInstances().count());
                assertTrue(name(txn3).getInstances().anyMatch(att -> att.getValue().equals("alice")));

                assertEquals(1, dob(txn1).getInstances().count());
                assertTrue(dob(txn1).getInstances().anyMatch(att -> att.getValue().equals(date_1992_2_3_4_5)));
                assertEquals(1, dob(txn2).getInstances().count());
                assertTrue(dob(txn2).getInstances().anyMatch(att -> att.getValue().equals(date_1992_2_3_4_5)));
                assertEquals(1, dob(txn3).getInstances().count());
                assertTrue(dob(txn3).getInstances().anyMatch(att -> att.getValue().equals(date_1992_2_3_4_5)));

                txn1.commit();
                txn2.commit();
                txn3.commit();

                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {

                    assertEquals(true, isAlive(txn).get(true).getValue());
                    assertEquals(17, age(txn).get(17).getValue().longValue());
                    assertEquals(70.5, score(txn).get(70.5).getValue(), 0.001);
                    assertEquals("alice", name(txn).get("alice").getValue());
                    assertEquals(date_1992_2_3_4_5, dob(txn).get(date_1992_2_3_4_5).getValue());

                    assertEquals(1, isAlive(txn).getInstances().count());
                    assertTrue(isAlive(txn).getInstances().anyMatch(att -> att.getValue().equals(true)));

                    assertEquals(1, age(txn).getInstances().count());
                    assertTrue(age(txn).getInstances().anyMatch(att -> att.getValue() == 17));

                    assertEquals(1, score(txn).getInstances().count());
                    assertTrue(score(txn).getInstances().anyMatch(att -> att.getValue() == 70.5));

                    assertEquals(1, name(txn).getInstances().count());
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("alice")));

                    assertEquals(1, dob(txn).getInstances().count());
                    assertTrue(dob(txn).getInstances().anyMatch(att -> att.getValue().equals(date_1992_2_3_4_5)));
                }
            }
        }
    }

    @Test
    public void write_and_delete_attributes_concurrently_repeatedly() throws IOException {
        for (int i = 0; i < 20; i++) {
            System.out.println(i + " ---- ");
            write_and_delete_attributes_concurrently();
        }
    }

    @Test
    public void write_and_delete_attributes_concurrently() throws IOException {
        reset_directory_and_create_attribute_types();

        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            try (TypeDB.Session session = typedb.session(database, Arguments.Session.Type.DATA)) {
                TypeDB.Transaction txn1 = session.transaction(Arguments.Transaction.Type.WRITE);
                TypeDB.Transaction txn2 = session.transaction(Arguments.Transaction.Type.WRITE);

                name(txn1).put("alice");
                name(txn2).put("alice");

                txn1.commit();
                txn2.commit();

                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    assertEquals("alice", name(txn).get("alice").getValue());
                    assertEquals(1, name(txn).getInstances().count());
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("alice")));
                }

                txn1 = session.transaction(Arguments.Transaction.Type.WRITE);
                txn2 = session.transaction(Arguments.Transaction.Type.WRITE);

                name(txn1).put("alice");
                name(txn2).get("alice").delete();

                assertEquals(0, name(txn2).getInstances().count());
                assertEquals(1, name(txn1).getInstances().count());
                assertTrue(name(txn1).getInstances().anyMatch(att -> att.getValue().equals("alice")));

                txn1.commit(); // write before delete
                try {
                    txn2.commit();
                    fail("The delete operation in TX2 is not supposed to succeed");
                } catch (Exception ignored) {
                    assertTrue(true);
                }

                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    assertEquals("alice", name(txn).get("alice").getValue());
                    assertEquals(1, name(txn).getInstances().count());
                    assertTrue(name(txn).getInstances().anyMatch(att -> att.getValue().equals("alice")));
                }

                txn1 = session.transaction(Arguments.Transaction.Type.WRITE);
                txn2 = session.transaction(Arguments.Transaction.Type.WRITE);

                name(txn1).put("alice");
                name(txn2).get("alice").delete();

                txn2.commit();
                try {
                    txn1.commit();
                    fail("put and delete should conflict in any order.");
                } catch (TypeDBException e) {
                    assertTrue(true);
                }

                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    assertEquals(0, name(txn).getInstances().count());
                }

                txn1 = session.transaction(Arguments.Transaction.Type.WRITE);
                name(txn1).put("alice");
                txn1.commit();

                txn1 = session.transaction(Arguments.Transaction.Type.WRITE);
                txn2 = session.transaction(Arguments.Transaction.Type.WRITE);

                name(txn1).get("alice").delete();
                name(txn2).get("alice").delete();

                txn1.commit(); // delete concurrently is not a conflict
                txn2.commit();

                try (TypeDB.Transaction txn = session.transaction(Arguments.Transaction.Type.READ)) {
                    assertNull(name(txn).get("alice"));
                    assertEquals(0, name(txn).getInstances().count());
                }
            }
        }
    }

    @Test
    public void test_query_cancelled_asynchronously() throws IOException {
        Util.resetDirectory(dataDir);
        try (TypeDB.DatabaseManager typedb = CoreDatabaseManager.open(options)) {
            typedb.create(database);
            for (int i = 0; i < 20; i++) {
                new Thread(() -> {
                    TypeDB.Session session = typedb.session(database, Arguments.Session.Type.DATA);
                    TypeDB.Transaction tx = session.transaction(Arguments.Transaction.Type.WRITE);
                    new Thread(() -> {
                        try {
                            Thread.sleep(1);
                        } catch (InterruptedException e) {
                            e.printStackTrace();
                        }
                        tx.close();
                        session.close();
                    }).start();
                    tx.query().get(TypeQL.parseQuery("match $x sub thing; get;").asGet());
                }).start();
            }
            TypeDB.Session session = typedb.session(database, Arguments.Session.Type.DATA);
            TypeDB.Transaction tx = session.transaction(Arguments.Transaction.Type.WRITE);
            tx.query().get(TypeQL.parseQuery("match $x sub thing; get;").asGet());
        }
    }
}
