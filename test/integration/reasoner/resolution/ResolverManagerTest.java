/*
 * Copyright (C) 2021 Grakn Labs
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

package grakn.core.reasoner.resolution;

import grakn.core.Grakn;
import grakn.core.common.parameters.Arguments;
import grakn.core.concept.ConceptManager;
import grakn.core.concept.type.EntityType;
import grakn.core.concept.type.RelationType;
import grakn.core.logic.LogicManager;
import grakn.core.logic.Rule;
import grakn.core.logic.resolvable.Concludable;
import grakn.core.logic.resolvable.Resolvable;
import grakn.core.logic.resolvable.Retrievable;
import grakn.core.pattern.Conjunction;
import grakn.core.pattern.Disjunction;
import grakn.core.rocks.RocksGrakn;
import grakn.core.rocks.RocksSession;
import grakn.core.rocks.RocksTransaction;
import grakn.core.test.integration.util.Util;
import graql.lang.Graql;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Set;

import static grakn.common.collection.Collections.list;
import static grakn.common.collection.Collections.set;
import static junit.framework.TestCase.assertEquals;
import static junit.framework.TestCase.assertTrue;

public class ResolverManagerTest {

    private static Path directory = Paths.get(System.getProperty("user.dir")).resolve("resolver-manager-test");
    private static String database = "resolver-manager-test";
    private static RocksGrakn grakn;
    private static RocksSession session;
    private static RocksTransaction rocksTransaction;
    private static ConceptManager conceptMgr;
    private static LogicManager logicMgr;

    @Before
    public void setUp() throws IOException {
        Util.resetDirectory(directory);
        grakn = RocksGrakn.open(directory);
        grakn.databases().create(database);
        session = grakn.session(database, Arguments.Session.Type.SCHEMA);
        rocksTransaction = session.transaction(Arguments.Transaction.Type.WRITE);
        conceptMgr = rocksTransaction.concepts();
        logicMgr = rocksTransaction.logic();
    }

    @After
    public void tearDown() {
        rocksTransaction.close();
        session.close();
        grakn.close();
    }

    private Conjunction parse(String query) {
        return Disjunction.create(Graql.parsePattern(query).asConjunction().normalise()).conjunctions().iterator().next();
    }

    @Test
    public void test_planner_retrievable_dependent_upon_concludable() {
        Concludable concludable = Concludable.create(parse("{ $a has $b; }")).iterator().next();
        Retrievable retrievable = new Retrievable(parse("{ $c($b); }"));

        Set<Resolvable> resolvables = set(concludable, retrievable);
        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();
        assertEquals(list(concludable, retrievable), plan);
    }

    @Test
    public void test_planner_prioritises_retrievable_without_dependencies() {
        Concludable concludable = Concludable.create(parse("{ $p has name $n; }")).iterator().next();
        Retrievable retrievable = new Retrievable(parse("{ $p isa person; }"));

        Set<Resolvable> resolvables = set(concludable, retrievable);

        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();
        assertEquals(list(retrievable, concludable), plan);
    }

    @Test
    public void test_planner_prioritises_largest_retrievable_without_dependencies() {
        Retrievable retrievable = new Retrievable(parse("{ $p isa person, has age $a, has first-name $fn, has surname $sn; }"));
        Concludable concludable = Concludable.create(parse("{ ($p, $c); }")).iterator().next();
        Retrievable retrievable2 = new Retrievable(parse("{ $c isa company, has name $cn; }"));

        Set<Resolvable> resolvables = set(retrievable, retrievable2, concludable);

        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();
        assertEquals(list(retrievable, concludable, retrievable2), plan);
    }

    @Test
    public void test_planner_starts_at_independent_concludable() {
        Concludable concludable = Concludable.create(parse("{ $r($a, $b); }")).iterator().next();
        Concludable concludable2 = Concludable.create(parse("{ $r has $c; }")).iterator().next();

        Set<Resolvable> resolvables = set(concludable, concludable2);

        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();
        assertEquals(list(concludable, concludable2), plan);
    }

    @Test
    public void test_planner_multiple_dependencies() {
        Retrievable retrievable = new Retrievable(parse("{ $p isa person; }"));
        Concludable concludable = Concludable.create(parse("{ $p has name $n; }")).iterator().next();
        Retrievable retrievable2 = new Retrievable(parse("{ $c isa company, has name $n; }"));
        Concludable concludable2 = Concludable.create(parse("{ $e($c, $p2) isa employment; }")).iterator().next();

        Set<Resolvable> resolvables = set(retrievable, retrievable2, concludable, concludable2);
        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();

        assertEquals(list(retrievable, concludable, retrievable2, concludable2), plan);
    }

    @Test
    public void test_planner_two_circular_has_dependencies() {
        Concludable concludable = Concludable.create(parse("{ $a has $b; }")).iterator().next();
        Concludable concludable2 = Concludable.create(parse("{ $b has $a; }")).iterator().next();

        Set<Resolvable> resolvables = set(concludable, concludable2);
        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();

        assertEquals(2, plan.size());
        assertEquals(set(concludable, concludable2), set(plan));
    }

    @Test
    public void test_planner_two_circular_relates_dependencies() {
        Concludable concludable = Concludable.create(parse("{ $a($b); }")).iterator().next();
        Concludable concludable2 = Concludable.create(parse("{ $b($a); }")).iterator().next();

        Set<Resolvable> resolvables = set(concludable, concludable2);
        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();

        assertEquals(2, plan.size());
        assertEquals(set(concludable, concludable2), set(plan));
    }

    @Test
    public void test_planner_disconnected_conjunction() {
        Concludable concludable = Concludable.create(parse("{ $a($b); }")).iterator().next();
        Concludable concludable2 = Concludable.create(parse("{ $c($d); }")).iterator().next();

        Set<Resolvable> resolvables = set(concludable, concludable2);
        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();

        assertEquals(2, plan.size());
        assertEquals(set(concludable, concludable2), set(plan));
    }

    @Test
    public void test_planner_prioritises_concludable_with_least_applicable_rules() {
        final EntityType person = conceptMgr.putEntityType("person");
        final RelationType friendship = conceptMgr.putRelationType("friendship");
        friendship.setRelates("friend");
        final RelationType marriage = conceptMgr.putRelationType("marriage");
        marriage.setRelates("spouse");
        person.setPlays(friendship.getRelates("friend"));
        person.setPlays(marriage.getRelates("spouse"));
        logicMgr.putRule(
                "marriage-is-friendship",
                Graql.parsePattern("{$x isa person; $y isa person; (spouse: $x, spouse: $y) isa marriage; }").asConjunction(),
                Graql.parseVariable("(friend: $x, friend: $y) isa friendship").asThing());
        rocksTransaction.commit();
        rocksTransaction = session.transaction(Arguments.Transaction.Type.WRITE);
        conceptMgr = rocksTransaction.concepts();
        logicMgr = rocksTransaction.logic();

        Concludable concludable = Concludable.create(parse("{ $b has $a; }")).iterator().next();
        Concludable concludable2 = Concludable.create(parse("{ $c($b) isa friendship; }")).iterator().next();

        Set<Resolvable> resolvables = set(concludable, concludable2);
        List<Resolvable> plan = new ResolverManager.Plan(resolvables, conceptMgr, logicMgr).plan();

        assertEquals(list(concludable, concludable2), plan);
    }
}
