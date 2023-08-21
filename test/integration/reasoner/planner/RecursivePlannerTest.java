/*
 * Copyright (C) 2022 Vaticle
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
 *
 */

package com.vaticle.typedb.core.reasoner.planner;

import com.vaticle.typedb.core.common.parameters.Arguments;
import com.vaticle.typedb.core.common.parameters.Options;
import com.vaticle.typedb.core.database.CoreDatabaseManager;
import com.vaticle.typedb.core.database.CoreSession;
import com.vaticle.typedb.core.database.CoreTransaction;
import com.vaticle.typedb.core.logic.LogicManager;
import com.vaticle.typedb.core.logic.resolvable.ResolvableConjunction;
import com.vaticle.typedb.core.pattern.Conjunction;
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.reasoner.common.ReasonerPerfCounters;
import com.vaticle.typedb.core.test.integration.util.Util;
import com.vaticle.typeql.lang.TypeQL;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

import static com.vaticle.typedb.common.collection.Collections.set;
import static com.vaticle.typedb.core.common.collection.Bytes.MB;
import static junit.framework.TestCase.assertEquals;
import static junit.framework.TestCase.assertTrue;

public class RecursivePlannerTest {

    private static final Path dataDir = Paths.get(System.getProperty("user.dir")).resolve("recursive-por-planner-test");
    private static final Path logDir = dataDir.resolve("logs");
    private static final Options.Database options = new Options.Database().dataDir(dataDir).reasonerDebuggerDir(logDir)
            .storageDataCacheSize(MB).storageIndexCacheSize(MB);
    private static final String database = "recursive-por-planner-test";
    private static CoreDatabaseManager databaseMgr;
    private static CoreSession session;
    private static CoreTransaction transaction;

    @Before
    public void setUp() throws IOException {
        Util.resetDirectory(dataDir);
        databaseMgr = CoreDatabaseManager.open(options);
        databaseMgr.create(database);
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);

        transaction.query().define(TypeQL.parseQuery("define " +
                "person sub entity, owns first-name, owns last-name," +
                "   plays friendship:friendor, plays friendship:friendee;" +
                "man sub person;" +
                "name sub attribute, abstract, value string;" +
                "first-name sub name;" +
                "last-name sub name;" +
                "household sub relation, relates member;" +
                "person plays household:member;" +
                "friendship sub relation, relates friendor, relates friendee;"));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.WRITE);
        transaction.query().insert(TypeQL.parseQuery("insert " +
                "$p1 isa person, has first-name \"p1_f\", has last-name \"p1_l\";" +
                "$p2 isa person;" +
                "$p3 isa person;" +
                "$m1 isa man, has first-name \"m1_f\", has last-name \"m1_l\";" +
                "$m2 isa man, has first-name \"m2_f\";" +

                "(member: $p1, member: $p2, member: $p3) isa household;" +
                "(member: $m1) isa household;" +

                "(friendor: $p1, friendee: $p2) isa friendship;" +
                "(friendor: $p2, friendee: $p3) isa friendship;" +
                "(friendor: $m1, friendee: $m2) isa friendship;"));
        transaction.commit();
    }

    private void initialise(Arguments.Session.Type schema, Arguments.Transaction.Type write) {
        session = databaseMgr.session(database, schema);
        transaction = session.transaction(write);
    }

    @After
    public void tearDown() {
        transaction.close();
        session.close();
        databaseMgr.close();
    }

    @Test
    public void test_single_retrieval() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        RecursivePlanner planner = RecursivePlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
        ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa person; }", transaction.logic()));
        planner.planRoot(conjunction);
        ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
        assertEquals(10.0, plan.allCallsCost()); // For now the retrieval cost is just the answer-count
    }

    @Test
    public void test_owns_retrieval() {
        // Still just answer counts. Improve if we have an improved estimate for retrievables
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);

        RecursivePlanner planner = RecursivePlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
        {   // Query only count of $p, where $p isa man;
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa man, has name $n; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(6.0, plan.allCallsCost());
        }

        {   // Query count of both variables $p and $n, where $p isa! person
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa! person, has name $n; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(4.0, plan.allCallsCost());
        }

        {   // Query count of both variables $p and $n, where $p isa person (and subtypes)
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa person, has name $n; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(10.0, plan.allCallsCost());
        }
    }

    @Test
    public void test_with_concludable_and_retrievable() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "rule everyone-is-named-dave: " +
                "when { $x isa person; } " +
                "then { $x has first-name \"Dave\"; };"));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        RecursivePlanner planner = RecursivePlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has name $n; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(30.0, plan.allCallsCost());
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has name $n; (friendor: $p, friendee: $f) isa friendship; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(24.0, plan.allCallsCost());
        }
    }

    @Test
    public void test_cycles() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "transitive-friendship sub relation, relates friendor, relates friendee;" +
                "person plays transitive-friendship:friendor, plays transitive-friendship:friendee;" +

                "rule friendship-is-transitive-1: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f1, friendee: $f2) isa transitive-friendship; };" +

                "rule friendship-is-transitive-2: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; (friendor: $f2, friendee: $f3) isa transitive-friendship;  } " +
                "then { (friendor: $f1, friendee: $f3) isa transitive-friendship; };" +
                ""));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        RecursivePlanner planner = RecursivePlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(98.0, plan.allCallsCost());
        }
    }

    @Test
    public void test_cycles_same_type_transitive() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "rule friendship-itself-is-transitive: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; (friendor: $f2, friendee: $f3) isa friendship;  } " +
                "then { (friendor: $f1, friendee: $f3) isa friendship; };"));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        RecursivePlanner planner = RecursivePlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(friendor: $x, friendee: $y) isa friendship; }", transaction.logic()));

            planner.planRoot(conjunction);

            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(429.0, plan.allCallsCost());
        }
    }

    @Test
    public void test_nested_cycles() {
        // the example may not make sense.
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "transitive-friendship sub relation, relates friendor, relates friendee;" +
                "person plays transitive-friendship:friendor, plays transitive-friendship:friendee;" +

                "rule friendship-is-transitive-1: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f1, friendee: $f2) isa transitive-friendship; };" +

                "rule friendship-is-transitive-2: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; (friendor: $f2, friendee: $f3) isa transitive-friendship;  } " +
                "then { (friendor: $f1, friendee: $f3) isa transitive-friendship; };"));

        transaction.query().define(TypeQL.parseQuery("define " +
                "can-live-with sub relation, relates guest, relates host;" +
                "person plays can-live-with:guest, plays can-live-with:host;" +

                "rule clw-if-housemates: " +
                "when { (member: $f1, member: $f2) isa household ; } " +
                "then { (guest: $f1, host: $f2) isa can-live-with; };" +

                "rule clw-if-housemate-friends-with: " +
                "when { (guest: $f1, host: $f2) isa can-live-with; (friendor: $f2, friendee: $f3) isa transitive-friendship;  } " +
                "then { (guest: $f1, host: $f3) isa can-live-with; };"));

        transaction.query().define(TypeQL.parseQuery("define " +
                "rule clw-means-friends: " +
                "when { (guest: $f1, host: $f2) isa can-live-with; } " +
                "then { (friendor: $f1, friendee: $f2) isa transitive-friendship; };"));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        RecursivePlanner planner = RecursivePlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertTrue(plan.allCallsCost() > 0); // TODO: Verify whether this is the right/sensible answer
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(guest: $x, host: $y) isa can-live-with; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertTrue(plan.allCallsCost() > 0); // TODO: Verify whether this is the right/sensible answer
        }
    }

    @Test
    public void test_bound_cycles() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "transitive-friendship sub relation, relates friendor, relates friendee;" +
                "person plays transitive-friendship:friendor, plays transitive-friendship:friendee;" +

                "rule friendship-is-transitive-1: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " + // 3
                "then { (friendor: $f1, friendee: $f2) isa transitive-friendship; };" +

                "rule friendship-is-transitive-2: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; (friendor: $f2, friendee: $f3) isa transitive-friendship;  } " + // 3 + 3/6 * 36 = 21
                "then { (friendor: $f1, friendee: $f3) isa transitive-friendship; };" +
                ""));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        RecursivePlanner planner = RecursivePlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{$x has name \"Jim\"; (friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(32.0, plan.allCallsCost());
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{$y has name \"Jim\"; (friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));
            planner.planRoot(conjunction);
            ReasonerPlanner.Plan plan = planner.getPlan(conjunction, set());
            assertEquals(22.0, plan.allCallsCost());
        }
    }

    private static Conjunction resolvedConjunction(String query, LogicManager logicMgr) {
        Disjunction disjunction = resolvedDisjunction(query, logicMgr);
        assert disjunction.conjunctions().size() == 1;
        return disjunction.conjunctions().get(0);
    }

    private static Disjunction resolvedDisjunction(String query, LogicManager logicMgr) {
        Disjunction disjunction = Disjunction.create(TypeQL.parsePattern(query).asConjunction().normalise());
        logicMgr.typeInference().applyCombination(disjunction);
        return disjunction;
    }
}
