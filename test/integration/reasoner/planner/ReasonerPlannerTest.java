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

import com.vaticle.typedb.common.collection.Collections;
import com.vaticle.typedb.core.common.parameters.Arguments;
import com.vaticle.typedb.core.common.parameters.Options;
import com.vaticle.typedb.core.database.CoreDatabaseManager;
import com.vaticle.typedb.core.database.CoreSession;
import com.vaticle.typedb.core.database.CoreTransaction;
import com.vaticle.typedb.core.logic.LogicManager;
import com.vaticle.typedb.core.logic.Rule;
import com.vaticle.typedb.core.logic.resolvable.Resolvable;
import com.vaticle.typedb.core.logic.resolvable.ResolvableConjunction;
import com.vaticle.typedb.core.pattern.Conjunction;
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.pattern.variable.Variable;
import com.vaticle.typedb.core.reasoner.common.ReasonerPerfCounters;
import com.vaticle.typedb.core.test.integration.util.Util;
import com.vaticle.typeql.lang.TypeQL;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Set;

import static com.vaticle.typedb.common.collection.Collections.set;
import static com.vaticle.typedb.core.common.collection.Bytes.MB;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;
import static junit.framework.TestCase.assertEquals;

public class ReasonerPlannerTest {

    private static final Path dataDir = Paths.get(System.getProperty("user.dir")).resolve("reasoner-planner-test");
    private static final Path logDir = dataDir.resolve("logs");
    private static final Options.Database options = new Options.Database().dataDir(dataDir).reasonerDebuggerDir(logDir)
            .storageDataCacheSize(MB).storageIndexCacheSize(MB);
    private static final String database = "reasoner-planner-test";
    private static CoreDatabaseManager databaseMgr;
    private static CoreSession session;
    private static CoreTransaction transaction;

    @Before
    public void setUp() throws IOException {
        Util.resetDirectory(dataDir);
        databaseMgr = CoreDatabaseManager.open(options);
        databaseMgr.create(database);
        session = databaseMgr.session(database, Arguments.Session.Type.SCHEMA);
        transaction = session.transaction(Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "nid sub attribute, value long;\n" +
                "node sub entity, owns nid @key,\n" +
                "   plays edge:from, plays edge:to,\n" +
                "   plays path:from, plays path:to;\n" +
                "edge sub relation, relates from, relates to;\n" +
                "path sub relation, relates from, relates to;\n" +
                "\n" +
                "rule path-base:\n" +
                "when { (from: $n1, to: $n2) isa edge; }\n" +
                "then { (from: $n1, to: $n2) isa path; };\n" +
                "rule path-recursive:\n" +
                "when { (from: $n1, to: $n2) isa path; (from: $n2, to: $n3) isa edge; }\n" +
                "then { (from: $n1, to: $n3) isa path; };\n"));
        transaction.commit();
        session.close();

        session = databaseMgr.session(database, Arguments.Session.Type.DATA);
        transaction = session.transaction(Arguments.Transaction.Type.WRITE);
        transaction.query().insert(TypeQL.parseQuery("insert " +
                "$n1 isa node, has nid 1;" +
                "$n2 isa node, has nid 2;" +
                "   (from: $n1, to: $n2) isa edge;" +
                "$n3 isa node, has nid 3;" +
                "   (from: $n2, to: $n3) isa edge;" +
                "$n4 isa node, has nid 4;" +
                "   (from: $n3, to: $n4) isa edge;" +
                "$n5 isa node, has nid 5;" +
                "   (from: $n4, to: $n5) isa edge;"));
        transaction.commit();
        session.close();
        session = databaseMgr.session(database, Arguments.Session.Type.DATA);
    }

    @After
    public void tearDown() {
        if (transaction != null) transaction.close();
        session.close();
        databaseMgr.close();
    }

    private void initialise(Arguments.Session.Type schema, Arguments.Transaction.Type write) {
        if (transaction.isOpen()) transaction.close();
        if (session.isOpen()) session.close();
        session = databaseMgr.session(database, schema);
        transaction = session.transaction(write);
    }

    private void verifyPlan(ReasonerPlanner planner, String ruleLabel, Set<String> inputBounds, List<String> order) {
        Rule rule = transaction.logic().rules().filter(rule1 -> rule1.getLabel().equals(ruleLabel)).next();
        assert rule.condition().branches().size() == 1;
        ResolvableConjunction condition = iterate(rule.condition().branches()).next().conjunction();
        verifyPlan(planner, condition, inputBounds, order);
    }

    private void verifyPlan(ReasonerPlanner planner, ResolvableConjunction conjunction, Set<String> inputBounds, List<String> order) {
        Set<Variable> bounds = iterate(conjunction.pattern().variables())
                .filter(variable -> variable.id().isName())
                .filter(variable -> inputBounds.contains(variable.id().asName().name()))
                .toSet();
        assertEquals(bounds.size(), inputBounds.size());
        List<Resolvable<?>> plan = planner.getPlan(new ReasonerPlanner.CallMode(conjunction, bounds)).plan();
        assertEquals(order.size(), plan.size());
        for (int i = 0; i < order.size(); i++) {
            assertEquals(plan.get(i).isConcludable() ? "c" : "r", order.get(i));
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

    @Test
    public void test_directed_transitivity() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "nid sub attribute, value long;\n" +
                "node sub entity, owns nid @key,\n" +
                "   plays edge:from, plays edge:to,\n" +
                "   plays path:from, plays path:to;\n" +
                "edge sub relation, relates from, relates to;\n" +
                "path sub relation, relates from, relates to;\n" +
                "\n" +
                "rule path-base:\n" +
                "when { (from: $n1, to: $n2) isa edge; }\n" +
                "then { (from: $n1, to: $n2) isa path; };\n" +
                "rule path-recursive:\n" +
                "when { (from: $n1, to: $n2) isa path; (from: $n2, to: $n3) isa edge; }\n" +
                "then { (from: $n1, to: $n3) isa path; };\n"));
        transaction.commit();
        transaction.close();
        session.close();

        {
            initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
            ReasonerPlanner planner = ReasonerPlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ (from: $x, to: $y) isa path; }", transaction.logic()));
            planner.planRoot(conjunction);
            verifyPlan(planner, conjunction, set(), Collections.list("c"));
            verifyPlan(planner, "path-recursive", set(), Collections.list("c", "r"));
        }

        {
            initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
            ReasonerPlanner planner = ReasonerPlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $x isa node, has nid 0; (from: $x, to: $y) isa path; }", transaction.logic()));
            planner.planRoot(conjunction);
            verifyPlan(planner, conjunction, set(), Collections.list("r", "c"));
            verifyPlan(planner, "path-recursive", set("n1"), Collections.list("c", "r"));
        }

        {
            initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
            ReasonerPlanner planner = ReasonerPlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $y isa node, has nid 0; (from: $x, to: $y) isa path; }", transaction.logic()));
            planner.planRoot(conjunction);
            verifyPlan(planner, conjunction, set(), Collections.list("r", "c"));
            verifyPlan(planner, "path-recursive", set("n3"), Collections.list("r", "c"));
        }

        {
            initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
            ReasonerPlanner planner = ReasonerPlanner.create(transaction.traversal(), transaction.concepts(), transaction.logic(), new ReasonerPerfCounters(false), false);
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $x isa node, has nid 0; $y isa node, has nid 1; (from: $x, to: $y) isa path; }", transaction.logic()));
            planner.planRoot(conjunction);
            verifyPlan(planner, conjunction, set(), Collections.list("r", "r", "c"));
            verifyPlan(planner, "path-recursive", set("n1", "n3"), Collections.list("c", "r"));
        }
    }
}
