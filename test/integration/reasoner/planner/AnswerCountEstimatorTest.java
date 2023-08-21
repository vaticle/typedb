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
import com.vaticle.typedb.core.common.parameters.Options.Database;
import com.vaticle.typedb.core.database.CoreDatabaseManager;
import com.vaticle.typedb.core.database.CoreSession;
import com.vaticle.typedb.core.database.CoreTransaction;
import com.vaticle.typedb.core.logic.LogicManager;
import com.vaticle.typedb.core.logic.resolvable.Resolvable;
import com.vaticle.typedb.core.logic.resolvable.ResolvableConjunction;
import com.vaticle.typedb.core.pattern.Conjunction;
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.pattern.variable.Variable;
import com.vaticle.typedb.core.test.integration.util.Util;
import com.vaticle.typedb.core.traversal.common.Identifier;
import com.vaticle.typeql.lang.TypeQL;
import com.vaticle.typeql.lang.pattern.variable.Reference;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Set;
import java.util.stream.Collectors;

import static com.vaticle.typedb.common.collection.Collections.set;
import static com.vaticle.typedb.core.common.collection.Bytes.MB;
import static junit.framework.TestCase.assertEquals;

public class AnswerCountEstimatorTest {

    private static final Path dataDir = Paths.get(System.getProperty("user.dir")).resolve("answer-count-estimator-test");
    private static final Path logDir = dataDir.resolve("logs");
    private static final Database options = new Database().dataDir(dataDir).reasonerDebuggerDir(logDir)
            .storageDataCacheSize(MB).storageIndexCacheSize(MB);
    private static final String database = "answer-count-estimator-test";
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
    public void test_type_based_estimate_with_subtypes() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);

        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa person; }", transaction.logic()));

        double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p")));
        assertEquals(5.0, answers);
    }

    @Test
    public void test_type_based_estimate_direct_type() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);

        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa! person; }", transaction.logic()));

        double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p")));
        assertEquals(3.0, answers);
    }

    @Test
    public void test_owns_based_estimate() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);

        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {   // Query only count of $p, where $p isa man;
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $m isa man, has name $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("m")));
            assertEquals(2.0, answers);
        }

        {   // Query only count of $p and $n, where $p isa man
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $m isa man, has name $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("m", "n")));
            assertEquals(3.0, answers);
        }

        {   // Query count of both variables $p and $n, where $p isa! person
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa! person, has name $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p", "n")));
            assertEquals(2.0, answers);
        }

        {   // Query count of both variables $p and $n, where $p isa person (and subtypes)
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa person, has name $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p", "n")));
            assertEquals(5.0, answers);
        }

        {   // Value constraint
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa person, has name $n; $n \"Steve\"; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("n")));
            assertEquals(1.0, answers);
        }

        {   // Value constraint
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p isa person, has name $n; $n \"Steve\"; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p", "n")));
            assertEquals(1.0, answers);
        }
    }

    @Test
    public void test_owns_based_estimate_two_concludables() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);

        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $m isa man, has name $n; $p isa! person, has $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("n")));
            assertEquals(2.0, answers);
        }

        {   // Restrict types
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $m isa man, has  first-name $n; $p isa! person, has $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("n")));
            assertEquals(1.0, answers);
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $m isa man, has name $n; $p isa! person, has $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("m", "p")));
            assertEquals(2.0, answers);
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $m isa man, has first-name $n; $p isa! person, has $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("m", "p")));
            assertEquals(1.0, answers);
        }
    }

    @Test
    public void test_roles_based_estimate() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);

        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {   // Query a single role-player
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ ($p1) isa household; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p1")));
            assertEquals(4.0, answers);
        }

        {   // Two role-players, projected to one
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ ($p1, $p2) isa household; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p1")));
            assertEquals(4.0, answers);
        }

        {   // Just the relation
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $r isa household; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("r")));
            assertEquals(2.0, answers);
        }

        {   // Project to just the relation
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $r ($p1, $p2) isa household; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("r")));
            assertEquals(2.0, answers);
        }

        {   // Relation and one role-player, binary constraints are considered.
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $r ($p1) isa household; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("r", "p1")));
            assertEquals(4.0, answers);
        }

        {   // Two role-players
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ ($p1, $p2) isa household; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p1", "p2")));
            assertEquals(4.0, answers);
        }

        {   // Two role-players and relation
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $r ($p1, $p2) isa household; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p1", "p2")));
            assertEquals(4.0, answers);
        }
    }

    @Test
    public void test_inferred_explicit_has() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "rule everyone-is-named-dave: " +
                "when { $x isa person; } " +
                "then { $x has first-name \"Dave\"; };"));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {   // The explicit has should add one to the estimate of $n
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has name $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("n")));
            assertEquals(6.0, answers);
        }

        {   // The explicit has should add 5 has-edges (one per person)
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has name $n; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p", "n")));
            assertEquals(10.0, answers);
        }

        {   // Value constraint, unifies with rule
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has name $n; $n \"Dave\"; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("n")));
            assertEquals(1.0, answers);
        }

        {   // Value constraint, unifies with rule
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has name $n; $n \"Dave\"; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p", "n")));
            assertEquals(10.0/6.0, answers, 0.01);
        }

        {   // Value constraint, doesn't unify with rule
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has name $n; $n \"Steve\"; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p", "n")));
            assertEquals(1.0, answers);
        }
    }

    @Test
    public void test_inferred_relation() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "symmetric-friendship sub relation, relates friendor, relates friendee;" +
                "person plays symmetric-friendship:friendor, plays symmetric-friendship:friendee;" +
                "rule friendship-is-symmetric-1: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f1, friendee: $f2) isa symmetric-friendship; };" +
                "rule friendship-is-symmetric-2: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f2, friendee: $f1) isa symmetric-friendship; };"));
        transaction.query().define(TypeQL.parseQuery("define " +
                "jealous sub relation, relates who, relates whom;" +
                "person plays jealous:who, plays jealous:whom;" +
                "rule everyone-is-jealous-of-everyone: " +
                "when { $p1 isa person; $p2 isa person; } " +
                "then { (who: $p1, whom: $p2) isa jealous; };"));

        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $f isa symmetric-friendship; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("f")));
            assertEquals(6.0, answers);
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $j isa jealous; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("j")));
            assertEquals(25.0, answers);
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ (who:$x, whom:$y) isa jealous; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y")));
            assertEquals(25.0, answers);
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ (who:$x, whom:$y) isa jealous; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x")));
            assertEquals(5.0, answers); // The type of x must dominate.
        }

        {   // Is not inferred.
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ " +
                    "(friendor: $x, friendee: $y) isa friendship;" +
                    "(friendor: $y, friendee: $z) isa friendship; " +
                    "}", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "z")));
            assertEquals(3.0, answers);
        }

        {   // Will work with only the relation-roleplayer and no sibling roleplayer co-constraints
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ " +
                    "(friendor: $x, friendee: $y) isa symmetric-friendship;" +
                    "(friendor: $y, friendee: $z) isa symmetric-friendship; " +
                    "}", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "z")));
            assertEquals(36.0/5.0, answers,0.01);
        }

        {   // Requires sibling roleplayer co-constraints
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ " +
                    "(friendor: $x, friendee: $y) isa symmetric-friendship;" +
                    "(friendor: $y, friendee: $z) isa symmetric-friendship; " +
                    "}", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y", "z")));
            assertEquals(36.0/5.0, answers,0.01);
        }
    }

    @Test
    public void test_inferred_relation_projection() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "one-hop-friends sub relation, relates first, relates second, relates third;" +
                "person plays one-hop-friends:first, plays one-hop-friends:second, plays one-hop-friends:third;" +
                "rule all-ternary: " +
                "when { (friendor: $p1, friendee: $p2) isa friendship; (friendor: $p2, friendee: $p3) isa friendship; } " +
                "then { (first: $p1, second: $p2, third: $p3) isa one-hop-friends; };"));

        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(first: $p1, second: $p2, third: $p3) isa one-hop-friends; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p1", "p2", "p3")));
            assertEquals(3.0, answers);
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ (first: $p1) isa one-hop-friends; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p1")));
            assertEquals(3.0, answers);
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ (first: $p1, second: $p2, third: $p3) isa one-hop-friends; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p1")));
            assertEquals(3.0, answers);
        }
    }

    @Test
    public void test_included_resolvables() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "symmetric-friendship sub relation, relates friendor, relates friendee;" +
                "person plays symmetric-friendship:friendor, plays symmetric-friendship:friendee;" +
                "rule friendship-is-symmetric-1: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f1, friendee: $f2) isa symmetric-friendship; };" +
                "rule friendship-is-symmetric-2: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f2, friendee: $f1) isa symmetric-friendship; };"));
        transaction.query().define(TypeQL.parseQuery("define " +
                "jealous sub relation, relates who, relates whom;" +
                "person plays jealous:who, plays jealous:whom;" +
                "rule everyone-is-jealous-of-everyone: " +
                "when { $p1 isa person; $p2 isa person; } " +
                "then { (who: $p1, whom: $p2) isa jealous; };"));

        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {   // Total answers
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $f (friendor: $p1, friendee: $p2) isa friendship; $j (who: $p1, whom: $p2) isa jealous;  }", transaction.logic()));

            Set<Resolvable<?>> resolvables = transaction.logic().compile(conjunction);
            AnswerCountEstimator.IncrementalEstimator incrementalEstimator = answerCountEstimator.createIncrementalEstimator(conjunction);
            resolvables.forEach(incrementalEstimator::extend);
            double answers = incrementalEstimator.answerEstimate(getVariablesByName(conjunction.pattern(), set("p1", "p2")));
            assertEquals(3.0, answers);
        }

        {   // With just jealous
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $f (friendor: $p1, friendee: $p2) isa friendship; $j (who: $p1, whom: $p2) isa jealous;  }", transaction.logic()));

            Set<Resolvable<?>> resolvables = transaction.logic().compile(conjunction);
            Set<Resolvable<?>> justJealous = resolvables.stream().filter(Resolvable::isConcludable).collect(Collectors.toSet());
            AnswerCountEstimator.IncrementalEstimator incrementalEstimator = answerCountEstimator.createIncrementalEstimator(conjunction);
            justJealous.forEach(incrementalEstimator::extend);
            double answers = incrementalEstimator.answerEstimate(getVariablesByName(conjunction.pattern(), set("p1", "p2")));
            assertEquals(25.0, answers);
        }
    }

    @Test
    public void test_negations() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {   // bringing a friend to your friends party is awkward if they arent friends with the host
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{" +
                    " (friendor: $host, friendee: $you) isa friendship;" +
                    " (friendor: $you, friendee: $guest) isa friendship; " +
                    " not{ (friendor: $host, friendee: $guest) isa friendship;}; " +
                    "}", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("host", "guest")));

            assertEquals(3.0, answers); // We assume all of them succeed?
        }
    }

    @Test
    public void test_inferred_has_on_inferred_relation() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "symmetric-friendship sub relation, relates friendor, relates friendee;" +
                "person plays symmetric-friendship:friendor, plays symmetric-friendship:friendee;" +
                "rule friendship-is-symmetric-1: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f1, friendee: $f2) isa symmetric-friendship; };" +
                "rule friendship-is-symmetric-2: " +
                "when { (friendor: $f1, friendee: $f2) isa friendship; } " +
                "then { (friendor: $f2, friendee: $f1) isa symmetric-friendship; };"));
        transaction.query().define(TypeQL.parseQuery("define " +
                "is-inferred sub attribute, value boolean;" +
                "symmetric-friendship owns is-inferred;" +
                "rule symmetric-frienship-are-inferred: " +
                "when { $f isa symmetric-friendship; } " +
                "then { $f has is-inferred true; };"));

        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $f has is-inferred $a; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("f")));
            assertEquals(6.0, answers);
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
                "then { (friendor: $f1, friendee: $f3) isa transitive-friendship; };"));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y")));
            assertEquals(18.0, answers);
            // 18 = 3 + 3 * 5  =  3 from rule-1 (coplayer) +  3 * 5  ($f1.unary(rp) * $f2.unary(type))  from rule-2
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x")));
            assertEquals(5.0, answers); // person type dominates actual transitive relations
        }

        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("y")));
            assertEquals(5.0, answers);
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
        {
            AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{$r (friendor: $x, friendee: $y) isa friendship; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y")));
            assertEquals(25.0, answers);
            // 25 = 5 * 5 = $x-unary(type) from ; $y-unary(type);   The multivar estimates aren't used because they are 3 + 25

            double answers1 = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("r", "x", "y")));
            assertEquals(25.0, answers1); // Still exceeds the types.

            double answers2 = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("r")));
            assertEquals(25.0, answers2);
        }
        transaction.close();

        // Add a friendship and verify the upper bound kicks in.
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.WRITE);
        transaction.query().insert(TypeQL.parseQuery("insert " +
                "$p5 isa person, has first-name \"p5_f\";\n" +
                "$p6 isa person, has first-name \"p6_f\";\n" +
                "(friendor: $p5, friendee: $p6) isa friendship;"));
        transaction.commit();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        {
            AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{$r (friendor: $x, friendee: $y) isa friendship; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y")));
            assertEquals(42.0, answers);
            //  = 4 + 6 * sqrt(6) ; from persisted + inferred-upper-bounded

            double answers1 = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("r", "x", "y")));
            assertEquals(42.0, answers1);

            double answers2 = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("r")));
            assertEquals(42.0, answers2);
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
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(friendor: $x, friendee: $y) isa transitive-friendship; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y")));
             assertEquals(25.0, answers);  // Costs are dominated by types. This test mainly tests the ability to handle nested loops
        }
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{(guest: $x, host: $y) isa can-live-with; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y")));
            assertEquals(25.0, answers);  // Costs are dominated by types. This test mainly tests the ability to handle nested loops
        }
    }

    @Test
    public void test_chain_3() {
        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{" +
                    "$x isa person, has first-name $xf;" +
                    "(friendor: $x, friendee: $y) isa friendship;" +
                    "$y isa person, has last-name $yl;" +
                    "}", transaction.logic()));
            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x")));
            assertEquals(2.0, answers);

            double answers1 = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("y")));
            assertEquals(2.0, answers1);

            double answers2 = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("x", "y")));
            assertEquals(2.0, answers2);
        }
    }

    @Test
    public void test_bounds_from_callee() {
        initialise(Arguments.Session.Type.SCHEMA, Arguments.Transaction.Type.WRITE);
        transaction.query().define(TypeQL.parseQuery("define " +
                "nick-name sub attribute, value string;" +
                "person owns nick-name;" +
                "rule bound-name-in-rule: " +
                "when { $x isa person, has name $n; $n \"Steven\"; } " +
                "then { $x has nick-name \"Steve\"; };"));
        transaction.commit();
        session.close();

        initialise(Arguments.Session.Type.DATA, Arguments.Transaction.Type.READ);
        AnswerCountEstimator answerCountEstimator = new AnswerCountEstimator(transaction.logic(), transaction.traversal().graph(), new ConjunctionGraph(transaction.logic()));
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has nick-name $n; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("n")));
            assertEquals(1.0, answers);

            double answers1 = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("p")));
            assertEquals(1.0, answers1);
        }
        {
            ResolvableConjunction conjunction = ResolvableConjunction.of(resolvedConjunction("{ $p has nick-name $n; (friendor: $p, friendee: $q) isa friendship; }", transaction.logic()));

            double answers = answerCountEstimator.estimateAnswers(conjunction, getVariablesByName(conjunction.pattern(), set("n")));
            assertEquals(1.0, answers);
        }
    }

    // TODO: Add tests with two rules inferring same relation but w/ different number of role-players
    // TODO: Add test with non-tree pattern to check propagation time.

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

    private Set<Variable> getVariablesByName(Conjunction conjunctionPattern, Set<String> names) {
        return names.stream()
                .map(name -> conjunctionPattern.variable(Identifier.Variable.of(Reference.concept(name))))
                .collect(Collectors.toSet());
    }
}
