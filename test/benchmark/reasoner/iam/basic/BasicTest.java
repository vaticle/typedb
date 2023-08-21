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

package com.vaticle.typedb.core.reasoner.benchmark.iam.basic;

import com.vaticle.typedb.core.reasoner.benchmark.iam.common.Benchmark;
import com.vaticle.typedb.core.reasoner.benchmark.iam.common.BenchmarkRunner;
import com.vaticle.typedb.core.reasoner.benchmark.iam.common.QueryParams;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

public class BasicTest {
    static final Path RESOURCE_DIRECTORY = Paths.get("test", "benchmark", "reasoner", "iam", "basic");
    private static final Path COMMON_RESOURCE_DIR = Paths.get("test", "benchmark", "reasoner", "iam", "resources");

    private static final int NOBJECTS = 52;
    private static final int NACCESS = 656;
    private static final String database = "iam-benchmark-basic-test";
    private static final BenchmarkRunner benchmarker = new BenchmarkRunner(database);

    private final QueryParams queryParams;

    public BasicTest() {
        queryParams = QueryParams.load(COMMON_RESOURCE_DIR.resolve("params.yml"));
    }

    @BeforeClass
    public static void setup() throws IOException {
        benchmarker.setUp();
        benchmarker.loadDatabase(COMMON_RESOURCE_DIR.resolve("types.tql"), COMMON_RESOURCE_DIR.resolve("data.typedb"));
        benchmarker.loadSchema(RESOURCE_DIRECTORY.resolve("basic_test.tql"));
        benchmarker.warmUp();
    }

    @AfterClass
    public static void tearDown() {
        benchmarker.tearDown();
    }

    @After
    public void reset() {
        benchmarker.reset();
    }

    @Test
    public void testOwnership() {
        String query = "match\n" +
                "$x isa access, has id $a; ";
        Benchmark benchmark = new Benchmark("inferred-ownership", query, NACCESS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(500);
        benchmark.assertCounters(10, NACCESS, 2, 2, 3 * NACCESS);
    }

    @Test
    public void testRelationWithRolePlayers() {
        String query = "match\n" +
                "(start: $o, end: $x) isa object-pair;\n";
        Benchmark benchmark = new Benchmark("relation-with-rp", query, NOBJECTS * NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(1500);
        benchmark.assertCounters(10, NOBJECTS * NOBJECTS, 2, 2, 2 * NOBJECTS * (NOBJECTS+1));
    }

    @Test
    public void testRelationWithoutRolePlayer() {
        String query = "match\n" +
                "$r isa object-pair;\n";
        Benchmark benchmark = new Benchmark("relation-without-rp", query, NOBJECTS * NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(1500);
        benchmark.assertCounters(10, NOBJECTS * NOBJECTS, 2, 2, 2 * NOBJECTS * (NOBJECTS+1));
    }

    @Test
    public void testBoundRelation() {
        String query = String.format(
                "match\n" +
                        "$o isa object, has id \"%s\";\n" +
                        "(start: $o, end: $x) isa object-pair;\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("relation-bound", query, NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(200);
        benchmark.assertCounters(10, NOBJECTS, 2, 2, 2 * (NOBJECTS+1));
    }

    @Test
    public void testRelationUnpacking() {
        String query = String.format(
                "match\n" +
                        "$o1 isa object, has id \"%s\";\n" +
                        "$r1 (start: $o1, end: $x1) isa object-pair;\n" +
                        "$r1 is $r2;\n" +
                        "$r2 (start: $o2, end: $x2);\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("relation-unpacking", query, NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(200);
        benchmark.assertCounters(10, NOBJECTS, 2, NOBJECTS + 3, 314);
    }

    @Test
    public void testInferredRelationAndOwnership() {
        String query = "match\n" +
                "$r isa object-pair, has id $id;\n";
        Benchmark benchmark = new Benchmark("inferred-relation-inferred-ownership", query, NOBJECTS * NOBJECTS * 2 - NOBJECTS);
        benchmarker.runBenchmark(benchmark);
        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(4500);
        benchmark.assertCounters(25, NOBJECTS * NOBJECTS + (NOBJECTS * NOBJECTS * 2 - NOBJECTS), 3, 3, 24180);
    }

    // More complicated
    @Test
    public void testDoubleJoin() {
        String query = String.format(
                "match\n" +
                        "$a isa object, has id \"%s\";\n" +
                        "(start: $a, end: $b) isa object-pair;\n" +
                        "(start: $b, end: $c) isa object-pair;\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("double-join", query, NOBJECTS * NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(1500);
        benchmark.assertCounters(25, NOBJECTS * NOBJECTS, NOBJECTS, NOBJECTS + 3, 8217);
    }

    @Test
    public void testTripleJoinWithProjection() {
        String query = String.format(
                "match\n" +
                        "$a isa object, has id \"%s\";\n" +
                        "(start: $a, end: $b) isa object-pair;\n" +
                        "(start: $b, end: $c) isa object-pair;\n" +
                        "(start: $c, end: $d) isa object-pair;\n" +
                        "get $a, $d;\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("triple-join-with-projection", query, NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(1500);
        benchmark.assertCounters(25, NOBJECTS * NOBJECTS, NOBJECTS, NOBJECTS + NOBJECTS + 3, 151529);
    }

    @Test
    public void testSymmetricDoubleJoin() {
        String query = String.format(
                "match\n" +
                        "$a isa object, has id \"%s\";\n" +
                        "($a, $b) isa object-pair;\n" +
                        "($b, $c) isa object-pair;\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("double-join-symmetric", query, NOBJECTS * NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(1500);
        benchmark.assertCounters(25, NOBJECTS * NOBJECTS, 1 + NOBJECTS * 2, NOBJECTS * 2 + 3, 18929);
    }

    @Test
    public void testLoopBack() {
        String query = String.format("match\n" +
                        "$a isa object, has id \"%s\";\n" +
                        "(start: $a, end: $b) isa object-pair;\n" +
                        "(start: $b, end: $a) isa object-pair;\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("double-join-loop", query, NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(200);
        benchmark.assertCounters(25, NOBJECTS * 2 - 1, 2 + NOBJECTS, NOBJECTS + 3, 314);
    }

    @Test
    public void testFromMiddle() {
        String query = String.format("match\n" +
                        "$b isa object, has id \"%s\";\n" +
                        "(start: $a, end: $b) isa object-pair;\n" +
                        "(start: $b, end: $c) isa object-pair;\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("double-join-from-middle", query, NOBJECTS * NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(500);
        benchmark.assertCounters(50, NOBJECTS + NOBJECTS, 3, 3 + 2, 5567);
    }

    @Test
    public void testDoubleOutGoing() {
        String query = String.format(
                "match\n" +
                        "$a isa object, has id \"%s\";\n" +
                        "(start: $a, end: $b) isa object-pair;\n" +
                        "(start: $a, end: $c) isa object-pair;\n",
                queryParams.basicTestObject);
        Benchmark benchmark = new Benchmark("double-join-out-going", query, NOBJECTS * NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(500);
        benchmark.assertCounters(40, NOBJECTS, 2, 3 + 1, 5514);
    }

    @Test
    public void testQueryTwice() {
        String query = "match\n" +
                "(start: $a, end: $b) isa object-pair;\n" +
                "(start: $a, end: $b) isa object-pair;\n";
        Benchmark benchmark = new Benchmark("double-join-self", query, NOBJECTS * NOBJECTS);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(3500);
        benchmark.assertCounters(35, NOBJECTS * NOBJECTS, NOBJECTS * NOBJECTS + 2, NOBJECTS * NOBJECTS + 2, 13572);
    }
}
