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

package com.vaticle.typedb.core.reasoner.benchmark.iam.complex;

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

public class LanguageFeaturesTest {
    static final Path RESOURCE_DIRECTORY = Paths.get("test", "benchmark", "reasoner", "iam", "complex");
    private static final Path COMMON_RESOURCE_DIR = Paths.get("test", "benchmark", "reasoner", "iam", "resources");

    private static final String database = "iam-benchmark-language-features";
    private static final BenchmarkRunner benchmarker = new BenchmarkRunner(database);
    private final QueryParams queryParams;

    public LanguageFeaturesTest() {
        queryParams = QueryParams.load(COMMON_RESOURCE_DIR.resolve("params.yml"));
    }

    @BeforeClass
    public static void setup() throws IOException {
        benchmarker.setUp();
        benchmarker.loadDatabase(COMMON_RESOURCE_DIR.resolve("types.tql"), COMMON_RESOURCE_DIR.resolve("data.typedb"));
        benchmarker.loadSchema(COMMON_RESOURCE_DIR.resolve("rules.tql"));
        benchmarker.loadSchema(RESOURCE_DIRECTORY.resolve("language-features-test.tql"));
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
    public void testValuePredicateFiltering() {
        String query = String.format(
                "match\n" +
                        "$p isa person, has $email; $email = \"%s\";\n" +
                        "$f isa file, has $path; $path = \"%s\";\n" +
                        "$o isa operation, has $operation; $operation = \"%s\";\n" +
                        "$a (object: $f, action: $o) isa access;\n" +
                        "$pe (subject: $p, access: $a) isa permission, has validity true;\n",
                queryParams.permissionEmail, queryParams.permissionObject, queryParams.permissionAction);
        Benchmark benchmark = new Benchmark("value-predicate-filtering", query, 1);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(2500);
        benchmark.assertCounters(1000, 108, 79, 115, 300);
    }

    @Test
    public void variabilisedRules() {
        String query = String.format(
                "match\n" +
                        "$p isa person, has email \"%s\";\n" +
                        "(group: $g, member: $p) isa variabilised-group-membership;\n",
                queryParams.permissionEmail);
        Benchmark benchmark = new Benchmark("variabilised-rules", query, 3);
        benchmarker.runBenchmark(benchmark);

        benchmark.assertAnswerCountCorrect();
        benchmark.assertRunningTime(100);
        benchmark.assertCounters(200, 9, 29, 101, 105);
    }
}
