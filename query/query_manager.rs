/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use function::function::Function;

struct QueryManager {}

impl QueryManager {
    fn execute(&self, query: &str) {
        // 1. parse query into list of TypeQL clauses
        // 2. expand implicit clauses, eg. fetch clause; -> filter clause; fetch clause;
        // 3. parse query-bound functions
        // 4. generate list of executors
        // 5. Execute each executor
    }

    // TODO: take in parsed TypeQL clause
    fn create_executor(&self, clause: &str) {
        // match clause
    }

    fn create_match_executor(&self, query_functions: Vec<Function>) {
        // let conjunction = Conjunction::new();
        // ... build conjunction...
    }
}

enum Executor {
    Match,
    Insert,
    Delete,
    Put,
    Fetch,
    Assert,
    Filter,
    Sort,
    Offset,
    Limit,
}

trait PipelineStage {}

enum QueryReturn {
    MapStream,
    JSONStream,
    Aggregate,
}
