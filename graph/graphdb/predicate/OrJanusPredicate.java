// Copyright 2017 JanusGraph Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package grakn.core.graph.graphdb.predicate;

import grakn.core.graph.graphdb.predicate.AndJanusPredicate;
import grakn.core.graph.graphdb.predicate.ConnectiveJanusPredicate;
import grakn.core.graph.graphdb.query.JanusGraphPredicate;

import java.util.List;

/**
 * @author David Clement (david.clement90@laposte.net)
 */
public class OrJanusPredicate extends ConnectiveJanusPredicate {

    private static final long serialVersionUID = 8069102813023214045L;

    public OrJanusPredicate(){
        super();
    }

    public OrJanusPredicate(List<JanusGraphPredicate> predicates) {
        super(predicates);
    }

    @Override
    ConnectiveJanusPredicate getNewNegateIntance() {
        return new AndJanusPredicate();
    }

    @Override
    boolean isOr() {
        return true;
    }

    @Override
    public boolean isQNF() {
        return ! this.stream().anyMatch(internalCondition -> internalCondition instanceof AndJanusPredicate || !internalCondition.isQNF());
    }
}
