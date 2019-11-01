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

package grakn.core.graph.graphdb.query.condition;

import grakn.core.graph.core.JanusGraphElement;
import grakn.core.graph.graphdb.query.condition.Condition;
import grakn.core.graph.graphdb.query.condition.MultiCondition;

/**
 * Combines multiple conditions under semantic OR, i.e. at least one condition must be true for this combination to be true
 *
 */

public class Or<E extends JanusGraphElement> extends MultiCondition<E> {

    public Or(Condition<E>... elements) {
        super(elements);
    }

    public Or(int size) {
        super(size);
    }

    public Or() {
        super();
    }

    @Override
    public org.janusgraph.graphdb.query.condition.Or<E> clone() {
        return new org.janusgraph.graphdb.query.condition.Or<>(this);
    }

    @Override
    public Type getType() {
        return Type.OR;
    }

    @Override
    public boolean evaluate(E element) {
        if (!hasChildren())
            return true;

        for (Condition<E> condition : this) {
            if (condition.evaluate(element))
                return true;
        }

        return false;
    }

    public static <E extends JanusGraphElement> org.janusgraph.graphdb.query.condition.Or<E> of(Condition<E>... elements) {
        return new org.janusgraph.graphdb.query.condition.Or<>(elements);
    }

}
