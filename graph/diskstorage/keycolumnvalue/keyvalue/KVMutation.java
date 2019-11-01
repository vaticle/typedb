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

package grakn.core.graph.diskstorage.keycolumnvalue.keyvalue;

import com.google.common.base.Function;
import com.google.common.base.Functions;
import grakn.core.graph.diskstorage.Mutation;
import grakn.core.graph.diskstorage.StaticBuffer;
import grakn.core.graph.diskstorage.keycolumnvalue.keyvalue.KeyValueEntry;
import grakn.core.graph.diskstorage.keycolumnvalue.keyvalue.KeyValueStore;

import javax.annotation.Nullable;

/**
 * {@link Mutation} for {@link KeyValueStore}.
 */
public class KVMutation extends Mutation<KeyValueEntry, StaticBuffer> {

    public KVMutation() {
        super();
    }

    private static final Function<KeyValueEntry, StaticBuffer> ENTRY2KEY_FCT = new Function<KeyValueEntry, StaticBuffer>() {
        @Nullable
        @Override
        public StaticBuffer apply(@Nullable KeyValueEntry keyValueEntry) {
            return keyValueEntry.getKey();
        }
    };

    @Override
    public void consolidate() {
        super.consolidate(ENTRY2KEY_FCT, Functions.identity());
    }

    @Override
    public boolean isConsolidated() {
        return super.isConsolidated(ENTRY2KEY_FCT, Functions.identity());
    }

}
