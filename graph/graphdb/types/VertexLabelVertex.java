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

package grakn.core.graph.graphdb.types;

import grakn.core.graph.graphdb.internal.InternalVertexLabel;
import grakn.core.graph.graphdb.transaction.StandardJanusGraphTx;
import grakn.core.graph.graphdb.types.TypeDefinitionCategory;
import grakn.core.graph.graphdb.types.TypeUtil;
import grakn.core.graph.graphdb.types.vertices.JanusGraphSchemaVertex;


public class VertexLabelVertex extends JanusGraphSchemaVertex implements InternalVertexLabel {

    public VertexLabelVertex(StandardJanusGraphTx tx, long id, byte lifecycle) {
        super(tx, id, lifecycle);
    }

    @Override
    public boolean isPartitioned() {
        return getDefinition().getValue(TypeDefinitionCategory.PARTITIONED, Boolean.class);
    }

    @Override
    public boolean isStatic() {
        return getDefinition().getValue(TypeDefinitionCategory.STATIC, Boolean.class);
    }

    @Override
    public boolean hasDefaultConfiguration() {
        return !isPartitioned() && !isStatic();
    }

    private Integer ttl = null;

    @Override
    public int getTTL() {
        if (null == ttl) {
            ttl = TypeUtil.getTTL(this);
        }
        return ttl;
    }

}
