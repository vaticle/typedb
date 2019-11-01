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

package grakn.core.graph.core.schema;

import grakn.core.graph.core.Namifiable;
import grakn.core.graph.core.schema.JanusGraphIndex;
import grakn.core.graph.core.schema.JanusGraphSchemaType;
import grakn.core.graph.core.schema.RelationTypeIndex;

/**
 * Marks any element that is part of a JanusGraph Schema.
 * JanusGraph Schema elements can be uniquely identified by their name.
 * <p>
 * A JanusGraph Schema element is either a {@link JanusGraphSchemaType} or an index definition, i.e.
 * {@link JanusGraphIndex} or {@link RelationTypeIndex}.
 *
 */
public interface JanusGraphSchemaElement extends Namifiable {

}
