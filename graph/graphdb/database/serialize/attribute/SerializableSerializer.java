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

package grakn.core.graph.graphdb.database.serialize.attribute;

import org.apache.commons.lang3.SerializationUtils;
import grakn.core.graph.core.attribute.AttributeSerializer;
import grakn.core.graph.diskstorage.ScanBuffer;
import grakn.core.graph.diskstorage.WriteBuffer;
import grakn.core.graph.graphdb.database.serialize.DataOutput;
import grakn.core.graph.graphdb.database.serialize.Serializer;
import grakn.core.graph.graphdb.database.serialize.SerializerInjected;

import java.io.Serializable;

/**
 * Serializes {@link Serializable} objects.
 * @param <T> Serializable type
 */
public class SerializableSerializer<T extends Serializable> implements AttributeSerializer<T>, SerializerInjected {

    private Serializer serializer;

    @Override
    public T read(ScanBuffer buffer) {
        byte[] data = serializer.readObjectNotNull(buffer,byte[].class);
        return (T) SerializationUtils.deserialize(data);
    }

    @Override
    public void write(WriteBuffer buffer, T attribute) {
        DataOutput out = (DataOutput) buffer;
        out.writeObjectNotNull(SerializationUtils.serialize(attribute));
    }

    @Override
    public void setSerializer(Serializer serializer) {
        this.serializer = serializer;
    }

}
