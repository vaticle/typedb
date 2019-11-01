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

import grakn.core.graph.core.attribute.AttributeSerializer;
import grakn.core.graph.diskstorage.ScanBuffer;
import grakn.core.graph.diskstorage.WriteBuffer;
import grakn.core.graph.graphdb.database.serialize.attribute.IntegerSerializer;
import grakn.core.graph.graphdb.database.serialize.attribute.LongSerializer;

import java.time.Duration;


public class DurationSerializer implements AttributeSerializer<Duration> {

    private final LongSerializer secondsSerializer = new LongSerializer();
    private final IntegerSerializer nanosSerializer = new IntegerSerializer();

    @Override
    public Duration read(ScanBuffer buffer) {
        long seconds = secondsSerializer.read(buffer);
        long nanos = nanosSerializer.read(buffer);
        return Duration.ofSeconds(seconds, nanos);
    }

    @Override
    public void write(WriteBuffer buffer, Duration attribute) {
        secondsSerializer.write(buffer,attribute.getSeconds());
        nanosSerializer.write(buffer,attribute.getNano());
    }
}
