/*
 * GRAKN.AI - THE KNOWLEDGE GRAPH
 * Copyright (C) 2018 Grakn Labs Ltd
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
 */

package ai.grakn.engine.attribute.uniqueness.queue;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.LinkedBlockingQueue;

/**
 * TODO
 * @author Ganeshwara Herawan Hananda
 */
public class InMemoryQueue implements Queue {
    private java.util.Queue<Attribute> newAttributeQueue = new LinkedBlockingQueue<>();

    @Override
    public void insertAttribute(Attribute attribute) {
        newAttributeQueue.add(attribute);
    }

    @Override
    public Attributes readAttributes(int max) {
        List<Attribute> batch = new LinkedList<>();

        for (int i = 0; i < max && batch.size() < max; ++i) {
            Attribute e = newAttributeQueue.poll();
            if (e != null) batch.add(e);
        }

        return new Attributes(batch);
    }

    // TODO
    @Override
    public void ackAttributes(Attributes batch) {
    }
}
