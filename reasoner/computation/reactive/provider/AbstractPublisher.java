/*
 * Copyright (C) 2021 Vaticle
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

package com.vaticle.typedb.core.reasoner.computation.reactive.provider;

import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.reasoner.computation.actor.Processor.TerminationTracker;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.BufferedStream;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.DeduplicationStream;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.FindFirstStream;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.FlatMapStream;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.MapStream;

import java.util.function.Function;

public abstract class AbstractPublisher<OUTPUT> implements Reactive.Provider.Publisher<OUTPUT> {

    private final TerminationTracker monitor;
    private final String groupName;

    protected AbstractPublisher(TerminationTracker monitor, String groupName) {
        this.monitor = monitor;
        this.groupName = groupName;
    }

    protected abstract ReceiverRegistry<OUTPUT> receiverRegistry();

    protected TerminationTracker monitor() {
        return monitor;
    }

    @Override
    public String groupName() {
        return groupName;
    }

    @Override
    public Stream<OUTPUT,OUTPUT> findFirst() {
        FindFirstStream<OUTPUT> findFirst = new FindFirstStream<>(this, monitor, groupName());
        publishTo(findFirst);
        return findFirst;
    }

    @Override
    public <R> Stream<OUTPUT, R> map(Function<OUTPUT, R> function) {
        MapStream<OUTPUT, R> map = new MapStream<>(this, function, monitor(), groupName());
        publishTo(map);
        return map;
    }

    @Override
    public <R> Stream<OUTPUT,R> flatMapOrRetry(Function<OUTPUT, FunctionalIterator<R>> function) {
        FlatMapStream<OUTPUT, R> flatMap = new FlatMapStream<>(this, function, monitor(), groupName());
        publishTo(flatMap);
        return flatMap;
    }

    @Override
    public Stream<OUTPUT, OUTPUT> buffer() {
        BufferedStream<OUTPUT> buffer = new BufferedStream<>(this, monitor(), groupName());
        publishTo(buffer);
        return buffer;
    }

    @Override
    public Stream<OUTPUT,OUTPUT> deduplicate() {
        DeduplicationStream<OUTPUT> dedup = new DeduplicationStream<>(this, monitor(), groupName());
        publishTo(dedup);
        return dedup;
    }
}
