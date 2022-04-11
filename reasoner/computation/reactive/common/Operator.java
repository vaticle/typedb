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

package com.vaticle.typedb.core.reasoner.computation.reactive.common;

import com.vaticle.typedb.common.collection.Either;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive.Publisher;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive.Subscriber;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.function.Function;

import static com.vaticle.typedb.common.collection.Collections.set;

public interface Operator {

    interface Source<OUTPUT> {

        boolean isExhausted(Subscriber<OUTPUT> subscriber);

        OUTPUT next(Subscriber<OUTPUT> subscriber);
    }

    interface Accepter<INPUT> extends Operator {

        void accept(Publisher<INPUT> publisher, INPUT packet);

    }

    interface Transformer<INPUT, OUTPUT> {

        Set<Publisher<INPUT>> initialNewPublishers();

        Either<Publisher<INPUT>, Set<OUTPUT>> accept(Publisher<INPUT> publisher, INPUT packet);

    }

    interface Sink<INPUT> extends Accepter<INPUT> {
        // TODO: Add methods to usefully retrieve items from the sink
    }

    interface Pool<INPUT, OUTPUT> {

        boolean accept(Publisher<INPUT> publisher, INPUT packet);

        boolean hasNext(Subscriber<OUTPUT> subscriber);

        OUTPUT next(Subscriber<OUTPUT> subscriber);

    }

    interface Bridge<PACKET> extends Accepter<PACKET>, Source<PACKET> {
        // TODO: To be used for negation
    }

    class Map<INPUT, OUTPUT> implements Transformer<INPUT, OUTPUT> {

        private final Function<INPUT, OUTPUT> mappingFunc;

        public Map(Function<INPUT, OUTPUT> mappingFunc) {
            this.mappingFunc = mappingFunc;
        }

        @Override
        public Set<Publisher<INPUT>> initialNewPublishers() {
            return set();
        }

        @Override
        public Either<Publisher<INPUT>, Set<OUTPUT>> accept(Publisher<INPUT> publisher, INPUT packet) {
            // TODO: Here and elsewhere the publisher argument is unused
            return Either.second(set(mappingFunc.apply(packet)));
        }

    }

    class FlatMap<INPUT, OUTPUT> implements Transformer<INPUT, OUTPUT> {

        private final Function<INPUT, FunctionalIterator<OUTPUT>> transform;

        public FlatMap(Function<INPUT, FunctionalIterator<OUTPUT>> transform) {
            this.transform = transform;
        }

        @Override
        public Set<Publisher<INPUT>> initialNewPublishers() {
            return set();
        }

        @Override
        public Either<Publisher<INPUT>, Set<OUTPUT>> accept(Publisher<INPUT> publisher, INPUT packet) {
            // This can actually create more receive() calls to downstream than the number of pulls it receives. Protect
            // against by manually adding .buffer() after calls to flatMap
            return Either.second(transform.apply(packet).toSet());
        }

    }

    class Supplier<PACKET> implements Source<PACKET> {

        private final java.util.function.Supplier<FunctionalIterator<PACKET>> iteratorSupplier;
        private FunctionalIterator<PACKET> iterator;

        public Supplier(java.util.function.Supplier<FunctionalIterator<PACKET>> iteratorSupplier) {
            this.iteratorSupplier = iteratorSupplier;
        }

        private FunctionalIterator<PACKET> iterator() {
            if (iterator == null) iterator = iteratorSupplier.get();
            return iterator;
        }

        @Override
        public boolean isExhausted(Subscriber<PACKET> subscriber) {
            return !iterator().hasNext();
        }

        @Override
        public PACKET next(Subscriber<PACKET> subscriber) {
            assert !isExhausted(subscriber);
            return iterator().next();
        }

    }

    class Distinct<PACKET> implements Transformer<PACKET, PACKET> {

        private final Set<PACKET> deduplicationSet;

        public Distinct() {
            this.deduplicationSet = new HashSet<>();
        }

        @Override
        public Set<Publisher<PACKET>> initialNewPublishers() {
            return set();
        }

        @Override
        public Either<Publisher<PACKET>, Set<PACKET>> accept(Publisher<PACKET> publisher, PACKET packet) {
            if (deduplicationSet.add(packet)) return Either.second(set(packet));
            else return Either.second(set());
        }
    }

    class Buffer<PACKET> implements Pool<PACKET, PACKET> {

        private final Stack<PACKET> stack;

        public Buffer() {
            this.stack = new Stack<>();
        }

        @Override
        public boolean accept(Publisher<PACKET> publisher, PACKET packet) {
            stack.add(packet);
            return true;
        }

        @Override
        public boolean hasNext(Subscriber<PACKET> subscriber) {
            return stack.size() > 0;
        }

        @Override
        public PACKET next(Subscriber<PACKET> subscriber) {
            return stack.pop();
        }

    }

    class FanOut<PACKET> implements Pool<PACKET, PACKET> {

        final java.util.Map<Subscriber<PACKET>, Integer> bufferPositions;  // Points to the next item needed
        final Set<PACKET> bufferSet;
        final List<PACKET> bufferList;

        public FanOut() {
            this.bufferSet = new HashSet<>();
            this.bufferList = new ArrayList<>();
            this.bufferPositions = new HashMap<>();
        }

        @Override
        public boolean accept(Publisher<PACKET> publisher, PACKET packet) {
            if (bufferSet.add(packet)) {
                bufferList.add(packet);
                return true;
            } else {
                return false;
            }
        }

        @Override
        public boolean hasNext(Subscriber<PACKET> subscriber) {
            bufferPositions.putIfAbsent(subscriber, 0);
            return bufferList.size() > bufferPositions.get(subscriber);
        }

        @Override
        public PACKET next(Subscriber<PACKET> subscriber) {
            Integer pos = bufferPositions.get(subscriber);
            bufferPositions.put(subscriber, pos + 1);
            return bufferList.get(pos);
        }

    }

}