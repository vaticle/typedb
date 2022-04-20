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

package com.vaticle.typedb.core.reasoner.reactive;

import com.vaticle.typedb.core.reasoner.reactive.common.PublisherRegistry;
import com.vaticle.typedb.core.reasoner.reactive.common.SubscriberRegistry;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.reasoner.reactive.common.Operator;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Function;

import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;

public class PoolingStream<PACKET> extends AbstractStream<PACKET, PACKET> {

    private final Operator.Pool<PACKET, PACKET> pool;

    protected PoolingStream(AbstractReactiveBlock<?, ?, ?, ?> reactiveBlock,
                            Operator.Pool<PACKET, PACKET> pool,
                            SubscriberRegistry<PACKET> subscriberRegistry,
                            PublisherRegistry<PACKET> publisherRegistry) {
        super(reactiveBlock, subscriberRegistry, publisherRegistry);
        this.pool = pool;
    }

    public static <PACKET> PoolingStream<PACKET> fanOut(
            AbstractReactiveBlock<?, ?, ?, ?> reactiveBlock) {
        return new PoolingStream<>(reactiveBlock, new Operator.FanOut<>(), new SubscriberRegistry.Multi<>(),
                                   new PublisherRegistry.Single<>());
    }

    public static <PACKET> PoolingStream<PACKET> fanIn(
            AbstractReactiveBlock<?, ?, ?, ?> reactiveBlock, Operator.Pool<PACKET, PACKET> pool) {
        return new PoolingStream<>(reactiveBlock, pool, new SubscriberRegistry.Single<>(), new PublisherRegistry.Multi<>());
    }

    public static <PACKET> PoolingStream<PACKET> fanInFanOut(AbstractReactiveBlock<?, ?, ?, ?> reactiveBlock) {
        return new PoolingStream<>(reactiveBlock, new Operator.FanOut<>(), new SubscriberRegistry.Multi<>(),
                                   new PublisherRegistry.Multi<>());
    }

    public static <PACKET> PoolingStream<PACKET> buffer(
            AbstractReactiveBlock<?, ?, ?, ?> reactiveBlock) {
        // TODO: The operator is not bound to the nature of the registries by type. We could not correctly use a FanOut
        //  operator here even though the types allow it. In fact what really changes in tandem is the signature of the
        //  receive() and pull() methods, as when there are multiple upstreams/downstreams we need to know which the
        //  message is from/to, but  not so for single upstream/downstreams
        return new PoolingStream<>(reactiveBlock, new Operator.Buffer<>(), new SubscriberRegistry.Single<>(),
                                   new PublisherRegistry.Single<>());
    }

    protected Operator.Pool<PACKET, PACKET> operator() {
        return pool;
    }

    @Override
    public void pull(Subscriber<PACKET> subscriber) {
        publisherActions.tracePull(subscriber);
        subscriberRegistry().recordPull(subscriber);
        // TODO: We don't care about the subscriber here
        if (operator().hasNext(subscriber)) {
            // TODO: Code duplicated in Source
            subscriberRegistry().setNotPulling(subscriber);  // TODO: This call should always be made when sending to a subscriber, so encapsulate it
            publisherActions.subscriberReceive(subscriber, operator().next(subscriber));
        } else {
            publisherRegistry().nonPulling().forEach(this::propagatePull);
        }
    }

    @Override
    public void receive(Publisher<PACKET> publisher, PACKET packet) {
        subscriberActions.traceReceive(publisher, packet);
        publisherRegistry().recordReceive(publisher);
        if (operator().accept(publisher, packet)) publisherActions.monitorCreateAnswers(1);
        publisherActions.monitorConsumeAnswers(1);
        AtomicBoolean retry = new AtomicBoolean();
        retry.set(false);
        iterate(subscriberRegistry().pulling()).forEachRemaining(subscriber -> {
            if (operator().hasNext(subscriber)) {
                subscriberRegistry().setNotPulling(subscriber);  // TODO: This call should always be made when sending to a subscriber, so encapsulate it
                publisherActions.subscriberReceive(subscriber, operator().next(subscriber));
            } else {
                retry.set(true);
            }
        });
        if (retry.get()) subscriberActions.rePullPublisher(publisher);
    }

    @Override
    public <MAPPED> Stream<PACKET, MAPPED> map(Function<PACKET, MAPPED> function) {
        return publisherActions.map(this, function);
    }

    @Override
    public <MAPPED> Stream<PACKET, MAPPED> flatMap(Function<PACKET, FunctionalIterator<MAPPED>> function) {
        return publisherActions.flatMap(this, function);
    }

    @Override
    public Stream<PACKET, PACKET> distinct() {
        return publisherActions.distinct(this);
    }

    @Override
    public Stream<PACKET, PACKET> buffer() {
        return publisherActions.buffer(this);
    }

    @Override
    public String toString() {
        return getClass().getSimpleName() + ":" + operator().getClass().getSimpleName();
    }

}