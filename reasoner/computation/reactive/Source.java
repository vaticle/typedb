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

package com.vaticle.typedb.core.reasoner.computation.reactive;

import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.reasoner.computation.actor.Processor;
import com.vaticle.typedb.core.reasoner.computation.reactive.operator.Operator;
import com.vaticle.typedb.core.reasoner.computation.reactive.utils.ReactiveActions;
import com.vaticle.typedb.core.reasoner.computation.reactive.utils.SubscriberRegistry;

import java.util.function.Function;

public class Source<PACKET> extends ReactiveImpl implements Reactive.Publisher<PACKET> {

    private final Operator.Source<PACKET> sourceOperator;
    private final SubscriberRegistry.Single<Subscriber<PACKET>> subscriberRegistry;
    private final ReactiveActions.PublisherActions<PACKET> providerActions;

    protected Source(Processor<?, ?, ?, ?> processor, Operator.Source<PACKET> sourceOperator) {
        super(processor);
        this.sourceOperator = sourceOperator;
        this.subscriberRegistry = new SubscriberRegistry.Single<>();
        this.providerActions = new AbstractStream.PublisherActionsImpl<>(this);
        processor().monitor().execute(actor -> actor.registerSource(identifier()));
    }

    public static <OUTPUT> Source<OUTPUT> create(Processor<?, ?, ?, ?> processor,
                                                 Operator.Source<OUTPUT> operator) {
        return new Source<>(processor, operator);
    }

    private Operator.Source<PACKET> operator() {
        return sourceOperator;
    }

    @Override
    public void pull(Subscriber<PACKET> subscriber) {
        providerActions.tracePull(subscriber);
        subscriberRegistry().recordPull(subscriber);
        if (!operator().isExhausted(subscriber)) {
            // TODO: Code duplicated in PoolingStream
            subscriberRegistry().setNotPulling(subscriber);  // TODO: This call should always be made when sending to a subscriber, so encapsulate it
            Operator.Supplied<PACKET> supplied = operator().next(subscriber);
            providerActions.processEffects(supplied);
            providerActions.subscriberReceive(subscriber, supplied.output());  // TODO: If the operator isn't tracking which subscribers have seen this packet then it needs to be sent to all subscribers. So far this is never the case.
        } else {
            processor().monitor().execute(actor -> actor.sourceFinished(identifier()));
        }
    }

    public SubscriberRegistry<Subscriber<PACKET>> subscriberRegistry() {
        return subscriberRegistry;
    }

    @Override
    public void registerSubscriber(Subscriber<PACKET> subscriber) {
        subscriberRegistry.addSubscriber(subscriber);
        subscriber.registerProvider(this);  // TODO: Bad to have this mutual registering in one method call, it's unclear
    }

    @Override
    public <MAPPED> Stream<PACKET, MAPPED> map(Function<PACKET, MAPPED> function) {
        return providerActions.map(this, function);
    }

    @Override
    public <MAPPED> Stream<PACKET, MAPPED> flatMap(Function<PACKET, FunctionalIterator<MAPPED>> function) {
        return providerActions.flatMap(this, function);
    }

    @Override
    public Stream<PACKET, PACKET> distinct() {
        return providerActions.distinct(this);
    }

    @Override
    public Stream<PACKET, PACKET> buffer() {
        return providerActions.buffer(this);
    }

}
