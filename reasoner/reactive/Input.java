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

import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.reasoner.utils.Tracer;

import java.util.function.Function;

/**
 * Governs an input to a reactiveBlock
 */
public class Input<PACKET> implements Reactive.Publisher<PACKET> {

    private final Identifier<PACKET, ?> identifier;
    private final AbstractReactiveBlock<PACKET, ?, ?, ?> reactiveBlock;
    private final AbstractReactive.PublisherActionsImpl<PACKET> publisherActions;
    private boolean ready;
    private Identifier<?, PACKET> providingOutput;
    private Subscriber<PACKET> subscriber;

    public Input(AbstractReactiveBlock<PACKET, ?, ?, ?> reactiveBlock) {
        this.reactiveBlock = reactiveBlock;
        this.identifier = reactiveBlock.registerReactive(this);
        this.ready = false;
        this.publisherActions = new AbstractReactive.PublisherActionsImpl<>(this);
    }

    @Override
    public AbstractReactiveBlock<?, ?, ?, ?> reactiveBlock() {
        return reactiveBlock;
    }

    @Override
    public Identifier<PACKET, ?> identifier() {
        return identifier;
    }

    public void setOutput(Identifier<?, PACKET> outputId) {
        assert providingOutput == null;
        providingOutput = outputId;
        reactiveBlock().monitor().execute(actor -> actor.registerPath(identifier(), outputId));
        assert !ready;
        ready = true;
    }

    public void pull() {
        pull(subscriber);
    }

    @Override
    public void pull(Subscriber<PACKET> subscriber) {
        assert subscriber.equals(this.subscriber);
        Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(subscriber.identifier(), identifier()));
        if (ready) providingOutput.reactiveBlock().execute(actor -> actor.pull(providingOutput));
    }

    @Override
    public void registerSubscriber(Subscriber<PACKET> subscriber) {
        assert this.subscriber == null;
        this.subscriber = subscriber;
        subscriber.registerPublisher(this);
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
    public Stream<PACKET, PACKET> buffer() {
        return publisherActions.buffer(this);
    }

    @Override
    public Stream<PACKET, PACKET> distinct() {
        return publisherActions.distinct(this);
    }

    public void receive(Identifier<?, PACKET> outputId, PACKET packet) {
        Tracer.getIfEnabled().ifPresent(tracer -> tracer.receive(outputId, identifier(), packet));
        subscriber.receive(this, packet);
    }

    @Override
    public String toString() {
        return reactiveBlock.debugName().get() + ":" + getClass().getSimpleName();
    }

}