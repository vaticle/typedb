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
import com.vaticle.typedb.core.concurrent.actor.Actor;

import java.util.function.Function;

public interface Reactive {

    AbstractReactiveBlock<?, ?, ?, ?> reactiveBlock();  // TODO: It's weird to be able to access your subscriber/publisher's reactiveBlock, but this is needed for monitoring?

    Identifier<?, ?> identifier();

    interface Identifier<P_IN, P_OUT> {

        String toString();

        // TODO: Weird to have a reactiveBlock inside an Identifier, if anything we would expect to see a reactiveBlock ID
        //  here, or use some kind of compound ID of Reactive + ReactiveBlock where we need it
        Actor.Driver<? extends AbstractReactiveBlock<P_IN, P_OUT, ?, ?>> reactiveBlock();

    }

    interface Publisher<PACKET> extends Reactive {

        void pull(Subscriber<PACKET> subscriber);

        void registerSubscriber(Subscriber<PACKET> subscriber);

        <MAPPED> Stream<PACKET, MAPPED> map(Function<PACKET, MAPPED> function);

        <MAPPED> Stream<PACKET, MAPPED> flatMap(Function<PACKET, FunctionalIterator<MAPPED>> function);

        Stream<PACKET, PACKET> buffer();

        Stream<PACKET, PACKET> distinct();

    }

    interface Subscriber<PACKET> extends Reactive {

        void receive(Publisher<PACKET> publisher, PACKET packet);

        void registerPublisher(Publisher<PACKET> publisher);

        interface Finishable<PACKET> extends Reactive.Subscriber<PACKET> {

            void finished();

        }
    }

    interface Stream<INPUT, OUTPUT> extends Subscriber<INPUT>, Publisher<OUTPUT> {

    }
}