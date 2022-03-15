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

package com.vaticle.typedb.core.reasoner.computation.reactive.stream;

import com.vaticle.typedb.core.concurrent.actor.Actor;
import com.vaticle.typedb.core.reasoner.computation.actor.Monitor;
import com.vaticle.typedb.core.reasoner.computation.reactive.receiver.ProviderRegistry;

import java.util.Stack;

public class BufferedStream<PACKET> extends SingleReceiverStream<PACKET, PACKET> {

    private final ProviderRegistry.SingleProviderRegistry<PACKET> providerRegistry;
    private final Stack<PACKET> stack;

    public BufferedStream(Publisher<PACKET> publisher, Actor.Driver<Monitor> monitor, String groupName) {
        super(monitor, groupName);
        this.providerRegistry = new ProviderRegistry.SingleProviderRegistry<>(publisher, this, monitor);
        this.stack = new Stack<>();
    }

    @Override
    protected ProviderRegistry<PACKET> providerRegistry() {
        return providerRegistry;
    }

    @Override
    public void receive(Provider<PACKET> provider, PACKET packet) {
        super.receive(provider, packet);
        if (receiverRegistry().isPulling()) {
            receiverRegistry().setNotPulling();
            receiverRegistry().receiver().receive(this, packet);
        } else {
            // TODO: Could add an answer deduplication optimisation here, but means holding an extra set of all answers seen
            stack.add(packet);
        }
    }

    @Override
    public void pull(Receiver<PACKET> receiver) {
        assert receiver.equals(receiverRegistry().receiver());
        receiverRegistry().recordPull(receiver);
        if (stack.size() > 0) {
            receiver.receive(this, stack.pop());
        } else {
            assert receiverRegistry().isPulling();
            providerRegistry().pullAll();
        }
    }
}
