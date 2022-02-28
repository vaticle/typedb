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

import com.vaticle.typedb.core.reasoner.computation.actor.Processor;
import com.vaticle.typedb.core.reasoner.computation.actor.Processor.TerminationTracker;
import com.vaticle.typedb.core.reasoner.computation.reactive.receiver.ProviderRegistry;

import java.util.Set;
import java.util.Stack;

public class BufferedStream<PACKET> extends SingleReceiverStream<PACKET, PACKET> {

    private final ProviderRegistry.SingleProviderRegistry<PACKET> providerManager;
    private final Stack<PACKET> stack;

    public BufferedStream(Publisher<PACKET> publisher, TerminationTracker monitor, String groupName) {
        super(monitor, groupName);
        this.providerManager = new ProviderRegistry.SingleProviderRegistry<>(publisher, this);
        this.stack = new Stack<>();
    }

    @Override
    protected ProviderRegistry<PACKET> providerRegistry() {
        return providerManager;
    }

    @Override
    public void receive(Provider<PACKET> provider, PACKET packet) {
        super.receive(provider, packet);
        if (receiverRegistry().isPulling()) {
            receiverRegistry().recordReceive();
            receiverRegistry().receiver().receive(this, packet);
        } else {
            // TODO: Could add an answer deduplication optimisation here, but means holding an extra set of all answers seen
            stack.add(packet);
        }
    }

    @Override
    public void pull(Receiver<PACKET> receiver, Set<Processor.Monitor.Reference> monitors) {
        assert receiver.equals(receiverRegistry().receiver());
        if (stack.size() > 0) {
            receiver.receive(this, stack.pop());
        } else {
            if (receiverRegistry().recordPull(monitors)) providerRegistry().pullAll(receiverRegistry().monitors());
        }
    }
}
