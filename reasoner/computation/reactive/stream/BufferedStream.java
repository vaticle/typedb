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
import com.vaticle.typedb.core.reasoner.utils.Tracer;

import java.util.Stack;

public class BufferedStream<PACKET> extends SingleReceiverSingleProviderStream<PACKET, PACKET> {

    private final Stack<PACKET> stack;

    public BufferedStream(Provider.Sync.Publisher<PACKET> publisher, Processor<?, ?, ?, ?> processor) {
        super(publisher, processor);
        this.stack = new Stack<>();
    }

    @Override
    public void receive(Provider.Sync<PACKET> provider, PACKET packet) {
        super.receive(provider, packet);
        if (receiverRegistry().isPulling()) {
            receiverRegistry().setNotPulling();
            receiverRegistry().receiver().receive(this, packet);
        } else {
            stack.add(packet);
        }
    }

    @Override
    public void pull(Receiver.Sync<PACKET> receiver) {
        assert receiver.equals(receiverRegistry().receiver());
        Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(receiver.identifier(),identifier()));
        receiverRegistry().recordPull(receiver);
        if (stack.size() > 0) {
            receiver.receive(this, stack.pop());
        } else {
            if (receiverRegistry().isPulling() && providerRegistry().setPulling()) {
                providerRegistry().provider().pull(this);
            }
        }
    }
}
