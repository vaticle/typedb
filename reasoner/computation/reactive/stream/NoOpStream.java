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
import com.vaticle.typedb.core.reasoner.computation.reactive.receiver.ProviderRegistry;

public class NoOpStream<PACKET> extends SingleReceiverSingleProviderStream<PACKET, PACKET> {  // TODO: Can we do away with this class?

    public NoOpStream(Processor<?, ?, ?, ?> processor) {
        super(processor);
    }

    @Override
    public void receive(Provider.Sync<PACKET> provider, PACKET packet) {
        super.receive(provider, packet);
        receiverRegistry().setNotPulling();
        receiverRegistry().receiver().receive(this, packet);
    }
}
