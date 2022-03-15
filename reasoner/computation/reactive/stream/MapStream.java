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

import java.util.function.Function;

public class MapStream<INPUT, OUTPUT> extends SingleReceiverStream<INPUT, OUTPUT> {

    private final Function<INPUT, OUTPUT> mappingFunc;
    private final ProviderRegistry.SingleProviderRegistry<INPUT> providerRegistry;

    public MapStream(Publisher<INPUT> publisher, Function<INPUT, OUTPUT> mappingFunc, Actor.Driver<Monitor> monitor,
                     String groupName) {
        super(monitor, groupName);
        this.mappingFunc = mappingFunc;
        this.providerRegistry = new ProviderRegistry.SingleProviderRegistry<>(publisher, this, monitor);
    }

    @Override
    protected ProviderRegistry<INPUT> providerRegistry() {
        return providerRegistry;
    }

    @Override
    public void receive(Provider<INPUT> provider, INPUT packet) {
        super.receive(provider, packet);
        receiverRegistry().setNotPulling();
        receiverRegistry().receiver().receive(this, mappingFunc.apply(packet));
    }
}
