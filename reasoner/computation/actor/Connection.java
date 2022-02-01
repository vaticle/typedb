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

package com.vaticle.typedb.core.reasoner.computation.actor;

import com.vaticle.typedb.core.concurrent.actor.Actor;
import com.vaticle.typedb.core.reasoner.utils.Tracer;

import java.util.List;
import java.util.Set;
import java.util.function.Function;

public class Connection<PACKET, PROCESSOR extends Processor<PACKET, ?, ?, PROCESSOR>, PROV_PROCESSOR extends Processor<?, PACKET, ?, PROV_PROCESSOR>> {

    private final Actor.Driver<PROCESSOR> recProcessor;
    private final Actor.Driver<PROV_PROCESSOR> provProcessor;
    private final long recEndpointId;
    private final long provEndpointId;
    private final List<Function<PACKET, PACKET>> transforms;

    /**
     * Connects a processor outlet (upstream, publishing) to another processor's inlet (downstream, subscribing)
     */
    Connection(Actor.Driver<PROCESSOR> recProcessor, Actor.Driver<PROV_PROCESSOR> provProcessor, long recEndpointId,
               long provEndpointId, List<Function<PACKET, PACKET>> transforms) {
        this.recProcessor = recProcessor;
        this.provProcessor = provProcessor;
        this.recEndpointId = recEndpointId;
        this.provEndpointId = provEndpointId;
        this.transforms = transforms;
    }

    protected void receive(PACKET packet) {
        recProcessor.execute(actor -> actor.endpointReceive(packet, recEndpointId));
    }

    protected void pull() {
        provProcessor.execute(actor -> actor.endpointPull(provEndpointId));
    }

    protected void propagateMonitors(Set<Actor.Driver<? extends Processor<?, ?, ?, ?>>> monitors) {
        provProcessor.execute(actor -> actor.setMonitorReporting(monitors));
    }

    protected void registerWithMonitor(Actor.Driver<? extends Processor<?, ?, ?, ?>> monitor) {
        Tracer.getIfEnabled().ifPresent(tracer -> tracer.registerWithMonitor(this, monitor));
        monitor.execute(actor -> actor.monitoring().asMonitor().register(provProcessor));
    }

    protected long receiverEndpointId() {
        return recEndpointId;
    }

    public long providerEndpointId() {
        return provEndpointId;
    }

    public List<Function<PACKET, PACKET>> transformations() {
        return transforms;
    }

}
