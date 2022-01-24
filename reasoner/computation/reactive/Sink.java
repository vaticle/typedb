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

import javax.annotation.Nullable;

public abstract class Sink<PACKET> implements Receiver.Subscriber<PACKET>, Provider<PACKET>  {

    private SingleManager<PACKET> providerManager;
    private PacketMonitor monitor;
    protected boolean isPulling;

    protected SingleManager<PACKET> providerManager() {
        // TODO: We would initialise this on construction if the monitor was ready, but that is set later via setMonitor()
        if (providerManager == null) this.providerManager = new Provider.SingleManager<>(this, monitor());
        return providerManager;
    }

    protected PacketMonitor monitor() {
        return monitor;
    }

    public void setMonitor(PacketMonitor monitor) {
        this.monitor = monitor;
    }

    @Override
    public void subscribeTo(Provider<PACKET> provider) {
        providerManager().add(provider);
        if (isPulling) {
            monitor().onPathFork(1);  // This is the exception for where we add a fork when we initialise a new path
            providerManager().pull(provider);
        }
    }

    @Override
    public void pull(@Nullable Receiver<PACKET> receiver) {
        assert receiver == null;
        isPulling = true;
        if (providerManager().size() > 0) {
            // TODO: This condition isn't congruent with others, can we omit?
            providerManager().pullAll();
        }
    }

    public void pull() {
        pull(null);
    }
}
