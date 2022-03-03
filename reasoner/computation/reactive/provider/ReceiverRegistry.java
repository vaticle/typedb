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

package com.vaticle.typedb.core.reasoner.computation.reactive.provider;

import com.vaticle.typedb.core.reasoner.computation.actor.Monitor;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;

import java.util.HashSet;
import java.util.Set;

public abstract class ReceiverRegistry<R> {

    abstract void setNotPulling();

    abstract boolean addReceiver(Reactive.Receiver<R> receiver);

    public static class SingleReceiverRegistry<R> extends ReceiverRegistry<R> {

        private final Reactive.Provider<R> provider;
        private final Monitor.MonitorRef monitor;
        private boolean isPulling;
        private Reactive.Receiver<R> receiver;

        public SingleReceiverRegistry(Reactive.Provider<R> provider, Reactive.Receiver<R> receiver, Monitor.MonitorRef monitor) {
            this.provider = provider;
            addReceiver(receiver);
            this.monitor = monitor;
            this.isPulling = false;
        }

        public SingleReceiverRegistry(Reactive.Provider<R> provider, Monitor.MonitorRef monitor) {
            this.provider = provider;
            this.receiver = null;
            this.monitor = monitor;
            this.isPulling = false;
        }

        @Override
        public void setNotPulling() {
            isPulling = false;
        }

        public void recordPull(Reactive.Receiver<R> receiver) {
            assert this.receiver.equals(receiver);
            isPulling = true;
        }

        public boolean isPulling() {
            return isPulling;
        }

        @Override
        public boolean addReceiver(Reactive.Receiver<R> receiver) {
            monitor.registerPath(receiver, provider);
            assert this.receiver == null;
            this.receiver = receiver;
            return false;
        }

        public Reactive.Receiver<R> receiver() {
            assert this.receiver != null;
            return receiver;
        }
    }

    public static class MultiReceiverRegistry<R> extends ReceiverRegistry<R> {

        private final Reactive.Provider<R> provider;
        private final Monitor.MonitorRef monitor;
        private final Set<Reactive.Receiver<R>> receivers;
        private final Set<Reactive.Receiver<R>> pullingReceivers;

        public MultiReceiverRegistry(Reactive.Provider<R> provider, Monitor.MonitorRef monitor) {
            this.provider = provider;
            this.monitor = monitor;
            this.receivers = new HashSet<>();
            this.pullingReceivers = new HashSet<>();
        }

        @Override
        public void setNotPulling() {
            pullingReceivers.clear();
        }

        public void recordPull(Reactive.Receiver<R> receiver) {
            assert receivers.contains(receiver);
            pullingReceivers.add(receiver);
        }

        public boolean isPulling() {
            return pullingReceivers.size() > 0;
        }

        @Override
        public boolean addReceiver(Reactive.Receiver<R> receiver) {
            boolean newReceiver = receivers.add(receiver);
            if (newReceiver) monitor.registerPath(receiver, provider);
            return newReceiver;
        }

        public Set<Reactive.Receiver<R>> pullingReceivers() {
            return new HashSet<>(pullingReceivers);
        }

        public int size() {
            return receivers.size();
        }
    }
}
