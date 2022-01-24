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

import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.reasoner.computation.reactive.Receiver.Subscriber;
import com.vaticle.typedb.core.reasoner.utils.Tracer;

import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

public interface Provider<R> {

    void pull(Receiver<R> receiver);

    String groupName();

    interface Publisher<T> extends Provider<T> {

        void publishTo(Subscriber<T> subscriber);

        Reactive<T, T> findFirst();

        <R> Reactive<T, R> map(Function<T, R> function);

        <R> Reactive<T, R> flatMapOrRetry(Function<T, FunctionalIterator<R>> function);

        Reactive<T, T> buffer();

    }

    interface Manager<R> {
        // TODO: Consider managing whether to pull on upstreams by telling the manager whether we are pulling or not
        void add(Provider<R> provider);

        void pull(Provider<R> provider);

        void pullAll();

        int size();

        void receivedFrom(Provider<R> provider);

    }

    class SingleManager<R> implements Manager<R> {

        private @Nullable Provider<R> provider;
        private final Receiver<R> receiver;
        private final PacketMonitor monitor;

        public SingleManager(@Nullable Publisher<R> provider, Subscriber<R> subscriber, PacketMonitor monitor) {
            this.provider = provider;
            this.receiver = subscriber;
            this.monitor = monitor;
        }

        public SingleManager(Subscriber<R> subscriber, PacketMonitor monitor) {
            this.provider = null;
            this.receiver = subscriber;
            this.monitor = monitor;
        }

        @Override
        public void add(Provider<R> provider) {
            assert this.provider == null || provider == this.provider;  // TODO: Add proper exception for trying to add more than one provider. Ideally only allow setting provider once
            this.provider = provider;
        }

        @Override
        public void pull(Provider<R> provider) {
            assert this.provider != null;
            assert this.provider == provider;
            if (monitor == null) Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(receiver, provider));
            else Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(receiver, provider, monitor.pathsCount()));
            provider.pull(receiver);
        }

        @Override
        public void pullAll() {
            if (provider != null) pull(provider);
        }

        @Override
        public int size() {
            if (provider == null) return 0;
            else return 1;
        }

        @Override
        public void receivedFrom(Provider<R> provider) {

        }
    }

    class MultiManager<R> implements Manager<R> {

        private final Map<Provider<R>, Boolean> providersPulling;
        private final Receiver<R> receiver;
        private final PacketMonitor monitor;
        private boolean hasForked;

        public MultiManager(Subscriber<R> subscriber, @Nullable PacketMonitor monitor) {
            this.providersPulling = new HashMap<>();
            this.receiver = subscriber;
            this.monitor = monitor;
            this.hasForked = false;
        }

        @Override
        public void add(Provider<R> provider) {
            providersPulling.putIfAbsent(provider, false);
        }

        @Override
        public void pullAll() {
            providersPulling.forEach((provider, hasBeenPulled) -> {
                if (!hasBeenPulled) pull(provider);
            });
        }

        @Override
        public int size() {
            return providersPulling.size();
        }

        @Override
        public void receivedFrom(Provider<R> provider) {
            providersPulling.put(provider, false);
            // TODO: Put a path join here would be ideal except it might mean the path tally drops to zero right before it will go back up to 1.
        }

        @Override
        public void pull(Provider<R> provider) {
            if (!providersPulling.get(provider)) {
                if (hasForked && monitor != null) monitor.onPathFork(1);
                providersPulling.put(provider, true);
                if (monitor == null) Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(receiver, provider));
                else Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(receiver, provider, monitor.pathsCount()));
                provider.pull(receiver);
                hasForked = true;
            }
        }
    }
}
