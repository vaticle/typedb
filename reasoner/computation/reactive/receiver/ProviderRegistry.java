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

package com.vaticle.typedb.core.reasoner.computation.reactive.receiver;

import com.vaticle.typedb.core.reasoner.computation.actor.Processor;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.utils.Tracer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public abstract class ProviderRegistry<R> {
    // TODO: Consider managing whether to pull on upstreams by telling the manager whether we are pulling or not
    public abstract void add(Reactive.Provider<R> provider);

    public abstract void pull(Reactive.Provider<R> provider, Set<Processor.Monitor.Reference> monitors);

    public abstract void pullAll(Set<Processor.Monitor.Reference> monitors);

    public abstract void recordReceive(Reactive.Provider<R> provider);

    public static class SingleProviderRegistry<R> extends ProviderRegistry<R> {

        private Reactive.Provider<R> provider;
        private final Reactive.Receiver<R> receiver;
        private boolean isPulling;

        public SingleProviderRegistry(Reactive.Provider.Publisher<R> provider, Reactive.Receiver<R> receiver) {
            this.provider = provider;
            this.receiver = receiver;
            this.isPulling = false;
        }

        public SingleProviderRegistry(Reactive.Receiver<R> receiver) {
            this.provider = null;
            this.receiver = receiver;
            this.isPulling = false;
        }

        @Override
        public void add(Reactive.Provider<R> provider) {
            assert this.provider == null || provider == this.provider;
            this.provider = provider;
        }

        @Override
        public void pullAll(Set<Processor.Monitor.Reference> monitors) {
            if (provider != null) pull(provider, monitors);
        }

        @Override
        public void pull(Reactive.Provider<R> provider, Set<Processor.Monitor.Reference> monitors) {
            assert this.provider != null;
            assert this.provider == provider;
            setPulling(true);
            pullProvider(monitors);
        }

        private boolean isPulling() {
            return isPulling;
        }

        private void setPulling(boolean pulling) {
            isPulling = pulling;
        }

        private void pullProvider(Set<Processor.Monitor.Reference> monitors) {
            assert this.provider != null;
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(receiver, provider, monitors));
            provider.pull(receiver, monitors);
        }

        @Override
        public void recordReceive(Reactive.Provider<R> provider) {
            assert this.provider == provider;
            setPulling(false);
        }
    }

    public static class MultiProviderRegistry<R> extends ProviderRegistry<R> {

        private final Map<Reactive.Provider<R>, Boolean> providersPullState;
        private final Reactive.Receiver<R> receiver;

        public MultiProviderRegistry(Reactive.Receiver.Subscriber<R> subscriber) {
            this.providersPullState = new HashMap<>();
            this.receiver = subscriber;
        }

        @Override
        public void add(Reactive.Provider<R> provider) {
            providersPullState.putIfAbsent(provider, false);
        }

        @Override
        public void recordReceive(Reactive.Provider<R> provider) {
            setPulling(provider, false);
        }

        @Override
        public void pullAll(Set<Processor.Monitor.Reference> monitors) {
            providersPullState.keySet().forEach(provider -> pull(provider, monitors));
        }

        @Override
        public void pull(Reactive.Provider<R> provider, Set<Processor.Monitor.Reference> monitors) {
            assert providersPullState.containsKey(provider);
            if (!isPulling(provider)) {
                setPulling(provider, true);
                pullProvider(provider, monitors);
            }
        }

        private boolean isPulling(Reactive.Provider<R> provider) {
            assert providersPullState.containsKey(provider);
            return providersPullState.get(provider);
        }

        private void setPulling(Reactive.Provider<R> provider, boolean isPulling) {
            assert providersPullState.containsKey(provider);
            providersPullState.put(provider, isPulling);
        }

        private void pullProvider(Reactive.Provider<R> provider, Set<Processor.Monitor.Reference> monitors) {
            assert providersPullState.containsKey(provider);
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.pull(receiver, provider, monitors));
            provider.pull(receiver, monitors);
        }

        public int size() {
            return providersPullState.size();
        }
    }
}
