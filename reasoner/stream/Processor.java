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

package com.vaticle.typedb.core.reasoner.stream;

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.concurrent.actor.Actor;

import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

import static com.vaticle.typedb.common.collection.Collections.set;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;

public abstract class Processor<OUTPUT, PROCESSOR extends Processor<OUTPUT, PROCESSOR>> extends Actor<PROCESSOR> {

    private final Driver<? extends Controller<?, ?, OUTPUT, PROCESSOR, ?>> controller;
    private final OutletManager<OUTPUT> outletManager;

    protected Processor(Driver<PROCESSOR> driver,
                        Driver<? extends Controller<?, ?, OUTPUT, PROCESSOR, ?>> controller,
                        String name, OutletManager<OUTPUT> outletManager) {
        super(driver, name);
        this.controller = controller;
        this.outletManager = outletManager;
    }

    public OutletManager<OUTPUT> outletManager() {
        return outletManager;
    }

    @Override
    protected void exception(Throwable e) {}

    protected <PACKET, UPS_CID, UPS_PID, UPS_PROCESSOR extends Processor<PACKET, UPS_PROCESSOR>>
    void requestConnection(Connection.Builder<PACKET, PROCESSOR, UPS_CID, UPS_PID, UPS_PROCESSOR> connectionBuilder) {
        controller.execute(actor -> actor.findUpstreamConnection(connectionBuilder));
    }

    protected <DNS_PROCESSOR extends Processor<?, DNS_PROCESSOR>>
    void buildConnection(Connection.Builder<OUTPUT, DNS_PROCESSOR, ?, ?, PROCESSOR> connectionBuilder) {
        OutletManager<OUTPUT>.Outlet newOutlet = outletManager().newOutlet();
        Connection<OUTPUT, DNS_PROCESSOR, PROCESSOR> connection =
                connectionBuilder.addOutlet(newOutlet).addUpstreamProcessor(driver()).build();
        newOutlet.addDownstream(connection);
        connection.downstreamProcessor().execute(actor -> actor.setReady(connection));
    }

    protected <PACKET, UPS_PROCESSOR extends Processor<PACKET, UPS_PROCESSOR>> void setReady(Connection<PACKET, PROCESSOR, UPS_PROCESSOR> connection) {
        connection.inletPort().addUpstream(connection);
    }

    interface Pullable<T> {
        void pull(Receiver<T> receiver);
    }

    interface Receiver<T> {
        void receive(Pullable<T> upstream, T packet);
    }

    // TODO: Note that the identifier for an upstream controller (e.g. resolvable) is different to for an upstream processor (resolvable plus bounds). So inletmanagers are managed based on the former.

    public static abstract class OutletManager<OUTPUT> extends IdentityReactive<OUTPUT> {

        OutletManager() {
            super(set(), set());
        }

        public abstract Outlet newOutlet();

        public static class Single<OUTPUT> extends OutletManager<OUTPUT> {

            Single() {
                super();
            }

            @Override
            public Outlet newOutlet() {
                if (downstreams().size() > 0) throw TypeDBException.of(ILLEGAL_STATE);
                else {
                    OutletManager<OUTPUT>.Outlet newOutlet = new Outlet(connection, this);
                    addDownstream(newOutlet);
                    return newOutlet;
                }
            }

        }

        public static class DynamicMulti<OUTPUT> extends OutletManager<OUTPUT> {

            DynamicMulti() {
                super();
            }

            @Override
            public Outlet newOutlet() {
                // TODO: Handle dynamically adding outlets in the reactive components
                OutletManager<OUTPUT>.Outlet newOutlet = new Outlet(connection, this);
                addDownstream(newOutlet);
                return newOutlet;
            }

        }

        class Outlet extends IdentityReactive<OUTPUT> {

            Outlet(Receiver<OUTPUT> downstream, Pullable<OUTPUT> upstream) {
                super(set(downstream), set(upstream));
            }
        }

    }

    static class Source<INPUT> implements Pullable<INPUT> {

        private final Supplier<FunctionalIterator<INPUT>> iteratorSupplier;
        private FunctionalIterator<INPUT> iterator;

        public Source(Supplier<FunctionalIterator<INPUT>> iteratorSupplier) {
            this.iteratorSupplier = iteratorSupplier;
            this.iterator = null;
        }

        public static <INPUT> Source<INPUT> fromIteratorSupplier(Supplier<FunctionalIterator<INPUT>> iteratorSupplier) {
            return new Source<>(iteratorSupplier);
        }

        @Override
        public void pull(Receiver<INPUT> receiver) {
            if (iterator == null) iterator = iteratorSupplier.get();
            if (iterator.hasNext()) {
                receiver.receive(this, iterator.next());
            }
        }
    }

    public static abstract class Reactive<INPUT, OUTPUT> implements Pullable<OUTPUT>, Receiver<INPUT> {

        private final Set<Receiver<OUTPUT>> downstreams;
        private final Set<Pullable<INPUT>> upstreams;
        protected boolean isPulling;

        Reactive(Set<Receiver<OUTPUT>> downstreams, Set<Pullable<INPUT>> upstreams) {
            this.downstreams = downstreams;
            this.upstreams = upstreams;
            this.isPulling = false;
        }

        @Override
        public void pull(Receiver<OUTPUT> receiver) {
            downstreams.add(receiver);  // TODO: This way we dynamically add the downstreams
            if (!isPulling) {
                upstreams.forEach(this::upstreamPull);
                isPulling = true;
            }
        }

        Set<Receiver<OUTPUT>> downstreams() {
            return downstreams;
        }

        Set<Pullable<INPUT>> upstreams() {
            return upstreams;
        }

        protected void addDownstream(Receiver<OUTPUT> downstream) {
            downstreams.add(downstream);
            // TODO: To dynamically add downstreams we need to have buffered all prior packets and send them here
            //  we can adopt a policy that if you weren't a downstream in time for the packet then you miss it, and
            //  break this only for outlets which will do the buffering and ensure all downstreams receive all answers.
        }

        protected Pullable<INPUT> addUpstream(Pullable<INPUT> upstream) {
            upstreams.add(upstream);
            if (isPulling) upstream.pull(this);
            return upstream;
        }

        protected void downstreamReceive(Receiver<OUTPUT> downstream, OUTPUT p) {
            // TODO: Override for cross-actor receiving
            downstream.receive(this, p);  // TODO: Remove casting
        }

        protected void upstreamPull(Pullable<INPUT> upstream) {
            // TODO: Override for cross-actor pulling
            upstream.pull(this);
        }

        public IdentityReactive<INPUT> findFirstIf(boolean condition) {
            if (condition) {
                FindFirstReactive<INPUT> newReactive = new FindFirstReactive<>(set(this), set());
                addUpstream(newReactive);
                return newReactive;
            } else {
                IdentityReactive<INPUT> newReactive = new IdentityReactive<>(set(this), set());
                addUpstream(newReactive);
                return newReactive;
            }
        }

        public <UPS_INPUT> MapReactive<UPS_INPUT, INPUT> map(Function<UPS_INPUT, INPUT> function) {
            MapReactive<UPS_INPUT, INPUT> newReactive = new MapReactive<>(set(this), set(), function);
            addUpstream(newReactive);
            return newReactive;
        }

        public <UPS_INPUT> FlatMapOrRetryReactive<UPS_INPUT, INPUT> flatMapOrRetry(Function<UPS_INPUT, FunctionalIterator<INPUT>> function) {
            FlatMapOrRetryReactive<UPS_INPUT, INPUT> newReactive = new FlatMapOrRetryReactive<>(set(this), set(), function);
            addUpstream(newReactive);
            return newReactive;
        }

        public Reactive<INPUT, OUTPUT> join(Pullable<INPUT> pullable) {
            addUpstream(pullable);
            return this;
        }

        public Reactive<INPUT, OUTPUT> join(Set<Pullable<INPUT>> pullables) {
            pullables.forEach(this::addUpstream);
            return this;
        }
    }

    public static class IdentityReactive<T> extends Reactive<T, T> {

        IdentityReactive(Set<Receiver<T>> downstreams, Set<Pullable<T>> upstreams) {
            super(downstreams, upstreams);
        }

        @Override
        public void receive(Pullable<T> upstream, T packet) {  // TODO: Doesn't do a retry
            downstreams().forEach(downstream -> downstreamReceive(downstream, packet));
        }
    }

    public static class MapReactive<INPUT, OUTPUT> extends Reactive<INPUT, OUTPUT> {

        private final Function<INPUT, OUTPUT> mappingFunc;

        MapReactive(Set<Receiver<OUTPUT>> downstreams, Set<Pullable<INPUT>> upstreams,
                               Function<INPUT, OUTPUT> mappingFunc) {
            super(downstreams, upstreams);
            this.mappingFunc = mappingFunc;
        }

        @Override
        public void receive(Pullable<INPUT> upstream, INPUT packet) {
            downstreams().forEach(downstream -> downstreamReceive(downstream, mappingFunc.apply(packet)));
        }

    }

    public static class FlatMapOrRetryReactive<INPUT, OUTPUT> extends Reactive<INPUT, OUTPUT> {

        private final Function<INPUT, FunctionalIterator<OUTPUT>> transform;

        FlatMapOrRetryReactive(Set<Receiver<OUTPUT>> downstreams, Set<Pullable<INPUT>> upstreams,
                               Function<INPUT, FunctionalIterator<OUTPUT>> transform) {
            super(downstreams, upstreams);
            this.transform = transform;
        }

        @Override
        public void receive(Pullable<INPUT> upstream, INPUT packet) {
            FunctionalIterator<OUTPUT> transformed = transform.apply(packet);
            if (transformed.hasNext()) {
                transformed.forEachRemaining(t -> downstreams().forEach(downstream -> downstreamReceive(downstream, t)));
                isPulling = false;
            } else if (isPulling) {
                upstreamPull(upstream);  // Automatic retry
            }
        }

    }

    public static class FindFirstReactive<T> extends IdentityReactive<T> {

        private boolean packetFound;

        FindFirstReactive(Set<Receiver<T>> downstreams, Set<Pullable<T>> upstreams) {
            super(downstreams, upstreams);
            this.packetFound = false;
        }

        @Override
        public void receive(Pullable<T> upstream, T packet) {  // TODO: Doesn't do a retry
            packetFound = true;
            super.receive(upstream, packet);
        }

        @Override
        public void pull(Receiver<T> receiver) {
            if (!packetFound) super.pull(receiver);
        }
    }

    public static class Connection<PACKET, PROCESSOR extends Processor<?, PROCESSOR>, UPS_PROCESSOR extends Processor<PACKET, UPS_PROCESSOR>> extends IdentityReactive<PACKET> {

        private final Driver<PROCESSOR> downstreamProcessor;
        private final Driver<UPS_PROCESSOR> upstreamProcessor;
        private final Reactive<PACKET, ?> inletPort;
        private final OutletManager<PACKET>.Outlet outlet;

        public Connection(Driver<PROCESSOR> downstreamProcessor, Driver<UPS_PROCESSOR> upstreamProcessor, Reactive<PACKET, ?> inletPort, OutletManager<PACKET>.Outlet outlet) {
            super(set(inletPort), set(outlet));
            this.downstreamProcessor = downstreamProcessor;
            this.upstreamProcessor = upstreamProcessor;
            this.inletPort = inletPort;
            this.outlet = outlet;
        }

        private Driver<UPS_PROCESSOR> upstreamProcessor() {
            return upstreamProcessor;
        }

        Driver<PROCESSOR> downstreamProcessor() {
            return downstreamProcessor;
        }

        OutletManager<PACKET>.Outlet outlet() {
            return outlet;  // TODO: Duplicates upstreams()
        }

        Reactive<PACKET, ?> inletPort() {
            return inletPort;  // TODO: Duplicates downstreams()
        }

        @Override
        protected void upstreamPull(Pullable<PACKET> upstream) {
            upstreamProcessor().execute(actor -> upstream.pull(this));
        }

        @Override
        protected void downstreamReceive(Receiver<PACKET> downstream, PACKET packet) {
            downstreamProcessor().execute(actor -> downstream.receive(this, packet));
        }

        public static class Builder<PACKET, PROCESSOR extends Processor<?, PROCESSOR>, UPS_CID, UPS_PID, UPS_PROCESSOR extends Processor<PACKET, UPS_PROCESSOR>> {

            private final Driver<PROCESSOR> downstreamProcessor;
            private final UPS_CID upstreamControllerId;
            private Driver<UPS_PROCESSOR> upstreamProcessor;
            private final UPS_PID upstreamProcessorId;
            private final Reactive<PACKET, ?> inletPort;
            private OutletManager<PACKET>.Outlet outlet;

            protected Builder(Driver<PROCESSOR> downstreamProcessor, UPS_CID upstreamControllerId,
                              UPS_PID upstreamProcessorId, Reactive<PACKET, ?> inletPort) {
                this.downstreamProcessor = downstreamProcessor;
                this.upstreamControllerId = upstreamControllerId;
                this.upstreamProcessorId = upstreamProcessorId;
                this.inletPort = inletPort;
            }

            UPS_CID upstreamControllerId() {
                return upstreamControllerId;
            }


            protected Builder<PACKET, PROCESSOR, UPS_CID, UPS_PID, UPS_PROCESSOR> addOutlet(OutletManager<PACKET>.Outlet outlet) {
                this.outlet = outlet;
                return this;
            }

            protected Builder<PACKET, PROCESSOR, UPS_CID, UPS_PID, UPS_PROCESSOR> addUpstreamProcessor(Driver<UPS_PROCESSOR> upstreamProcessor) {
                this.upstreamProcessor = upstreamProcessor;
                return this;
            }

            Connection<PACKET, PROCESSOR, UPS_PROCESSOR> build() {
                assert downstreamProcessor != null;
                assert upstreamProcessor != null;
                assert inletPort != null;
                assert outlet != null;
                return new Connection<>(downstreamProcessor, upstreamProcessor, inletPort, outlet);
            }

            public UPS_PID upstreamProcessorId() {
                return upstreamProcessorId;
            }
        }
    }
}
