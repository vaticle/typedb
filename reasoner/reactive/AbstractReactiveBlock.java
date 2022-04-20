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

package com.vaticle.typedb.core.reasoner.reactive;

import com.vaticle.typedb.common.collection.Pair;
import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.concurrent.actor.Actor;
import com.vaticle.typedb.core.reasoner.controller.AbstractController;
import com.vaticle.typedb.core.reasoner.reactive.Reactive.Identifier;
import com.vaticle.typedb.core.reasoner.reactive.Reactive.Publisher;
import com.vaticle.typedb.core.reasoner.reactive.Reactive.Subscriber;
import com.vaticle.typedb.core.reasoner.reactive.common.ReactiveIdentifier;
import com.vaticle.typedb.core.reasoner.utils.Tracer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.function.Supplier;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_OPERATION;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.RESOURCE_CLOSED;

public abstract class AbstractReactiveBlock<INPUT, OUTPUT,
        REQ extends AbstractReactiveBlock.Connector.AbstractRequest<?, ?, INPUT>,
        REACTIVE_BLOCK extends AbstractReactiveBlock<INPUT, OUTPUT, REQ, REACTIVE_BLOCK>> extends Actor<REACTIVE_BLOCK> {

    private static final Logger LOG = LoggerFactory.getLogger(AbstractReactiveBlock.class);

    private final Driver<? extends AbstractController<?, INPUT, OUTPUT, REQ, REACTIVE_BLOCK, ?>> controller;
    private final Map<Identifier<?, ?>, Input<INPUT>> inputs;
    private final Map<Identifier<?, ?>, Output<OUTPUT>> outputs;
    private final Map<Pair<Identifier<?, ?>, Identifier<?, ?>>, Runnable> pullRetries;
    private final Driver<Monitor> monitor;
    private Reactive.Stream<OUTPUT,OUTPUT> outputRouter;
    private boolean terminated;
    protected boolean done;
    private long reactiveCounter;

    protected AbstractReactiveBlock(Driver<REACTIVE_BLOCK> driver,
                                    Driver<? extends AbstractController<?, INPUT, OUTPUT, REQ, REACTIVE_BLOCK, ?>> controller,
                                    Driver<Monitor> monitor,
                                    Supplier<String> debugName) {
        super(driver, debugName);
        this.controller = controller;
        this.inputs = new HashMap<>();
        this.outputs = new HashMap<>();
        this.done = false;
        this.monitor = monitor;
        this.reactiveCounter = 0;
        this.pullRetries = new HashMap<>();
    }

    public abstract void setUp();

    protected void setOutputRouter(Reactive.Stream<OUTPUT, OUTPUT> outputRouter) {
        this.outputRouter = outputRouter;
    }

    public Reactive.Stream<OUTPUT,OUTPUT> outputRouter() {
        return outputRouter;
    }

    public void rootPull() {
        throw TypeDBException.of(ILLEGAL_OPERATION);
    }

    public void pull(Identifier<?, ?> outputId) {
        assert !done;
        outputs.get(outputId).pull();
    }

    public void receive(Identifier<?, INPUT> publisherId, INPUT input, Identifier<?, ?> inputId) {
        assert !done;
        inputs.get(inputId).receive(publisherId, input);
    }

    public <PACKET> void schedulePullRetry(Publisher<PACKET> publisher, Subscriber<PACKET> subscriber) {
        pullRetries.put(new Pair<>(publisher.identifier(), subscriber.identifier()), () -> publisher.pull(subscriber));
        driver().execute(actor -> actor.pullRetry(publisher.identifier(), subscriber.identifier()));
    }

    protected void pullRetry(Identifier<?, ?> publisher, Identifier<?, ?> subscriber) {
        Tracer.getIfEnabled().ifPresent(tracer -> tracer.pullRetry(subscriber, publisher));
        pullRetries.get(new Pair<Identifier<?, ?>, Identifier<?, ?>>(publisher, subscriber)).run();
    }

    protected void requestConnection(REQ req) {
        assert !done;
        if (isTerminated()) return;
        controller.execute(actor -> actor.resolveController(req));
    }

    public void establishConnection(Connector<?, OUTPUT> connector) {
        assert !done;
        if (isTerminated()) return;
        Output<OUTPUT> output = createOutput();
        output.setSubscriber(connector.inputId());
        connector.connectViaTransforms(outputRouter(), output);
        connector.inputId().reactiveBlock().execute(
                actor -> actor.finishConnection(connector.inputId(), output.identifier()));
    }

    protected void finishConnection(Identifier<INPUT, ?> inputId, Identifier<?, INPUT> outputId) {
        assert !done;
        Input<INPUT> input = inputs.get(inputId);
        input.setOutput(outputId);
        input.pull();
    }

    protected Input<INPUT> createInput() {
        assert !done;
        Input<INPUT> input = new Input<>(this);
        inputs.put(input.identifier(), input);
        return input;
    }

    protected Output<OUTPUT> createOutput() {
        assert !done;
        Output<OUTPUT> output = new Output<>(this);
        outputs.put(output.identifier(), output);
        return output;
    }

    public Driver<Monitor> monitor() {
        return monitor;
    }

    public void onFinished(Identifier<?, ?> finishable) {
        throw TypeDBException.of(ILLEGAL_STATE);
    }

    @Override
    protected void exception(Throwable e) {
        if (e instanceof TypeDBException && ((TypeDBException) e).code().isPresent()) {
            String code = ((TypeDBException) e).code().get();
            if (code.equals(RESOURCE_CLOSED.code())) {
                LOG.debug("ReactiveBlock interrupted by resource close: {}", e.getMessage());
                controller.execute(actor -> actor.exception(e));
                return;
            } else {
                LOG.debug("ReactiveBlock interrupted by TypeDB exception: {}", e.getMessage());
            }
        }
        LOG.error("Actor exception", e);
        controller.execute(actor -> actor.exception(e));
    }

    public void terminate(Throwable cause) {
        LOG.debug("Actor terminated.", cause);
        this.terminated = true;
    }

    public boolean isTerminated() {
        return terminated;
    }

    public long incrementReactiveCounter() {
        reactiveCounter += 1;
        return reactiveCounter;
    }

    public Identifier<INPUT, OUTPUT> registerReactive(Reactive reactive) {
        return new ReactiveIdentifier<>(driver(), reactive, incrementReactiveCounter());
    }

    public static class Connector<BOUNDS, PACKET> {

        private final Identifier<PACKET, ?> inputId;
        private final List<Function<PACKET, PACKET>> transforms;
        private final BOUNDS bounds;

        public Connector(Identifier<PACKET, ?> inputId, BOUNDS bounds) {
            this.inputId = inputId;
            this.transforms = new ArrayList<>();
            this.bounds = bounds;
        }

        public Connector(Identifier<PACKET, ?> inputId, BOUNDS bounds, List<Function<PACKET, PACKET>> transforms) {
            this.inputId = inputId;
            this.transforms = transforms;
            this.bounds = bounds;
        }

        public void connectViaTransforms(Reactive.Stream<PACKET, PACKET> toConnect, Output<PACKET> output) {
            Publisher<PACKET> op = toConnect;
            for (Function<PACKET, PACKET> t : transforms) op = op.map(t);
            op.registerSubscriber(output);
        }

        public BOUNDS bounds(){
            return bounds;
        }

        public Identifier<PACKET, ?> inputId() {
            return inputId;
        }

        public Connector<BOUNDS, PACKET> withMap(Function<PACKET, PACKET> function) {
            ArrayList<Function<PACKET, PACKET>> newTransforms = new ArrayList<>(transforms);
            newTransforms.add(function);
            return new Connector<>(inputId, bounds, newTransforms);
        }

        public Connector<BOUNDS, PACKET> withNewBounds(BOUNDS newBounds) {
            return new Connector<>(inputId, newBounds, transforms);
        }

        public abstract static class AbstractRequest<CONTROLLER_ID, BOUNDS, PACKET> {

            private final CONTROLLER_ID controllerId;
            private final BOUNDS bounds;
            private final Identifier<PACKET, ?> inputId;

            protected AbstractRequest(Identifier<PACKET, ?> inputId, CONTROLLER_ID controllerId,
                                      BOUNDS bounds) {
                this.inputId = inputId;
                this.controllerId = controllerId;
                this.bounds = bounds;
            }

            public Identifier<PACKET, ?> inputId() {
                return inputId;
            }

            public CONTROLLER_ID controllerId() {
                return controllerId;
            }

            public BOUNDS bounds() {
                return bounds;
            }

            @Override
            public boolean equals(Object o) {
                // TODO: be wary with request equality when conjunctions are involved
                if (this == o) return true;
                if (o == null || getClass() != o.getClass()) return false;
                AbstractRequest<?, ?, ?> request = (AbstractRequest<?, ?, ?>) o;
                return inputId == request.inputId &&
                        controllerId.equals(request.controllerId) &&
                        bounds.equals(request.bounds);
            }

            @Override
            public int hashCode() {
                return Objects.hash(controllerId, inputId, bounds);
            }

        }
    }
}