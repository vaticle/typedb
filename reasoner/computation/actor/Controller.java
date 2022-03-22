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

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.concurrent.actor.Actor;
import com.vaticle.typedb.core.concurrent.actor.ActorExecutorGroup;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.controller.Registry;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.function.Supplier;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.RESOURCE_CLOSED;


public abstract class Controller<
        PROCESSOR_ID, INPUT, OUTPUT,
        PROCESSOR extends Processor<INPUT, OUTPUT, ?, PROCESSOR>,
        CONTROLLER extends Controller<PROCESSOR_ID, INPUT, OUTPUT, PROCESSOR, CONTROLLER>
        > extends Actor<CONTROLLER> {

    private static final Logger LOG = LoggerFactory.getLogger(Controller.class);

    private boolean terminated;
    private final ActorExecutorGroup executorService;
    private final Registry registry;
    protected final Map<PROCESSOR_ID, Actor.Driver<PROCESSOR>> processors;

    protected Controller(Driver<CONTROLLER> driver, ActorExecutorGroup executorService, Registry registry,
                         Supplier<String> debugName) {
        super(driver, debugName);
        this.executorService = executorService;
        this.processors = new HashMap<>();
        this.terminated = false;
        this.registry = registry;
    }

    public abstract void setUpUpstreamControllers();

    protected Registry registry() {
        return registry;
    }

    public <OUTPUT_CID, OUTPUT_PID, REQ extends ConnectionRequest<OUTPUT_CID, OUTPUT_PID, INPUT, CONTROLLER>> void findOutputForRequest(REQ connectionRequest) {
        if (isTerminated()) return;
        Connector<OUTPUT_PID, INPUT> connector = connectionRequest.getConnector(getThis());
        connector.outputController().execute(actor -> actor.sendConnectorToProcessor(connector));
    }

    public abstract CONTROLLER getThis();  // We need this because the processor can't access the controller actor from the driver when building a request

    public void sendConnectorToProcessor(Connector<PROCESSOR_ID, OUTPUT> connector) {
        if (isTerminated()) return;
        createProcessorIfAbsent(connector.outputProcessorId()).execute(actor -> actor.acceptConnector(connector));
    }

    public Driver<PROCESSOR> createProcessorIfAbsent(PROCESSOR_ID processorId) {
        // TODO: We can do subsumption in the subtypes here
        return processors.computeIfAbsent(processorId, this::createProcessor);
    }

    private Actor.Driver<PROCESSOR> createProcessor(PROCESSOR_ID processorId) {
        if (isTerminated()) return null;  // TODO: Avoid returning null
        Driver<PROCESSOR> processor = Actor.driver(createProcessorFunc(processorId), executorService);
        processor.execute(Processor::setUp);
        return processor;
    }

    protected abstract Function<Driver<PROCESSOR>, PROCESSOR> createProcessorFunc(PROCESSOR_ID processorId);

    @Override
    protected void exception(Throwable e) {
        if (e instanceof TypeDBException && ((TypeDBException) e).code().isPresent()) {
            String code = ((TypeDBException) e).code().get();
            if (code.equals(RESOURCE_CLOSED.code())) {
                LOG.debug("Controller interrupted by resource close: {}", e.getMessage());
                registry.terminate(e);
                return;
            } else {
                LOG.debug("Controller interrupted by TypeDB exception: {}", e.getMessage());
            }
        }
        LOG.error("Actor exception", e);
        registry.terminate(e);
    }

    public void terminate(Throwable cause) {
        LOG.debug("Actor terminated.", cause);
        this.terminated = true;
        processors.values().forEach(p -> p.execute(actor -> actor.terminate(cause)));
    }

    public boolean isTerminated() {
        return terminated;
    }

    public static abstract class ConnectionRequest<OUTPUT_CID, OUTPUT_PID, PACKET, CONTROLLER extends Controller<?, PACKET, ?, ?, CONTROLLER>> {

        private final OUTPUT_CID outputControllerId;
        private final Reactive.Identifier.Input<PACKET> inputId;
        private final OUTPUT_PID outputProcessorId;

        protected ConnectionRequest(Reactive.Identifier.Input<PACKET> inputId, OUTPUT_CID outputControllerId,
                                    OUTPUT_PID outputProcessorId) {
            this.inputId = inputId;
            this.outputControllerId = outputControllerId;
            this.outputProcessorId = outputProcessorId;
        }

        public abstract Connector<OUTPUT_PID, PACKET> getConnector(CONTROLLER controller);

        public OUTPUT_CID outputControllerId() {
            return outputControllerId;
        }

        public OUTPUT_PID outputProcessorId() {
            return outputProcessorId;
        }

        public Reactive.Identifier.Input<PACKET> inputId() {
            return inputId;
        }

        @Override
        public boolean equals(Object o) {
            // TODO: be wary with request equality when conjunctions are involved
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            ConnectionRequest<?, ?, ?, ?> request = (ConnectionRequest<?, ?, ?, ?>) o;
            return inputId == request.inputId &&
                    outputControllerId.equals(request.outputControllerId) &&
                    outputProcessorId.equals(request.outputProcessorId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(outputControllerId, inputId, outputProcessorId);
        }
    }
}
