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

package com.vaticle.typedb.core.reasoner.controller;

import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.concurrent.actor.ActorExecutorGroup;
import com.vaticle.typedb.core.logic.resolvable.Negated;
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.reasoner.computation.actor.Controller;
import com.vaticle.typedb.core.reasoner.computation.actor.Monitor;
import com.vaticle.typedb.core.reasoner.computation.actor.Processor;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.computation.reactive.receiver.ProviderRegistry;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.FanOutStream;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.SingleReceiverStream;

import java.util.function.Function;

public class NegationController extends Controller<ConceptMap, ConceptMap, ConceptMap, NegationController.NegationProcessor, NegationController> {

    private final Negated negated;
    private final Monitor.MonitorRef monitorRef;
    private Driver<NestedDisjunctionController> disjunctionContoller;

    public NegationController(Driver<NegationController> driver, Negated negated, ActorExecutorGroup executorService,
                              Monitor.MonitorRef monitorRef, Registry registry) {
        super(driver, executorService, registry, NegationController.class.getSimpleName() + "(pattern:" + negated + ")");
        this.negated = negated;
        this.monitorRef = monitorRef;
    }

    @Override
    public void setUpUpstreamProviders() {
        // TODO: If there is only one conjunction in the disjunction we could theoretically skip the disjunction, but
        //  this is architecturally difficult.
        disjunctionContoller = registry().registerNestedDisjunctionController(negated.pattern());
    }

    @Override
    protected Function<Driver<NegationProcessor>, NegationProcessor> createProcessorFunc(ConceptMap bounds) {
        return driver -> new NegationProcessor(
                driver, driver(), monitorRef, negated, bounds,
                NegationProcessor.class.getSimpleName() + "(pattern: " + negated + ", bounds: " + bounds + ")"
        );
    }

    private Driver<NestedDisjunctionController> disjunctionContoller() {
        return disjunctionContoller;
    }

    @Override
    public NegationController asController() {
        return this;
    }

    protected static class NegationProcessor extends Processor<ConceptMap, ConceptMap, NegationController, NegationProcessor> {

        private final Negated negated;
        private final ConceptMap bounds;
        private NegationReactive negation;

        protected NegationProcessor(Driver<NegationProcessor> driver, Driver<NegationController> controller,
                                    Monitor.MonitorRef monitorRef, Negated negated, ConceptMap bounds, String name) {
            super(driver, controller, monitorRef, name);
            this.negated = negated;
            this.bounds = bounds;
        }

        @Override
        protected boolean isPulling() {
            return true;  // TODO: Check this
        }

        @Override
        public void setUp() {
            setOutlet(new FanOutStream<>(monitor(), name()));
            InletEndpoint<ConceptMap> endpoint = createReceivingEndpoint();
            requestConnection(new DisjunctionRequest(driver(), endpoint.id(), negated.pattern(), bounds));
            negation = new NegationReactive(monitor(), name(), bounds);
            monitor().registerRoot(driver(), negation);
            monitor().forkFrontier(1, negation);
            endpoint.publishTo(negation);
            negation.publishTo(outlet());
        }

        @Override
        protected void onFinished(Reactive.Receiver.Finishable<?> finishable) {
            assert !done;
//            done = true;
            assert finishable == negation;
            finishable.onFinished();
        }

        private static class NegationReactive extends SingleReceiverStream<ConceptMap, ConceptMap> implements Reactive.Receiver.Finishable<ConceptMap> {

            private final ProviderRegistry.SingleProviderRegistry<ConceptMap> providerRegistry;
            private final ConceptMap bounds;
            private boolean answerFound;

            protected NegationReactive(Monitor.MonitorRef monitor, String groupName, ConceptMap bounds) {
                super(monitor, groupName);
                this.providerRegistry = new ProviderRegistry.SingleProviderRegistry<>(this, monitor);
                this.bounds = bounds;
                this.answerFound = false;
            }

            @Override
            protected ProviderRegistry<ConceptMap> providerRegistry() {
                return providerRegistry;
            }

            @Override
            public void pull(Receiver<ConceptMap> receiver) {
                if (!answerFound) super.pull(receiver);
            }

            @Override
            public void receive(Provider<ConceptMap> provider, ConceptMap packet) {
                super.receive(provider, packet);
                answerFound = true;
                monitor().rootFinalised(this);
            }

            @Override
            public void onFinished() {
                assert !answerFound;
                monitor().createAnswer(this);
                receiverRegistry().receiver().receive(this, bounds);
                monitor().rootFinalised(this);
            }
        }

        protected static class DisjunctionRequest extends Request<Disjunction, ConceptMap, NestedDisjunctionController,
                ConceptMap, NegationProcessor, NegationController, DisjunctionRequest> {

            protected DisjunctionRequest(Driver<NegationProcessor> recProcessor, long recEndpointId,
                                         Disjunction provControllerId, ConceptMap provProcessorId) {
                super(recProcessor, recEndpointId, provControllerId, provProcessorId);
            }

            @Override
            public Builder<ConceptMap, ConceptMap, DisjunctionRequest, NegationProcessor, ?> getBuilder(NegationController controller) {
                return new Builder<>(controller.disjunctionContoller(), this);
            }
        }
    }

}