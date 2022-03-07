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
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.reasoner.ReasonerProducer.EntryPoint;
import com.vaticle.typedb.core.reasoner.computation.actor.Monitor;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.FanInStream;
import com.vaticle.typedb.core.traversal.common.Identifier;

import java.util.Set;
import java.util.function.Function;

public class RootDisjunctionController
        extends DisjunctionController<RootDisjunctionController.RootDisjunctionProcessor, RootDisjunctionController> {
    private final Set<Identifier.Variable.Retrievable> filter;
    private final Monitor.MonitorRef monitorRef;
    private final EntryPoint reasonerEndpoint;

    public RootDisjunctionController(Driver<RootDisjunctionController> driver, Disjunction disjunction,
                                     Set<Identifier.Variable.Retrievable> filter, ActorExecutorGroup executorService,
                                     Monitor.MonitorRef monitorRef, Registry registry,
                                     EntryPoint reasonerEndpoint) {
        super(driver, disjunction, executorService, registry);
        this.filter = filter;
        this.monitorRef = monitorRef;
        this.reasonerEndpoint = reasonerEndpoint;
    }

    @Override
    protected Function<Driver<RootDisjunctionProcessor>, RootDisjunctionProcessor> createProcessorFunc(ConceptMap bounds) {
        return driver -> new RootDisjunctionProcessor(
                driver, driver(), monitorRef, disjunction, bounds, filter, reasonerEndpoint,
                RootDisjunctionProcessor.class.getSimpleName() + "(pattern:" + disjunction + ", bounds: " + bounds + ")"
        );
    }

    @Override
    public RootDisjunctionController asController() {
        return this;
    }

    @Override
    protected void exception(Throwable e) {
        super.exception(e);
        reasonerEndpoint.exception(e);
    }

    protected static class RootDisjunctionProcessor
            extends DisjunctionController.DisjunctionProcessor<RootDisjunctionController, RootDisjunctionProcessor> {

        private final Set<Identifier.Variable.Retrievable> filter;
        private final EntryPoint reasonerEntryPoint;

        protected RootDisjunctionProcessor(Driver<RootDisjunctionProcessor> driver,
                                           Driver<RootDisjunctionController> controller, Monitor.MonitorRef monitorRef, Disjunction disjunction,
                                           ConceptMap bounds, Set<Identifier.Variable.Retrievable> filter,
                                           EntryPoint reasonerEntryPoint, String name) {
            super(driver, controller, monitorRef, disjunction, bounds, name);
            this.filter = filter;
            this.reasonerEntryPoint = reasonerEntryPoint;
            monitor().registerRoot(driver(), reasonerEntryPoint);
        }

        @Override
        public void setUp() {
            super.setUp();
            outlet().publishTo(reasonerEntryPoint);
        }

        @Override
        protected Reactive.Stream<ConceptMap, ConceptMap> getOutlet(FanInStream<ConceptMap> fanIn) {
            // Simply here to be overridden by root disjuntion to avoid duplicating setUp
            return fanIn.buffer().map(conceptMap -> conceptMap.filter(filter)).deduplicate();
        }

        @Override
        protected boolean isPulling() {
            return reasonerEntryPoint.isPulling();
        }

        @Override
        protected void onFinished(Reactive.Receiver.Finishable<?> finishable) {
            assert !done;
//            done = true;
            assert finishable == reasonerEntryPoint;
            finishable.onFinished();
        }
    }
}
