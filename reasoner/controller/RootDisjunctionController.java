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
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.reasoner.ReasonerConsumer;
import com.vaticle.typedb.core.reasoner.processor.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.processor.reactive.RootSink;
import com.vaticle.typedb.core.traversal.common.Identifier;

import java.util.Set;
import java.util.function.Supplier;

public class RootDisjunctionController
        extends DisjunctionController<RootDisjunctionController.Processor, RootDisjunctionController> {

    private final Set<Identifier.Variable.Retrievable> filter;
    private final boolean explain;
    private final ReasonerConsumer<ConceptMap> reasonerConsumer;

    public RootDisjunctionController(Driver<RootDisjunctionController> driver, Disjunction disjunction,
                                     Set<Identifier.Variable.Retrievable> filter, boolean explain,
                                     Context context, ReasonerConsumer<ConceptMap> reasonerConsumer) {
        super(driver, disjunction, context);
        this.filter = filter;
        this.explain = explain;
        this.reasonerConsumer = reasonerConsumer;
    }

    @Override
    public void initialise() {
        setUpUpstreamControllers();
        getOrCreateProcessor(new ConceptMap());
    }

    @Override
    protected Processor createProcessorFromDriver(Driver<Processor> processorDriver, ConceptMap bounds) {
        return new Processor(
                processorDriver, driver(), processorContext(), disjunction, bounds, filter, explain,
                reasonerConsumer,
                () -> Processor.class.getSimpleName() + "(pattern:" + disjunction + ", bounds: " + bounds + ")"
        );
    }

    @Override
    public void terminate(Throwable cause) {
        super.terminate(cause);
        reasonerConsumer.exception(cause);
    }

    protected static class Processor extends DisjunctionController.Processor<Processor> {

        private final Set<Identifier.Variable.Retrievable> filter;
        private final boolean explain;
        private final ReasonerConsumer<ConceptMap> reasonerConsumer;
        private RootSink<ConceptMap> rootSink;

        private Processor(Driver<Processor> driver, Driver<RootDisjunctionController> controller,
                          Context context, Disjunction disjunction, ConceptMap bounds,
                          Set<Identifier.Variable.Retrievable> filter, boolean explain,
                          ReasonerConsumer<ConceptMap> reasonerConsumer, Supplier<String> debugName) {
            super(driver, controller, context, disjunction, bounds, debugName);
            this.filter = filter;
            this.explain = explain;
            this.reasonerConsumer = reasonerConsumer;
        }

        @Override
        public void setUp() {
            super.setUp();
            rootSink = new RootSink<>(this, reasonerConsumer);
            outputRouter().registerSubscriber(rootSink);
        }

        @Override
        public void rootPull() {
            rootSink.pull();
        }

        @Override
        protected Reactive.Stream<ConceptMap, ConceptMap> getOutputRouter(Reactive.Stream<ConceptMap, ConceptMap> fanIn) {
            // Simply here to be overridden by root disjuntion to avoid duplicating setUp
            Reactive.Stream<ConceptMap, ConceptMap> op = fanIn;
            if (!explain) op = op.map(conceptMap -> conceptMap.filter(filter));
            op = op.distinct();
            return op;
        }

        @Override
        public void onFinished(Reactive.Identifier finishable) {
            assert finishable == rootSink.identifier();
            rootSink.finished();
        }
    }
}
