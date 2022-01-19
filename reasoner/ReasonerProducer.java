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
 */

package com.vaticle.typedb.core.reasoner;

import com.vaticle.typedb.core.common.parameters.Options;
import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.concurrent.executor.Executors;
import com.vaticle.typedb.core.concurrent.producer.Producer;
import com.vaticle.typedb.core.pattern.Conjunction;
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.reasoner.computation.reactive.Provider;
import com.vaticle.typedb.core.reasoner.computation.reactive.Sink;
import com.vaticle.typedb.core.reasoner.controller.Registry;
import com.vaticle.typedb.core.reasoner.utils.Tracer;
import com.vaticle.typedb.core.reasoner.utils.Tracer.Trace;
import com.vaticle.typedb.core.traversal.common.Identifier;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.annotation.concurrent.ThreadSafe;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.Executor;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;

@ThreadSafe
public class ReasonerProducer implements Producer<ConceptMap> { // TODO: Rename to MatchProducer and create abstract supertype

    private static final Logger LOG = LoggerFactory.getLogger(ReasonerProducer.class);

    private final AtomicInteger required;
    private final AtomicInteger processing;
    private final Options.Query options;
    private final Registry controllerRegistry;
    private final ExplainablesManager explainablesManager;
    private final int computeSize;
    private final EntryPoint reasonerEntryPoint;
    private boolean done;
    private Queue<ConceptMap> queue;

    // TODO: this class should not be a Producer, it implements a different async processing mechanism
    public ReasonerProducer(Conjunction conjunction, Set<Identifier.Variable.Retrievable> filter, Options.Query options,
                            Registry controllerRegistry, ExplainablesManager explainablesManager) {
        this.options = options;
        this.controllerRegistry = controllerRegistry;
        this.explainablesManager = explainablesManager;
        this.queue = null;
        this.done = false;
        this.required = new AtomicInteger();
        this.processing = new AtomicInteger();
        this.reasonerEntryPoint = new EntryPoint(this::receiveAnswer, this::exception, conjunction.toString());
        this.controllerRegistry.createRootConjunctionController(conjunction, reasonerEntryPoint);
        this.computeSize = options.parallel() ? Executors.PARALLELISATION_FACTOR * 2 : 1;
        assert computeSize > 0;
        if (options.traceInference()) Tracer.initialise(options.logsDir());
    }

    public ReasonerProducer(Disjunction disjunction, Set<Identifier.Variable.Retrievable> filter, Options.Query options,
                            Registry controllerRegistry, ExplainablesManager explainablesManager) {
        this.options = options;
        this.controllerRegistry = controllerRegistry;
        this.explainablesManager = explainablesManager;
        this.queue = null;
        this.done = false;
        this.required = new AtomicInteger();
        this.processing = new AtomicInteger();
        this.reasonerEntryPoint = new EntryPoint(this::receiveAnswer, this::exception, disjunction.toString());
        this.controllerRegistry.createRootDisjunctionController(disjunction, reasonerEntryPoint);
        this.computeSize = options.parallel() ? Executors.PARALLELISATION_FACTOR * 2 : 1;
        assert computeSize > 0;
        if (options.traceInference()) Tracer.initialise(options.logsDir());
    }

    @Override
    public synchronized void produce(Queue<ConceptMap> queue, int request, Executor executor) {
        assert this.queue == null || this.queue == queue;
        this.queue = queue;
        this.required.addAndGet(request);
        int canRequest = computeSize - processing.get();
        int toRequest = Math.min(canRequest, request);
        pullAnswer();
        processing.addAndGet(toRequest);
    }

    private void pullAnswer() {
        Tracer.get().startDefaultTrace();
        reasonerEntryPoint.pull();
    }

    private void receiveAnswer(ConceptMap answer) {
        // if (options.traceInference()) Tracer.get().finishDefaultTrace();
        if (options.explain() && !answer.explainables().isEmpty()) {
            explainablesManager.setAndRecordExplainables(answer);
        }
        queue.put(answer);
        if (required.decrementAndGet() > 0) pullAnswer();
        else processing.decrementAndGet();
    }

    // note: root resolver calls this single-threaded, so is threads safe

    private void answersFinished() {
        // TODO: Call when the end of answers has been detected
        LOG.trace("All answers found.");
        if (options.traceInference()) Tracer.get().finishDefaultTrace();
        finish();
    }

    private void finish() {
        // query is completely terminated
        done = true;
        queue.done();
        required.set(0);
    }

    private void exception(Throwable e) {
        // TODO: Should this mirror finish()?
        if (!done) {
            done = true;
            required.set(0);
            queue.done(e);
        }
    }

    @Override
    public void recycle() {

    }

    public static class EntryPoint extends Sink<ConceptMap> {

        private final Consumer<ConceptMap> answerConsumer;
        private final Consumer<Throwable> exceptionConsumer;
        private final String groupName;
        private final UUID traceId = UUID.randomUUID();
        private int traceCounter = 0;

        public EntryPoint(Consumer<ConceptMap> answerConsumer, Consumer<Throwable> exceptionConsumer, String groupName) {
            this.answerConsumer = answerConsumer;
            this.exceptionConsumer = exceptionConsumer;
            this.groupName = groupName;
        }

        @Override
        public void receive(@Nullable Provider<ConceptMap> provider, ConceptMap packet) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.receive(provider, this, packet));
            isPulling = false;
            answerConsumer.accept(packet);
        }

        @Override
        public String groupName() {
            return groupName;
        }

        public Trace trace(){
            return Trace.create(traceId, traceCounter);
        }

        public void exception(Throwable e) {
            exceptionConsumer.accept(e);
        }
    }

}
