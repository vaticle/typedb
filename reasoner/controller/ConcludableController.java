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

import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.concept.Concept;
import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.concurrent.actor.ActorExecutorGroup;
import com.vaticle.typedb.core.logic.Rule.Conclusion;
import com.vaticle.typedb.core.logic.resolvable.Concludable;
import com.vaticle.typedb.core.logic.resolvable.Unifier;
import com.vaticle.typedb.core.reasoner.computation.actor.ConnectionBuilder;
import com.vaticle.typedb.core.reasoner.computation.actor.Controller;
import com.vaticle.typedb.core.reasoner.computation.actor.Monitor;
import com.vaticle.typedb.core.reasoner.computation.actor.Processor;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.computation.reactive.provider.Source;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.FanInStream;
import com.vaticle.typedb.core.reasoner.computation.reactive.stream.FanOutStream;
import com.vaticle.typedb.core.reasoner.utils.Traversal;
import com.vaticle.typedb.core.traversal.common.Identifier.Variable;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;
import static com.vaticle.typedb.core.reasoner.computation.reactive.stream.FanInStream.fanIn;

public class ConcludableController extends Controller<ConceptMap, Map<Variable, Concept>, ConceptMap,
        ConcludableController.ConcludableProcessor, ConcludableController> {

    private final Map<Conclusion, Driver<ConclusionController>> conclusionControllers;
    private final Map<Conclusion, Set<Unifier>> conclusionUnifiers;
    private final Set<Variable.Retrievable> unboundVars;
    private final Driver<Monitor> monitor;
    private final Registry registry;
    private final Concludable concludable;

    public ConcludableController(Driver<ConcludableController> driver, Concludable concludable,
                                 ActorExecutorGroup executorService, Driver<Monitor> monitor, Registry registry) {
        super(driver, executorService, registry,
              () -> ConcludableController.class.getSimpleName() + "(pattern: " + concludable + ")");
        this.monitor = monitor;
        this.registry = registry;
        this.concludable = concludable;
        this.unboundVars = unboundVars();
        this.conclusionControllers = new HashMap<>();
        this.conclusionUnifiers = new HashMap<>();
    }

    @Override
    public void setUpUpstreamProviders() {
        concludable.getApplicableRules(registry.conceptManager(), registry.logicManager())
                .forEachRemaining(rule -> {
                    Driver<ConclusionController> controller = registry.registerConclusionController(rule.conclusion());
                    conclusionControllers.put(rule.conclusion(), controller);
                    conclusionUnifiers.put(rule.conclusion(), concludable.getUnifiers(rule).toSet());
                });
    }

    private Set<Variable.Retrievable> unboundVars() {
        Set<Variable.Retrievable> missingBounds = new HashSet<>();
        iterate(concludable.pattern().variables())
                .filter(var -> var.id().isRetrievable())
                .forEachRemaining(var -> {
                    if (var.isType() && !var.asType().label().isPresent()) {
                        missingBounds.add(var.asType().id().asRetrievable());
                    } else if (var.isThing() && !var.asThing().iid().isPresent()) {
                        missingBounds.add(var.asThing().id().asRetrievable());
                    }
                });
        return missingBounds;
    }

    @Override
    protected Function<Driver<ConcludableProcessor>, ConcludableProcessor> createProcessorFunc(ConceptMap bounds) {
        // TODO: upstreamConclusions contains *all* conclusions even if they are irrelevant for this particular
        //  concludable. They should be filtered before being passed to the concludableProcessor's constructor
        return driver -> new ConcludableProcessor(
                driver, driver(), monitor, bounds, unboundVars, conclusionUnifiers,
                () -> Traversal.traversalIterator(registry, concludable.pattern(), bounds),
                () -> ConcludableProcessor.class.getSimpleName() + "(pattern: " + concludable.pattern() + ", bounds: " + bounds + ")"
        );
    }

    private Driver<ConclusionController> conclusionProvider(Conclusion conclusion) {
        return conclusionControllers.get(conclusion);
    }

    @Override
    public ConcludableController getThis() {
        return this;
    }

    protected static class ConclusionRequest extends ProviderRequest<Conclusion, ConceptMap, Map<Variable, Concept>, ConcludableController> {

        public ConclusionRequest(Reactive.Identifier.Input<Map<Variable, Concept>> inputId,
                                 Conclusion controllerId, ConceptMap processorId) {
            super(inputId, controllerId, processorId);
        }

        @Override
        public ConnectionBuilder<ConceptMap, Map<Variable, Concept>> getConnectionBuilder(ConcludableController controller) {
            return new ConnectionBuilder<>(controller.conclusionProvider(providerControllerId()), this);
        }
    }

    protected static class ConcludableProcessor extends Processor<Map<Variable, Concept>, ConceptMap, ConcludableController, ConcludableProcessor> {

        private final ConceptMap bounds;
        private final Set<Variable.Retrievable> unboundVars;
        private final Map<Conclusion, Set<Unifier>> conclusionUnifiers;
        private final Supplier<FunctionalIterator<ConceptMap>> traversalSuppplier;
        private final Set<ConclusionRequest> requestedConnections;

        public ConcludableProcessor(Driver<ConcludableProcessor> driver, Driver<ConcludableController> controller,
                                    Driver<Monitor> monitor, ConceptMap bounds, Set<Variable.Retrievable> unboundVars,
                                    Map<Conclusion, Set<Unifier>> conclusionUnifiers,
                                    Supplier<FunctionalIterator<ConceptMap>> traversalSuppplier,
                                    Supplier<String> debugName) {
            super(driver, controller, monitor, debugName);
            this.bounds = bounds;
            this.unboundVars = unboundVars;
            this.conclusionUnifiers = conclusionUnifiers;
            this.traversalSuppplier = traversalSuppplier;
            this.requestedConnections = new HashSet<>();
        }

        @Override
        public void setUp() {
            setOutputRouter(new FanOutStream<>(this));
            FanInStream<ConceptMap> fanIn = fanIn(this);
//            boolean singleAnswerRequired = bounds.concepts().keySet().containsAll(unboundVars);
//            if (singleAnswerRequired) fanIn.findFirst().publishTo(outputRouter());
//            else fanIn.publishTo(outputRouter());
            // TODO: How do we do a find first optimisation and also know that we're done? This needs to be local to
            //  this processor because in general we couldn't call all upstream work done.
            fanIn.buffer().publishTo(outputRouter());

            Source.fromIteratorSupplier(traversalSuppplier, this).publishTo(fanIn);

            conclusionUnifiers.forEach((conclusion, unifiers) -> {
                unifiers.forEach(unifier -> unifier.unify(bounds).ifPresent(boundsAndRequirements -> {
                    Input<Map<Variable, Concept>> endpoint = this.createInput();
                    mayRequestConnection(new ConclusionRequest(endpoint.identifier(), conclusion, boundsAndRequirements.first()));
                    endpoint.flatMapOrRetry(conclusionAns -> unifier.unUnify(conclusionAns, boundsAndRequirements.second()))
                            .buffer()
                            .publishTo(fanIn);
                }));
            });
            fanIn.finaliseProviders();
        }

        private void mayRequestConnection(ConclusionRequest conclusionRequest) {
            if (!requestedConnections.contains(conclusionRequest)) {
                requestedConnections.add(conclusionRequest);
                requestProvider(conclusionRequest);
            }
        }

    }

}
