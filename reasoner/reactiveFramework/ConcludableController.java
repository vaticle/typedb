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

package com.vaticle.typedb.core.reasoner.reactiveFramework;

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.concurrent.actor.ActorExecutorGroup;
import com.vaticle.typedb.core.logic.Rule.Conclusion;
import com.vaticle.typedb.core.logic.resolvable.Concludable;
import com.vaticle.typedb.core.logic.resolvable.Unifier;
import com.vaticle.typedb.core.pattern.Conjunction;
import com.vaticle.typedb.core.reasoner.reactiveFramework.ConclusionController.ConclusionAns;
import com.vaticle.typedb.core.reasoner.reactiveFramework.ConclusionController.ConclusionProcessor;
import com.vaticle.typedb.core.reasoner.reactiveFramework.Processor.Connection.Builder;
import com.vaticle.typedb.core.reasoner.reactive.Reactive;
import com.vaticle.typedb.core.traversal.common.Identifier;

import java.util.LinkedHashMap;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;

public class ConcludableController extends Controller<Concludable, ConceptMap, ConcludableController.ConcludableAns,
        ConcludableController.ConcludableProcessor, ConcludableController> {

    private final LinkedHashMap<Conclusion, Set<Unifier>> upstreamConclusions;
    private final Set<Identifier.Variable.Retrievable> unboundVars;

    protected ConcludableController(Driver<ConcludableController> driver, String name, Concludable id,
                                    ActorExecutorGroup executorService) {
        super(driver, name, id, executorService);
        this.upstreamConclusions = initialiseUpstreamConclusions();
        this.unboundVars = unboundVars();
    }

    private LinkedHashMap<Conclusion, Set<Unifier>> initialiseUpstreamConclusions() {
        return null;  // TODO
    }

    private Set<Identifier.Variable.Retrievable> unboundVars() {
        return null;  // TODO
    }

    @Override
    protected Function<Driver<ConcludableProcessor>, ConcludableProcessor> createProcessorFunc(ConceptMap bounds) {
        return driver -> new ConcludableProcessor(driver, driver(), "", bounds, unboundVars, upstreamConclusions,
                                                  () -> traversalIterator(id().pattern(), bounds));
    }

    private FunctionalIterator<ConceptMap> traversalIterator(Conjunction conjunction, ConceptMap bounds) {
        return null;  // TODO
    }

    @Override
    <UPS_CID, UPS_PID, PACKET,
            UPS_CONTROLLER extends Controller<UPS_CID, UPS_PID, PACKET, UPS_PROCESSOR, UPS_CONTROLLER>,
            UPS_PROCESSOR extends Processor<PACKET, UPS_PROCESSOR>> Driver<UPS_CONTROLLER> getControllerForId(UPS_CID id) {
        if (id instanceof Conclusion) {
            Driver<ConclusionController> conclusionController = null; // TODO: Fetch from registry using rule conclusion
            return (Driver<UPS_CONTROLLER>) conclusionController;  // TODO: Using instanceof requires that we do a casting.
        } else {
            throw TypeDBException.of(ILLEGAL_STATE);
        }
    }

    public static class ConcludableAns {
        public ConcludableAns(ConceptMap conceptMap) {
            // TODO
        }

        public ConceptMap conceptMap() {
            return null;  // TODO
        }
    }

    public static class ConcludableProcessor extends Processor<ConcludableAns, ConcludableProcessor> {

        public ConcludableProcessor(Driver<ConcludableProcessor> driver,
                                    Driver<ConcludableController> controller, String name,
                                    ConceptMap bounds, Set<Identifier.Variable.Retrievable> unboundVars,
                                    LinkedHashMap<Conclusion, Set<Unifier>> upstreamConclusions,
                                    Supplier<FunctionalIterator<ConceptMap>> traversalSuppplier) {
            super(driver, controller, name, new Outlet.DynamicMulti<>());

            boolean singleAnswerRequired = bounds.concepts().keySet().containsAll(unboundVars);

            Reactive<ConceptMap, ?> op = outlet().mapSubscribe(ConcludableAns::new);
            if (singleAnswerRequired) op = op.findFirstSubscribe();
            op.subscribe(Source.fromIteratorSupplier(traversalSuppplier));

            Reactive<ConceptMap, ?> finalOp = op;
            upstreamConclusions.forEach((conclusion, unifiers) -> {
                unifiers.forEach(unifier -> unifier.unify(bounds).ifPresent(boundsAndRequirements -> {
                    Reactive<ConclusionAns, ConceptMap> input = finalOp.flatMapOrRetrySubscribe(
                            conclusionAns -> unifier.unUnify(conclusionAns.concepts(), boundsAndRequirements.second()));
                    // Now we've got the reactive element that interfaces with upstream, get a connection for it to
                    // cross the actor boundary
                    Builder<ConclusionAns, ConcludableProcessor, Conclusion, ConceptMap, ConclusionProcessor> builder =
                            new Builder<>(driver(), conclusion, boundsAndRequirements.first(), input);
                    requestConnection(builder);
                }));
            });

        }
    }
}
