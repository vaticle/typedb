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

import com.vaticle.typedb.common.collection.Either;
import com.vaticle.typedb.core.concept.Concept;
import com.vaticle.typedb.core.concept.ConceptManager;
import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.concurrent.actor.ActorExecutorGroup;
import com.vaticle.typedb.core.logic.Rule;
import com.vaticle.typedb.core.logic.Rule.Conclusion.Materialisable;
import com.vaticle.typedb.core.logic.Rule.Conclusion.Materialisation;
import com.vaticle.typedb.core.reasoner.computation.actor.Connection;
import com.vaticle.typedb.core.reasoner.computation.actor.Connection.Builder;
import com.vaticle.typedb.core.reasoner.computation.actor.Connection.Request;
import com.vaticle.typedb.core.reasoner.computation.actor.Controller;
import com.vaticle.typedb.core.reasoner.computation.actor.Processor;
import com.vaticle.typedb.core.reasoner.resolution.ControllerRegistry;
import com.vaticle.typedb.core.traversal.common.Identifier.Variable;

import java.util.Map;
import java.util.function.Function;

import static com.vaticle.typedb.core.reasoner.computation.reactive.IdentityReactive.noOp;

public class ConclusionController extends Controller<ConceptMap, Map<Variable, Concept>,
        ConclusionController.ConclusionProcessor, ConclusionController> {
    private final Rule.Conclusion conclusion;

    protected ConclusionController(Driver<ConclusionController> driver, String name, Rule.Conclusion conclusion,
                                   ActorExecutorGroup executorService, ControllerRegistry registry) {
        super(driver, name, executorService, registry);
        this.conclusion = conclusion;
    }

    @Override
    protected Function<Driver<ConclusionProcessor>, ConclusionProcessor> createProcessorFunc(ConceptMap bounds) {
        return driver -> new ConclusionProcessor(
                driver, driver(), this.conclusion.rule(), bounds,
                ConclusionProcessor.class.getSimpleName() + "(pattern: " + conclusion + ", bounds: " + bounds + ")",
                registry().conceptManager()
        );
    }

    protected static class ConditionRequest extends Request<Rule.Condition, ConceptMap, ConditionController, Either<ConceptMap, Materialisation>, ConclusionProcessor, ConditionRequest> {

        public ConditionRequest(Driver<ConclusionProcessor> recProcessor, long recEndpointId,
                                Rule.Condition provControllerId, ConceptMap provProcessorId) {
            super(recProcessor, recEndpointId, provControllerId, provProcessorId);
        }

        @Override
        public Builder<ConceptMap, Either<ConceptMap, Materialisation>, ConditionRequest, ConclusionProcessor, ?> getBuilder(ControllerRegistry registry) {
            return createConnectionBuilder(registry.registerConditionController(pubControllerId()));
        }
    }

    protected static class MaterialiserRequest extends Connection.Request<Void, Materialisable, MaterialiserController, Either<ConceptMap, Materialisation>, ConclusionProcessor, MaterialiserRequest> {

        public MaterialiserRequest(Driver<ConclusionProcessor> recProcessor, long recEndpointId,
                                   Void provControllerId, Materialisable provProcessorId) {
            super(recProcessor, recEndpointId, provControllerId, provProcessorId);
        }

        @Override
        public Builder<Materialisable, Either<ConceptMap, Materialisation>, MaterialiserRequest, ConclusionProcessor, ?> getBuilder(ControllerRegistry registry) {
            return createConnectionBuilder(registry.materialiserController());
        }
    }

    protected static class ConclusionProcessor extends Processor<Either<ConceptMap, Materialisation>, Map<Variable, Concept>, ConclusionProcessor> {

        private final Rule rule;
        private final ConceptMap bounds;
        private final ConceptManager conceptManager;

        protected ConclusionProcessor(
                Driver<ConclusionProcessor> driver,
                Driver<? extends Controller<?, ?, ConclusionProcessor, ?>> controller, Rule rule,
                ConceptMap bounds, String name, ConceptManager conceptManager) {
            super(driver, controller, name, noOp());
            this.rule = rule;
            this.bounds = bounds;
            this.conceptManager = conceptManager;
        }

        @Override
        public void setUp() {
            InletEndpoint<Either<ConceptMap, Materialisation>> conditionEndpoint = createReceivingEndpoint();
            requestConnection(new ConditionRequest(driver(), conditionEndpoint.id(), rule.condition(), bounds));
            conditionEndpoint.forEach(ans -> {
                InletEndpoint<Either<ConceptMap, Materialisation>> materialiserEndpoint = createReceivingEndpoint();
                requestConnection(new MaterialiserRequest(
                        driver(), materialiserEndpoint.id(), null,
                        rule.conclusion().materialisable(ans.first(), conceptManager))
                );
                materialiserEndpoint.map(m -> m.second().bindToConclusion(rule.conclusion(), ans.first())).publishTo(outlet());
            });
        }
    }

}