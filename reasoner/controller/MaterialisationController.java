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
import com.vaticle.typedb.core.common.iterator.Iterators;
import com.vaticle.typedb.core.concept.ConceptManager;
import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.logic.Materialiser;
import com.vaticle.typedb.core.logic.Materialiser.Materialisation;
import com.vaticle.typedb.core.logic.Rule.Conclusion.Materialisable;
import com.vaticle.typedb.core.reasoner.reactive.AbstractReactiveBlock;
import com.vaticle.typedb.core.reasoner.reactive.AbstractReactiveBlock.Connector.AbstractRequest;
import com.vaticle.typedb.core.reasoner.reactive.PoolingStream;
import com.vaticle.typedb.core.reasoner.reactive.Source;
import com.vaticle.typedb.core.reasoner.reactive.common.Operator;
import com.vaticle.typedb.core.traversal.TraversalEngine;

import java.util.function.Supplier;

public class MaterialisationController extends AbstractController<
        Materialisable,
        Void,
        Either<ConceptMap, Materialisation>,
        AbstractRequest<?, ?, Void>,
        MaterialisationController.ReactiveBlock,
        MaterialisationController
        > {
    // Either<> is just to match the input to ConclusionController, but this class only ever returns Materialisation

    private final ConceptManager conceptMgr;
    private final TraversalEngine traversalEng;

    public MaterialisationController(Driver<MaterialisationController> driver, Context context,
                                     TraversalEngine traversalEng, ConceptManager conceptMgr) {
        super(driver, context, MaterialisationController.class::getSimpleName);
        this.traversalEng = traversalEng;
        this.conceptMgr = conceptMgr;
    }

    @Override
    public void setUpUpstreamControllers() {
        // None to set up
    }

    @Override
    protected ReactiveBlock createReactiveBlockFromDriver(
            Driver<ReactiveBlock> reactiveBlockDriver, Materialisable materialisable
    ) {
        return new ReactiveBlock(
                reactiveBlockDriver, driver(), reactiveBlockContext(), materialisable, traversalEng, conceptMgr,
                () -> ReactiveBlock.class.getSimpleName() + "(Materialisable: " + materialisable + ")"
        );
    }

    @Override
    public void resolveController(AbstractRequest<?, ?, Void> connectionRequest) {
        // Nothing to do
    }

    public static class ReactiveBlock extends AbstractReactiveBlock<Void, Either<ConceptMap, Materialisation>,
            AbstractRequest<?, ?, Void>, ReactiveBlock> {

        private final Materialisable materialisable;
        private final TraversalEngine traversalEng;
        private final ConceptManager conceptMgr;

        protected ReactiveBlock(Driver<ReactiveBlock> driver, Driver<MaterialisationController> controller,
                                Context context, Materialisable materialisable, TraversalEngine traversalEng,
                                ConceptManager conceptMgr, Supplier<String> debugName) {
            super(driver, controller, context, debugName);
            this.materialisable = materialisable;
            this.traversalEng = traversalEng;
            this.conceptMgr = conceptMgr;
        }

        @Override
        public void setUp() {
            setOutputRouter(PoolingStream.fanOut(this));
            Source.create(this, new Operator.Supplier<>(
                    () -> Materialiser.materialise(materialisable, traversalEng, conceptMgr)
                            .map(Iterators::single)
                            .orElse(Iterators.empty()))
            ).map(Either::<ConceptMap, Materialisation>second).registerSubscriber(outputRouter());
        }
    }
}
