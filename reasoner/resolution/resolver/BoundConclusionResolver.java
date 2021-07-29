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

package com.vaticle.typedb.core.reasoner.resolution.resolver;

import com.vaticle.typedb.common.collection.Pair;
import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.common.iterator.Iterators;
import com.vaticle.typedb.core.concept.Concept;
import com.vaticle.typedb.core.concept.ConceptManager;
import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.logic.Rule;
import com.vaticle.typedb.core.reasoner.resolution.ResolverRegistry;
import com.vaticle.typedb.core.reasoner.resolution.answer.AnswerState;
import com.vaticle.typedb.core.reasoner.resolution.answer.AnswerState.Partial.Concludable;
import com.vaticle.typedb.core.reasoner.resolution.framework.Request;
import com.vaticle.typedb.core.reasoner.resolution.framework.RequestState;
import com.vaticle.typedb.core.reasoner.resolution.framework.ResolutionTracer;
import com.vaticle.typedb.core.reasoner.resolution.framework.Resolver;
import com.vaticle.typedb.core.reasoner.resolution.framework.Response;
import com.vaticle.typedb.core.traversal.GraphTraversal;
import com.vaticle.typedb.core.traversal.TraversalEngine;
import com.vaticle.typedb.core.traversal.common.Identifier;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;

public class BoundConclusionResolver extends Resolver<BoundConclusionResolver> {

    private static final Logger LOG = LoggerFactory.getLogger(BoundConclusionResolver.class);
    private final ConceptMap bounds;
    private final Driver<ConditionResolver> conditionResolver;
    private final Rule.Conclusion conclusion;
    private final Driver<Materialiser> materialiser;
    private final Map<Request, ConclusionRequestState<? extends Concludable<?>>> requestStates;
    private final Map<Materialiser.Request, Pair<Request, Integer>> materialiserRequestRouter;

    public BoundConclusionResolver(Driver<BoundConclusionResolver> driver, Rule.Conclusion conclusion, ConceptMap bounds,
                                   Driver<ConditionResolver> conditionResolver,
                                   Driver<Materialiser> materialiser, ResolverRegistry registry, TraversalEngine traversalEngine,
                                   ConceptManager conceptMgr, boolean resolutionTracing) {
        super(driver, initName(conclusion, bounds), registry, traversalEngine, conceptMgr, resolutionTracing);
        this.bounds = bounds;
        this.conditionResolver = conditionResolver;
        this.conclusion = conclusion;
        this.materialiser = materialiser;
        this.requestStates = new HashMap<>();
        this.materialiserRequestRouter = new HashMap<>();
    }

    private static String initName(Rule.Conclusion conclusion, ConceptMap bounds) {
        return BoundConclusionResolver.class.getSimpleName() + "(pattern: " + conclusion.conjunction() + " bounds: " +
                bounds.toString() + ")";
    }

    @Override
    public void receiveRequest(Request fromUpstream, int iteration) {
        LOG.trace("{}: received Request: {}", name(), fromUpstream);
        if (isTerminated()) return;
        if (fromUpstream.isToSubsumed()) {
            assert fromUpstream.partialAnswer().conceptMap().equals(bounds);
            receiveSubsumedRequest(fromUpstream.asToSubsumed(), iteration);
        } else if (fromUpstream.isToSubsumer()) {
            receiveSubsumerRequest(fromUpstream.asToSubsumer(), iteration);
        } else {
            assert fromUpstream.partialAnswer().conceptMap().equals(bounds);
            receiveDirectRequest(fromUpstream, iteration);
        }
    }

    private void receiveSubsumedRequest(Request.ToSubsumed fromUpstream, int iteration) {
        throw TypeDBException.of(ILLEGAL_STATE);
//        RequestState requestState = requestStates.computeIfAbsent(
//                fromUpstream, request -> new BoundRequestState(request, cache, iteration));
//        if (cache.sourceExhausted()) {
//            sendAnswerOrFail(fromUpstream, iteration, requestState);
//        } else {
//            cache.clearSource();
//            Optional<? extends AnswerState.Partial<?>> upstreamAnswer;
//            upstreamAnswer = requestState.nextAnswer();
//            if (upstreamAnswer.isPresent()) {
//                answerToUpstream(upstreamAnswer.get(), fromUpstream, iteration);
//            } else {
//                requestFromSubsumer(fromUpstream, iteration);
//            }
//        }
    }

    private void receiveSubsumerRequest(Request.ToSubsumer fromUpstream, int iteration) {
        throw TypeDBException.of(ILLEGAL_STATE);
//        sendAnswerOrFail(fromUpstream, iteration, requestStates.computeIfAbsent(
//                fromUpstream, request -> new SubsumerRequestState(request, cache, iteration)));
    }

    private void receiveDirectRequest(Request fromUpstream, int iteration) {
        requestStates.computeIfAbsent(fromUpstream, r -> createRequestState(fromUpstream, iteration));
        sendAnswerOrSearchDownstreamOrFail(fromUpstream, requestStates.get(fromUpstream), iteration);
    }

    @Override
    protected void receiveAnswer(Response.Answer fromDownstream, int iteration) {
        LOG.trace("{}: received Answer: {}", name(), fromDownstream);
        if (isTerminated()) return;
        Request toDownstream = fromDownstream.sourceRequest();
        Request fromUpstream = fromUpstream(toDownstream);
        ConclusionRequestState<? extends Concludable<?>> requestState = this.requestStates.get(fromUpstream);
        if (!requestState.isComplete()) {
            Materialiser.Request request = Materialiser.Request.create(driver(), materialiser, conclusion,
                                                                       fromDownstream.answer());
            requestFromMaterialiser(request, fromUpstream, iteration);
            requestState.incrementWaiting();
        } else {
            sendAnswerOrSearchDownstreamOrFail(fromUpstream, requestState, iteration);
        }
    }

    private void requestFromMaterialiser(Materialiser.Request request, Request fromUpstream, int iteration) {
        if (resolutionTracing) ResolutionTracer.get().request(
                this.name(), request.receiver().name(), iteration,
                request.partialAnswer().conceptMap().concepts().keySet().toString());
        materialiserRequestRouter.put(request, new Pair<>(fromUpstream, iteration));
        materialiser.execute(actor -> actor.receiveRequest(request));
    }

    protected void receiveMaterialisation(Materialiser.Response response) {
        if (isTerminated()) return;
        Materialiser.Request toDownstream = response.sourceRequest();
        Pair<Request, Integer> fromUpstream = fromUpstream(toDownstream);
        ConclusionRequestState<? extends Concludable<?>> requestState = this.requestStates.get(fromUpstream.first());
        LOG.trace("{}: received materialisation response: {}", name(), response);
        Optional<Map<Identifier.Variable, Concept>> materialisation = response.materialisation();
        materialisation.ifPresent(m -> requestState.newMaterialisation(response.partialAnswer(), m));
        sendAnswerOrSearchDownstreamOrFail(fromUpstream.first(), requestState, fromUpstream.second());
        requestState.decrementWaiting();
        if (!requestState.waiting()) {
            requestState.queue().forEach(r -> sendAnswerOrSearchDownstreamOrFail(r.first(), requestState, r.second()));
            requestState.emptyQueue();
        }
    }

    protected Pair<Request, Integer> fromUpstream(Materialiser.Request toDownstream) {
        assert materialiserRequestRouter.containsKey(toDownstream);
        return materialiserRequestRouter.remove(toDownstream);
    }

    private void sendAnswerOrSearchDownstreamOrFail(Request fromUpstream, ConclusionRequestState<?> requestState, int iteration) {
        Optional<? extends AnswerState.Partial<?>> upstreamAnswer = requestState.nextAnswer();
        if (upstreamAnswer.isPresent()) {
            answerToUpstream(upstreamAnswer.get(), fromUpstream, iteration);
        } else if (!requestState.isComplete() && requestState.downstreamManager().hasDownstream()) {
            requestFromDownstream(requestState.downstreamManager().nextDownstream(), fromUpstream, iteration);
        } else if (requestState.waiting()) {
            requestState.addToQueue(fromUpstream, iteration);
        } else {
            requestState.setComplete();
            failToUpstream(fromUpstream, iteration);
        }
    }

    @Override
    protected void receiveFail(Response.Fail fromDownstream, int iteration) {
        LOG.trace("{}: received Fail: {}", name(), fromDownstream);
        if (isTerminated()) return;

        Request toDownstream = fromDownstream.sourceRequest();
        Request fromUpstream = fromUpstream(toDownstream);
        ConclusionRequestState<?> requestState = this.requestStates.get(fromUpstream);

        if (iteration < requestState.iteration()) {
            // short circuit old iteration fail messages to upstream
            failToUpstream(fromUpstream, iteration);
            return;
        }

        requestState.downstreamManager().removeDownstream(fromDownstream.sourceRequest());
        sendAnswerOrSearchDownstreamOrFail(fromUpstream, requestState, iteration);
    }

    @Override
    protected void initialiseDownstreamResolvers() {
        throw TypeDBException.of(ILLEGAL_STATE);
    }

    private ConclusionRequestState<?> createRequestState(Request fromUpstream, int iteration) {
        LOG.debug("{}: Creating a new ConclusionResponse for request: {}", name(), fromUpstream);

        ConclusionRequestState<?> requestState;
        if (fromUpstream.partialAnswer().asConclusion().isExplain()) {
            requestState = new ConclusionRequestState.Explaining(fromUpstream, iteration);
        } else if (fromUpstream.partialAnswer().asConclusion().isMatch()) {
            requestState = new ConclusionRequestState.Rule(fromUpstream, iteration);
        } else {
            throw TypeDBException.of(ILLEGAL_STATE);
        }

        assert fromUpstream.partialAnswer().isConclusion();
        AnswerState.Partial.Conclusion<?, ?> partialAnswer = fromUpstream.partialAnswer().asConclusion();
        // we do a extra traversal to expand the partial answer if we already have the concept that is meant to be generated
        // and if there's extra variables to be populated
        if (!requestState.isComplete()) {
            assert conclusion.retrievableIds().containsAll(partialAnswer.conceptMap().concepts().keySet());
            if (conclusion.generating().isPresent() && conclusion.retrievableIds().size() > partialAnswer.conceptMap().concepts().size() &&
                    partialAnswer.conceptMap().concepts().containsKey(conclusion.generating().get().id())) {
                FunctionalIterator<AnswerState.Partial.Compound<?, ?>> completedDownstreamAnswers = candidateAnswers(partialAnswer);
                completedDownstreamAnswers.forEachRemaining(answer -> requestState.downstreamManager()
                        .addDownstream(Request.create(driver(), conditionResolver, answer)));
            } else {
                Set<Identifier.Variable.Retrievable> named = iterate(conclusion.retrievableIds()).filter(Identifier::isName).toSet();
                AnswerState.Partial.Compound<?, ?> downstreamAnswer = partialAnswer.toDownstream(named);
                requestState.downstreamManager().addDownstream(Request.create(driver(), conditionResolver, downstreamAnswer));
            }
        }
        return requestState;
    }

    private FunctionalIterator<AnswerState.Partial.Compound<?, ?>> candidateAnswers(AnswerState.Partial.Conclusion<?, ?> partialAnswer) {
        GraphTraversal traversal = boundTraversal(conclusion.conjunction().traversal(), partialAnswer.conceptMap());
        FunctionalIterator<ConceptMap> answers = traversalEngine.iterator(traversal).map(conceptMgr::conceptMap);
        Set<Identifier.Variable.Retrievable> named = iterate(conclusion.retrievableIds()).filter(Identifier::isName).toSet();
        return answers.map(ans -> partialAnswer.extend(ans).toDownstream(named));
    }

    private static abstract class ConclusionRequestState<CONCLUDABLE extends Concludable<?>> extends RequestState {

        private final DownstreamManager downstreamManager;
        protected FunctionalIterator<CONCLUDABLE> materialisation;
        private boolean complete;
        private int waiting;
        private final List<Pair<Request, Integer>> queue; // TODO: Will always be the same request, so can just hold an int instead

        protected ConclusionRequestState(Request fromUpstream, int iteration) {
            super(fromUpstream, iteration);
            this.downstreamManager = new DownstreamManager();
            this.materialisation = Iterators.empty();
            this.complete = false;
            this.waiting = 0;
            this.queue = new ArrayList<>();
        }

        public DownstreamManager downstreamManager() {
            return downstreamManager;
        }

        public boolean isComplete() {
            // TODO: Placeholder for re-introducing caching
            return complete;
        }

        public void setComplete() {
            // TODO: Placeholder for re-introducing caching. Should only be used once Conclusion caching works in
            //  recursive settings
            complete = true;
        }

        protected abstract FunctionalIterator<CONCLUDABLE> toUpstream(AnswerState.Partial<?> fromDownstream,
                                                                      Map<Identifier.Variable, Concept> answer);

        public void newMaterialisation(AnswerState.Partial<?> fromDownstream,
                                       Map<Identifier.Variable, Concept> materialisation) {
            this.materialisation = this.materialisation.link(toUpstream(fromDownstream, materialisation));
        }

        public boolean waiting() {
            return waiting > 0;
        }

        public void addToQueue(Request fromUpstream, int iteration) {
            queue.add(new Pair<>(fromUpstream, iteration));
        }

        public List<Pair<Request, Integer>> queue() {
            return queue;
        }

        public void emptyQueue() {
            queue.clear();
        }

        public void incrementWaiting() {
            waiting += 1;
        }

        public void decrementWaiting() {
            waiting -= 1;
        }

        private static class Rule extends ConclusionRequestState<Concludable.Match<?>> {

            private final Set<ConceptMap> deduplicationSet;

            public Rule(Request fromUpstream, int iteration) {
                super(fromUpstream, iteration);
                this.deduplicationSet = new HashSet<>();
            }

            @Override
            protected FunctionalIterator<Concludable.Match<?>> toUpstream(AnswerState.Partial<?> fromDownstream,
                                                                          Map<Identifier.Variable, Concept> answer) {
                return fromDownstream.asConclusion().asMatch().aggregateToUpstream(answer);
            }

            @Override
            public Optional<Concludable.Match<?>> nextAnswer() {
                // TODO Clean up now that materialisations aren't an iterator
                if (!materialisation.hasNext()) return Optional.empty();
                while (materialisation.hasNext()) {
                    Concludable.Match<?> ans = materialisation.next();
                    if (!deduplicationSet.contains(ans.conceptMap())) {
                        deduplicationSet.add(ans.conceptMap());
                        return Optional.of(ans);
                    }
                }
                return Optional.empty();
            }

        }

        private static class Explaining extends ConclusionRequestState<Concludable.Explain> {

            public Explaining(Request fromUpstream, int iteration) {
                super(fromUpstream, iteration);
            }

            @Override
            protected FunctionalIterator<Concludable.Explain> toUpstream(AnswerState.Partial<?> fromDownstream,
                                                                         Map<Identifier.Variable, Concept> answer) {
                return fromDownstream.asConclusion().asExplain().aggregateToUpstream(answer);
            }

            @Override
            public Optional<Concludable.Explain> nextAnswer() {
                if (!materialisation.hasNext()) return Optional.empty();
                return Optional.of(materialisation.next());
            }
        }
    }
}
