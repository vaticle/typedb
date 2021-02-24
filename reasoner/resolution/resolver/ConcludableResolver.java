/*
 * Copyright (C) 2021 Grakn Labs
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

package grakn.core.reasoner.resolution.resolver;

import grakn.core.common.exception.GraknCheckedException;
import grakn.core.common.iterator.ResourceIterator;
import grakn.core.concept.ConceptManager;
import grakn.core.concept.answer.ConceptMap;
import grakn.core.concurrent.actor.Actor;
import grakn.core.logic.LogicManager;
import grakn.core.logic.resolvable.Concludable;
import grakn.core.logic.resolvable.Unifier;
import grakn.core.reasoner.resolution.ResolutionRecorder;
import grakn.core.reasoner.resolution.ResolverRegistry;
import grakn.core.reasoner.resolution.answer.AnswerState.Partial;
import grakn.core.reasoner.resolution.answer.AnswerState.Partial.Unified;
import grakn.core.reasoner.resolution.framework.Request;
import grakn.core.reasoner.resolution.framework.Resolver;
import grakn.core.reasoner.resolution.framework.Response;
import grakn.core.reasoner.resolution.framework.Response.Answer;
import grakn.core.traversal.TraversalEngine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

public class ConcludableResolver extends Resolver<ConcludableResolver> {
    private static final Logger LOG = LoggerFactory.getLogger(ConcludableResolver.class);

    private final LinkedHashMap<Actor<ConclusionResolver>, Set<Unifier>> applicableRules;
    private final Concludable concludable;
    private final LogicManager logicMgr;
    private final Map<Actor<? extends Resolver<?>>, RecursionState> recursionStates;
    private final Actor<ResolutionRecorder> resolutionRecorder;
    private final Map<Request, Responses> responses;
    private boolean isInitialised;

    public ConcludableResolver(Actor<ConcludableResolver> self, Concludable concludable,
                               Actor<ResolutionRecorder> resolutionRecorder, ResolverRegistry registry,
                               TraversalEngine traversalEngine, ConceptManager conceptMgr, LogicManager logicMgr,
                               boolean resolutionTracing) {
        super(self, ConcludableResolver.class.getSimpleName() + "(pattern: " + concludable.pattern() + ")",
              registry, traversalEngine, conceptMgr, resolutionTracing);
        this.logicMgr = logicMgr;
        this.resolutionRecorder = resolutionRecorder;
        this.concludable = concludable;
        this.applicableRules = new LinkedHashMap<>();
        this.recursionStates = new HashMap<>();
        this.responses = new HashMap<>();
        this.isInitialised = false;
    }

    @Override
    public void receiveRequest(Request fromUpstream, int iteration) {
        LOG.trace("{}: received Request: {}", name(), fromUpstream);
        if (!isInitialised) initialiseDownstreamResolvers();
        if (isTerminated()) return;

        Responses responses = getOrUpdateResponses(fromUpstream, iteration);
        if (iteration < responses.iteration()) {
            // short circuit if the request came from a prior iteration
            failToUpstream(fromUpstream, iteration);
        } else {
            assert iteration == responses.iteration();
            nextAnswer(fromUpstream, responses, iteration);
        }
    }

    @Override
    protected void receiveAnswer(Answer fromDownstream, int iteration) {
        LOG.trace("{}: received Answer: {}", name(), fromDownstream);
        if (isTerminated()) return;

        Request toDownstream = fromDownstream.sourceRequest();
        Request fromUpstream = fromUpstream(toDownstream);
        Responses responses = this.responses.get(fromUpstream);

        Partial<?> upstreamAnswer = fromDownstream.answer().asMapped().toUpstream();

        if (!responses.hasProduced(upstreamAnswer.conceptMap())) {
            responses.recordProduced(upstreamAnswer.conceptMap());
            answerToUpstream(upstreamAnswer, fromUpstream, iteration);
        } else {
            if (fromDownstream.answer().recordExplanations()) {
                LOG.trace("{}: Recording deduplicated answer derivation: {}", name(), upstreamAnswer);
                resolutionRecorder.tell(actor -> actor.record(upstreamAnswer));
            }
            nextAnswer(fromUpstream, responses, iteration);
        }
    }

    @Override
    protected void receiveFail(Response.Fail fromDownstream, int iteration) {
        LOG.trace("{}: received Fail: {}", name(), fromDownstream);
        if (isTerminated()) return;

        Request toDownstream = fromDownstream.sourceRequest();
        Request fromUpstream = fromUpstream(toDownstream);
        Responses responses = this.responses.get(fromUpstream);

        if (iteration < responses.iteration()) {
            // short circuit old iteration failed messages to upstream
            failToUpstream(fromUpstream, iteration);
            return;
        }

        responses.removeDownstreamProducer(fromDownstream.sourceRequest());
        nextAnswer(fromUpstream, responses, iteration);
    }

    @Override
    public void terminate(Throwable cause) {
        super.terminate(cause);
        responses.clear();
        recursionStates.clear();
    }

    @Override
    protected void initialiseDownstreamResolvers() {
        LOG.debug("{}: initialising downstream resolvers", name());
        concludable.getApplicableRules(conceptMgr, logicMgr).forEachRemaining(rule -> concludable.getUnifiers(rule)
                .forEachRemaining(unifier -> {
                    if (isTerminated()) return;
                    Actor<ConclusionResolver> conclusionResolver = null;
                    try {
                        conclusionResolver = registry.registerConclusion(rule.conclusion());
                        applicableRules.putIfAbsent(conclusionResolver, new HashSet<>());
                        applicableRules.get(conclusionResolver).add(unifier);
                    } catch (GraknCheckedException e) {
                        terminate(e);
                    }
                }));
        if (!isTerminated()) isInitialised = true;
    }

    private void nextAnswer(Request fromUpstream, Responses responses, int iteration) {
        if (responses.hasUpstreamAnswer()) {
            Partial<?> upstreamAnswer = responses.upstreamAnswers().next();
            responses.recordProduced(upstreamAnswer.conceptMap());
            answerToUpstream(upstreamAnswer, fromUpstream, iteration);
        } else {
            if (responses.hasDownstreamProducer()) {
                requestFromDownstream(responses.nextDownstreamProducer(), fromUpstream, iteration);
            } else {
                failToUpstream(fromUpstream, iteration);
            }
        }
    }

    private Responses getOrUpdateResponses(Request fromUpstream, int iteration) {
        if (!responses.containsKey(fromUpstream)) {
            responses.put(fromUpstream, responsesCreate(fromUpstream, iteration));
        } else {
            Responses responses = this.responses.get(fromUpstream);
            assert responses.iteration() == iteration || responses.iteration() + 1 == iteration;

            if (responses.iteration() + 1 == iteration) {
                // when the same request for the next iteration the first time, re-initialise required state
                Responses newResponses = responsesCreate(fromUpstream, iteration);
                this.responses.put(fromUpstream, newResponses);
            }
        }
        return responses.get(fromUpstream);
    }

    protected Responses responsesCreate(Request fromUpstream, int iteration) {
        LOG.debug("{}: Creating new Responses for iteration{}, request: {}", name(), iteration, fromUpstream);
        Actor<? extends Resolver<?>> root = fromUpstream.partialAnswer().root();
        recursionStates.putIfAbsent(root, new RecursionState(iteration));
        RecursionState iterationState = recursionStates.get(root);
        if (iterationState.iteration() < iteration) {
            iterationState.nextIteration(iteration);
        }

        assert fromUpstream.partialAnswer().isMapped();
        ResourceIterator<Partial<?>> upstreamAnswers =
                traversalIterator(concludable.pattern(), fromUpstream.partialAnswer().conceptMap())
                        .map(conceptMap -> fromUpstream.partialAnswer().asMapped().aggregateToUpstream(conceptMap));

        Responses responses = new Responses(upstreamAnswers, iteration);
        mayRegisterRules(fromUpstream, iterationState, responses);
        return responses;
    }

    private void mayRegisterRules(Request fromUpstream, RecursionState recursionState, Responses responses) {
        // loop termination: when receiving a new request, we check if we have seen it before from this root query
        // if we have, we do not allow rules to be registered as possible downstreams
        if (!recursionState.hasReceived(fromUpstream.partialAnswer().conceptMap())) {
            for (Map.Entry<Actor<ConclusionResolver>, Set<Unifier>> entry : applicableRules.entrySet()) {
                Actor<ConclusionResolver> conclusionResolver = entry.getKey();
                for (Unifier unifier : entry.getValue()) {
                    Optional<Unified> unified = fromUpstream.partialAnswer().unifyToDownstream(unifier, conclusionResolver);
                    if (unified.isPresent()) {
                        Request toDownstream = Request.create(self(), conclusionResolver, unified.get());
                        responses.addDownstreamProducer(toDownstream);
                    }
                }
            }
            recursionState.recordReceived(fromUpstream.partialAnswer().conceptMap());
        }
    }

    private static class Responses {
        private final Set<ConceptMap> produced;
        private final ResourceIterator<Partial<?>> newUpstreamAnswers;
        private final LinkedHashSet<Request> downstreamProducer;
        private final int iteration;
        private Iterator<Request> downstreamProducerSelector;

        public Responses(ResourceIterator<Partial<?>> upstreamAnswers, int iteration) {
            this(upstreamAnswers, iteration, new HashSet<>());
        }

        private Responses(ResourceIterator<Partial<?>> upstreamAnswers, int iteration, Set<ConceptMap> produced) {
            this.newUpstreamAnswers = upstreamAnswers.filter(partial -> !hasProduced(partial.conceptMap()));
            this.iteration = iteration;
            this.produced = produced;
            downstreamProducer = new LinkedHashSet<>();
            downstreamProducerSelector = downstreamProducer.iterator();
        }

        public void recordProduced(ConceptMap conceptMap) {
            produced.add(conceptMap);
        }

        public boolean hasProduced(ConceptMap conceptMap) {
            return produced.contains(conceptMap);
        }

        public boolean hasUpstreamAnswer() {
            return newUpstreamAnswers.hasNext();
        }

        public ResourceIterator<Partial<?>> upstreamAnswers() {
            return newUpstreamAnswers;
        }

        public boolean hasDownstreamProducer() {
            return !downstreamProducer.isEmpty();
        }

        public Request nextDownstreamProducer() {
            if (!downstreamProducerSelector.hasNext()) downstreamProducerSelector = downstreamProducer.iterator();
            return downstreamProducerSelector.next();
        }

        public void addDownstreamProducer(Request request) {
            assert !(downstreamProducer.contains(request)) : "downstream answer producer already contains this request";

            downstreamProducer.add(request);
            downstreamProducerSelector = downstreamProducer.iterator();
        }

        public void removeDownstreamProducer(Request request) {
            boolean removed = downstreamProducer.remove(request);
            // only update the iterator when removing an element, to avoid resetting and reusing first request too often
            // note: this is a large performance win when processing large batches of requests
            if (removed) downstreamProducerSelector = downstreamProducer.iterator();
        }

        public int iteration() {
            return iteration;
        }

    }

    /**
     * Maintain iteration state per root query
     * This allows us to share resolvers across different queries
     * while maintaining the ability to do loop termination within a single query
     */
    private static class RecursionState {
        private Set<ConceptMap> receivedMaps;
        private int iteration;

        RecursionState(int iteration) {
            this.iteration = iteration;
            this.receivedMaps = new HashSet<>();
        }

        public int iteration() {
            return iteration;
        }

        public void nextIteration(int newIteration) {
            assert newIteration > iteration;
            iteration = newIteration;
            receivedMaps = new HashSet<>();
        }

        public void recordReceived(ConceptMap conceptMap) {
            receivedMaps.add(conceptMap);
        }

        public boolean hasReceived(ConceptMap conceptMap) {
            return receivedMaps.contains(conceptMap);
        }
    }
}

