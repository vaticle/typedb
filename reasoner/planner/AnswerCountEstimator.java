/*
 * Copyright (C) 2022 Vaticle
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
package com.vaticle.typedb.core.reasoner.planner;

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.common.parameters.Label;
import com.vaticle.typedb.core.graph.GraphManager;
import com.vaticle.typedb.core.logic.LogicManager;
import com.vaticle.typedb.core.logic.Rule;
import com.vaticle.typedb.core.logic.resolvable.Concludable;
import com.vaticle.typedb.core.logic.resolvable.Resolvable;
import com.vaticle.typedb.core.logic.resolvable.ResolvableConjunction;
import com.vaticle.typedb.core.logic.resolvable.Unifier;
import com.vaticle.typedb.core.pattern.constraint.thing.RelationConstraint;
import com.vaticle.typedb.core.pattern.variable.ThingVariable;
import com.vaticle.typedb.core.pattern.variable.TypeVariable;
import com.vaticle.typedb.core.pattern.variable.Variable;
import com.vaticle.typedb.core.traversal.common.Identifier;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.vaticle.typedb.common.collection.Collections.list;
import static com.vaticle.typedb.common.collection.Collections.set;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;

public class AnswerCountEstimator {
    private final LogicManager logicMgr;
    private final Map<ResolvableConjunction, ConjunctionAnswerCountEstimator> estimators;

    // Cycle handling
    private final ArrayList<ResolvableConjunction> initializationStack;
    private final Set<ResolvableConjunction> cycleHeads;
    private final Set<ResolvableConjunction> toReset;
    private final AnswerCountModel answerCountModel;

    public AnswerCountEstimator(LogicManager logicMgr, GraphManager graph) {
        this.logicMgr = logicMgr;
        this.answerCountModel = new AnswerCountModel(this, graph);
        this.estimators = new HashMap<>();
        this.initializationStack = new ArrayList<>();
        this.cycleHeads = new HashSet<>();
        this.toReset = new HashSet<>();
    }

    public long estimateAllAnswers(ResolvableConjunction conjunction) {
        registerAndInitializeConjunction(conjunction);
        return estimators.get(conjunction).estimateAllAnswers();
    }

    public long estimateAnswers(ResolvableConjunction conjunction, Set<Variable> variableFilter) {
        return estimateAnswers(conjunction, variableFilter, logicMgr.compile(conjunction));
    }

    public long estimateAnswers(ResolvableConjunction conjunction, Set<Variable> variableFilter, Set<Resolvable<?>> includedResolvables) {
        registerAndInitializeConjunction(conjunction);
        return estimators.get(conjunction).estimateAnswers(variableFilter, includedResolvables);
    }

    private void registerAndInitializeConjunction(ResolvableConjunction conjunction) {
        if (!estimators.containsKey(conjunction)) {
            estimators.put(conjunction, new ConjunctionAnswerCountEstimator(this, conjunction));
        }

        if (estimators.get(conjunction).needsPreparation()) {
            initializationStack.add(conjunction);
            estimators.get(conjunction).initializeLocalEstimates();
            assert initializationStack.get(initializationStack.size() - 1) == conjunction;
            initializationStack.remove(initializationStack.size() - 1);

            if (cycleHeads.size() == 1 && cycleHeads.contains(conjunction)) {
                // Reset all cyclic paths
                for (ResolvableConjunction conjunctionToReset : toReset) {
                    estimators.get(conjunctionToReset).reset();
                }
            }
        }
    }

    private void reportInitializationCycle(ResolvableConjunction conjunction) {
        cycleHeads.add(conjunction);
        for (int i = initializationStack.size() - 1; initializationStack.get(i) != conjunction; i--) {
            toReset.add(initializationStack.get(i));
        }
    }

    private static class ConjunctionAnswerCountEstimator {

        private final ResolvableConjunction conjunction;
        private final AnswerCountEstimator answerCountEstimator;
        private final LogicManager logicMgr;
        private final AnswerCountModel answerCountModel;
        private Map<Variable, LocalEstimate> unaryEstimateCover;
        private Map<Resolvable<?>, List<LocalEstimate>> retrievableEstimates;
        private Map<Resolvable<?>, LocalEstimate> inferrableEstimates;
        private Map<Resolvable<?>, LocalEstimate> unaryEstimates;

        private long fullAnswerCount;
        private long negatedsCost;

        private enum InitializationStatus {NOT_STARTED, RESET, IN_PROGRESS, COMPLETE}

        private InitializationStatus initializationStatus;

        public ConjunctionAnswerCountEstimator(AnswerCountEstimator answerCountEstimator, ResolvableConjunction conjunction) {
            this.answerCountEstimator = answerCountEstimator;
            this.answerCountModel = answerCountEstimator.answerCountModel;
            this.logicMgr = answerCountEstimator.logicMgr;
            this.conjunction = conjunction;
            this.fullAnswerCount = -1;
            this.negatedsCost = -1;
            this.initializationStatus = InitializationStatus.NOT_STARTED;
        }

        private FunctionalIterator<Resolvable<?>> resolvables() {
            return iterate(logicMgr.compile(conjunction));
        }

        private Set<Variable> allVariables() {
            return iterate(conjunction.pattern().variables())
                    .filter(Variable::isThing)
                    .toSet();
        }

        private List<LocalEstimate> estimatesFromResolvable(Resolvable<?> resolvable) {
            List<LocalEstimate> results = new ArrayList<>();
            assert retrievableEstimates != null;
            assert inferrableEstimates != null || this.initializationStatus == InitializationStatus.IN_PROGRESS || this.initializationStatus == InitializationStatus.RESET;

            if (retrievableEstimates.containsKey(resolvable)) results.addAll(retrievableEstimates.get(resolvable));
            if (unaryEstimates != null && unaryEstimates.containsKey(resolvable))
                results.add(unaryEstimates.get(resolvable));
            if (inferrableEstimates != null && inferrableEstimates.containsKey(resolvable))
                results.add(inferrableEstimates.get(resolvable));
            return results;
        }

        public long estimateAllAnswers() {
            assert this.fullAnswerCount >= 0;
            return this.fullAnswerCount;
        }

        public long estimateAnswers(Set<Variable> variableFilter, Set<Resolvable<?>> includedResolvables) {
            if (this.initializationStatus == InitializationStatus.IN_PROGRESS) {
                answerCountEstimator.reportInitializationCycle(this.conjunction);
            }

            List<LocalEstimate> includedEstimates = iterate(includedResolvables)
                    .flatMap(resolvable -> iterate(estimatesFromResolvable(resolvable)))
                    .toList();
            Map<Variable, LocalEstimate> costCover = computeGreedyEstimateCoverForVariables(variableFilter, includedEstimates);
            long ret = costOfEstimateCover(variableFilter, costCover);
            assert ret > 0;             // Flag in tests if it happens.
            return Math.max(ret, 1);    // Don't do stupid stuff in prod when it happens.
        }

        private Map<Variable, LocalEstimate> computeGreedyEstimateCoverForVariables(Set<Variable> variableFilter, List<LocalEstimate> includedEstimates) {
            // Does a greedy set cover
            Map<Variable, LocalEstimate> costCover = new HashMap<>(unaryEstimateCover);
            includedEstimates.sort(Comparator.comparing(x -> x.answerEstimate(variableFilter)));
            for (LocalEstimate estimate : includedEstimates) {
                Set<Variable> filteredVariablesInEstimate = estimate.variables.stream()
                        .filter(variableFilter::contains).collect(Collectors.toSet());

                long currentCostToCover = costOfEstimateCover(filteredVariablesInEstimate, costCover);
                if (currentCostToCover > estimate.answerEstimate(filteredVariablesInEstimate)) {
                    filteredVariablesInEstimate.forEach(v -> costCover.put(v, estimate));
                }
            }
            return costCover;
        }

        private static long costOfEstimateCover(Set<Variable> variablesToConsider, Map<Variable, LocalEstimate> coverMap) {
            Set<LocalEstimate> subsetCoveredBy = coverMap.keySet().stream().filter(variablesToConsider::contains)
                    .map(coverMap::get).collect(Collectors.toSet());
            return subsetCoveredBy.stream().map(estimate -> estimate.answerEstimate(variablesToConsider)).reduce(1L, (x, y) -> x * y);
        }

        public boolean needsPreparation() {
            return initializationStatus == InitializationStatus.NOT_STARTED || initializationStatus == InitializationStatus.RESET;
        }

        private void reset() {
            assert this.initializationStatus == InitializationStatus.COMPLETE;
            this.initializationStatus = InitializationStatus.RESET;
            this.inferrableEstimates = null;
            this.unaryEstimates = null;
            this.fullAnswerCount = -1;
            this.negatedsCost = -1;
        }

        private void recursivelyInitializeTriggeredRules() {
            resolvables().filter(Resolvable::isConcludable).map(Resolvable::asConcludable).forEachRemaining(concludable -> {
                Map<Rule, Set<Unifier>> unifiers = logicMgr.applicableRules(concludable);
                iterate(unifiers.keySet()).forEachRemaining(rule -> {
                    answerCountEstimator.registerAndInitializeConjunction(rule.condition().conjunction());
                });
            });
        }

        private void initializeLocalEstimates() {
            if (!this.needsPreparation()) return;
            //TODO: How does traversal handle type Variables?

            InitializationStatus originalStatus = initializationStatus;
            initializationStatus = InitializationStatus.IN_PROGRESS;
            // Create a baseline estimate from type information
            if (originalStatus == InitializationStatus.NOT_STARTED) {
                assert unaryEstimateCover == null && retrievableEstimates == null;
                unaryEstimateCover = computeNonInferredUnaryEstimateCover();
                retrievableEstimates = deriveEstimatesFromRetrievables();
                recursivelyInitializeTriggeredRules();
            }

            assert inferrableEstimates == null && unaryEstimates == null;
            inferrableEstimates = deriveEstimatesFromInferrables();
            unaryEstimates = computeUnaryEstimatesWithInference(unaryEstimateCover);
            unaryEstimateCover = computeFinalUnaryEstimateCover(unaryEstimateCover); // recompute with inferred

            assert this.negatedsCost == -1 || originalStatus == InitializationStatus.RESET;
            if (originalStatus == InitializationStatus.NOT_STARTED) this.negatedsCost = computeNegatedsCost();

            List<LocalEstimate> allEstimates = resolvables().flatMap(resolvable -> iterate(estimatesFromResolvable(resolvable))).toList();
            Map<Variable, LocalEstimate> fullCostCover = computeGreedyEstimateCoverForVariables(allVariables(), allEstimates);
            this.fullAnswerCount = costOfEstimateCover(allVariables(), fullCostCover) + this.negatedsCost;

            // Can we prune the multiVarEstimates stored?
            // Not if we want to order-resolvables. Else, yes based on queryableVariables.
            initializationStatus = InitializationStatus.COMPLETE;
        }

        private Map<Resolvable<?>, LocalEstimate> computeUnaryEstimatesWithInference(Map<Variable, LocalEstimate> nonInferredCover) {
            assert inferrableEstimates != null;
            Map<Resolvable<?>, LocalEstimate> unaryEstimates = new HashMap<>();
            iterate(inferrableEstimates.keySet()).map(Resolvable::asConcludable)
                    .forEachRemaining(concludable -> {
                        ThingVariable v = concludable.generating().get();
                        long inferredAnswerCount = (concludable.isHas() || concludable.isAttribute()) ?
                                answerCountModel.attributesCreatedByExplicitHas(concludable) :
                                answerCountModel.estimateInferredAnswerCount(concludable, set(v));
                        unaryEstimates.put(concludable, new LocalEstimate.SimpleEstimate(list(v), nonInferredCover.get(v).answerEstimate(set(v)) + inferredAnswerCount));
                    });
            return unaryEstimates;
        }

        private Map<Variable, LocalEstimate> computeNonInferredUnaryEstimateCover() {
            Map<Variable, LocalEstimate> unaryEstimateCover = new HashMap<>();
            iterate(allVariables()).forEachRemaining(v -> {
                unaryEstimateCover.put(v.asThing(), new LocalEstimate.SimpleEstimate(list(v.asThing()), answerCountModel.countPersistedThingsMatchingType(v.asThing())));
            });
            return unaryEstimateCover;
        }

        private Map<Variable, LocalEstimate> computeFinalUnaryEstimateCover(Map<Variable, LocalEstimate> nonInferredUnaryEstimateCover) {
            Map<Variable, LocalEstimate> newUnaryEstimateCover = new HashMap<>(nonInferredUnaryEstimateCover);
            iterate(unaryEstimates.values()).forEachRemaining(estimate -> {
                Variable v = estimate.variables.get(0);
                long existingEstimate = newUnaryEstimateCover.get(v).answerEstimate(set(v));
                long newEstimate = estimate.answerEstimate(set(v));
                if (newEstimate > existingEstimate) { // Biggest one serves as baseline.
                    newUnaryEstimateCover.put(v, estimate);
                }
            });
            return newUnaryEstimateCover;
        }

        private Map<Resolvable<?>, List<LocalEstimate>> deriveEstimatesFromRetrievables() {
            Map<Resolvable<?>, List<LocalEstimate>> retrievableEstimates = new HashMap<>();
            resolvables().filter(Resolvable::isRetrievable).map(Resolvable::asRetrievable).forEachRemaining(retrievable -> {
                retrievableEstimates.put(retrievable, new ArrayList<>());
                Set<Concludable> concludablesInRetrievable = ResolvableConjunction.of(retrievable.pattern()).positiveConcludables();
                iterate(concludablesInRetrievable).forEachRemaining(concludable -> {
                    deriveEstimatesFromConcludable(concludable)
                            .ifPresent(estimate -> retrievableEstimates.get(retrievable).add(estimate));
                });
            });

            return retrievableEstimates;
        }

        private Map<Resolvable<?>, LocalEstimate> deriveEstimatesFromInferrables() {
            Map<Resolvable<?>, LocalEstimate> inferrableEstimates = new HashMap<>();
            iterate(resolvables()).filter(Resolvable::isConcludable).map(Resolvable::asConcludable)
                    .forEachRemaining(concludable -> {
                        deriveEstimatesFromConcludable(concludable)
                                .ifPresent(estimate -> inferrableEstimates.put(concludable, estimate));
                    });
            return inferrableEstimates;
        }

        private Optional<LocalEstimate> deriveEstimatesFromConcludable(Concludable concludable) {
            if (concludable.isHas()) {
                return Optional.of(answerCountModel.estimatesFromHasEdges(concludable.asHas()));
            } else if (concludable.isRelation()) {
                return Optional.of(answerCountModel.estimatesFromRolePlayersAssumingEvenDistribution(concludable.asRelation()));
            } else if (concludable.isIsa()) {
                assert concludable.generating().isPresent();
                ThingVariable v = concludable.generating().get();
                return Optional.of(new LocalEstimate.SimpleEstimate(list(v),
                        unaryEstimateCover.get(v).answerEstimate(set(v)) + answerCountModel.estimateInferredAnswerCount(concludable, set(v))));
            } else throw TypeDBException.of(ILLEGAL_STATE);
        }

        private long computeNegatedsCost() {
            return resolvables().filter(Resolvable::isNegated).map(Resolvable::asNegated)
                    .flatMap(negated -> iterate(negated.disjunction().conjunctions()))
                    .map(negatedConjunction -> {
                        answerCountEstimator.registerAndInitializeConjunction(negatedConjunction);
                        return answerCountEstimator.estimateAllAnswers(negatedConjunction);
                    }).reduce(0L, Long::sum);
        }

        private static abstract class LocalEstimate {

            final List<Variable> variables;

            private LocalEstimate(List<Variable> variables) {
                this.variables = variables;
            }

            abstract long answerEstimate(Set<Variable> variableFilter);

            private static class SimpleEstimate extends LocalEstimate {
                private final long staticEstimate;

                private SimpleEstimate(List<Variable> variables, long estimate) {
                    super(variables);
                    this.staticEstimate = estimate;
                }

                @Override
                long answerEstimate(Set<Variable> variableFilter) {
                    return staticEstimate;
                }
            }

            public static class CoPlayerEstimate extends LocalEstimate {

                private final Map<TypeVariable, Integer> rolePlayerCounts;
                private final Map<TypeVariable, Long> rolePlayerEstimates;
                private final double relationTypeEstimate;
                private final long inferredRelationEstimate;

                public CoPlayerEstimate(List<Variable> variables, double relationTypeEstimate,
                                        Map<TypeVariable, Long> rolePlayerEstimates, Map<TypeVariable, Integer> rolePlayerCounts,
                                        long inferredRelationEstimate) {
                    super(variables);
                    this.relationTypeEstimate = relationTypeEstimate;
                    this.rolePlayerEstimates = rolePlayerEstimates;
                    this.rolePlayerCounts = rolePlayerCounts;
                    this.inferredRelationEstimate = inferredRelationEstimate;
                }

                @Override
                long answerEstimate(Set<Variable> variableFilter) {
                    long singleRelationEstimate = 1L;
                    for (TypeVariable key : rolePlayerCounts.keySet()) {
                        assert rolePlayerEstimates.containsKey(key);
                        long avgRolePlayers = Double.valueOf(Math.ceil(rolePlayerEstimates.get(key) / relationTypeEstimate)).longValue();
                        singleRelationEstimate *= nPermuteKforSmallK(avgRolePlayers, rolePlayerCounts.get(key));
                    }

                    long fullEstimate = Double.valueOf(Math.ceil(relationTypeEstimate * singleRelationEstimate)).longValue() + inferredRelationEstimate;
                    return fullEstimate;
                }

                private long nPermuteKforSmallK(long n, long k) {
                    long ans = 1;
                    for (int i = 0; i < k; i++) ans *= n - i;
                    return ans;
                }
            }
        }
    }

    private static class AnswerCountModel {
        private final AnswerCountEstimator answerCountEstimator;
        private GraphManager graphMgr;

        public AnswerCountModel(AnswerCountEstimator answerCountEstimator, GraphManager graphMgr) {
            this.answerCountEstimator = answerCountEstimator;
            this.graphMgr = graphMgr;
        }

        private long estimateInferredAnswerCount(Concludable concludable, Set<Variable> variableFilter) {
            Map<Rule, Set<Unifier>> unifiers = answerCountEstimator.logicMgr.applicableRules(concludable);
            long inferredEstimate = 0;
            for (Rule rule : unifiers.keySet()) {
                for (Unifier unifier : unifiers.get(rule)) {
                    Set<Identifier.Variable> ruleSideIds = iterate(variableFilter)
                            .flatMap(v -> iterate(unifier.mapping().get(v.id()))).toSet();
                    Set<Variable> ruleSideVariables = iterate(ruleSideIds).map(id -> rule.conclusion().conjunction().pattern().variable(id))
                            .toSet();
                    if (rule.conclusion().generating().isPresent() && ruleSideVariables.contains(rule.conclusion().generating().get())) {
                        // There is one generated variable per combination of ALL variables in the conclusion
                        ruleSideVariables = rule.conclusion().pattern().variables().stream().filter(Variable::isThing).collect(Collectors.toSet());
                    }
                    inferredEstimate += answerCountEstimator.estimateAnswers(rule.condition().conjunction(), ruleSideVariables);
                }
            }
            return inferredEstimate;
        }

        private ConjunctionAnswerCountEstimator.LocalEstimate estimatesFromHasEdges(Concludable.Has concludableHas) {
            long estimate = countPersistedHasEdges(concludableHas.asHas().owner().inferredTypes(), concludableHas.asHas().attribute().inferredTypes()) +
                    estimateInferredAnswerCount(concludableHas, set(concludableHas.asHas().owner(), concludableHas.asHas().attribute()));

            return new ConjunctionAnswerCountEstimator.LocalEstimate.SimpleEstimate(list(concludableHas.asHas().owner(), concludableHas.asHas().attribute()), estimate);
        }

        private ConjunctionAnswerCountEstimator.LocalEstimate estimatesFromRolePlayersAssumingEvenDistribution(Concludable.Relation concludable) {
            // Small inaccuracy: We double count duplicate roles (r:$a, r:$b)
            // counts the case where r:$a=r:$b, which TypeDB wouldn't return
            Set<RelationConstraint.RolePlayer> rolePlayers = concludable.relation().players();
            List<Variable> constrainedVars = new ArrayList<>();
            Map<TypeVariable, Long> rolePlayerEstimates = new HashMap<>();
            Map<TypeVariable, Integer> rolePlayerCounts = new HashMap<>();

            double relationTypeEstimate = countPersistedThingsMatchingType(concludable.relation().owner());

            for (RelationConstraint.RolePlayer rp : rolePlayers) {
                constrainedVars.add(rp.player());
                TypeVariable key = rp.roleType().orElse(null);
                rolePlayerCounts.put(key, rolePlayerCounts.getOrDefault(key, 0) + 1);
                if (!rolePlayerEstimates.containsKey(key)) {
                    rolePlayerEstimates.put(key, countPersistedRolePlayers(rp));
                }
            }

            // TODO: Can improve estimate by collecting List<List<LocalEstimate>> from the triggered rules and doign sum(costCover).
            // Consider owner in the inferred estimate call only if it's not anonymous
            if (concludable.relation().owner().id().isName()) {
                constrainedVars.add(concludable.relation().owner());
            }
            long inferredRelationsEstimate = estimateInferredAnswerCount(concludable, new HashSet<>(constrainedVars));
            constrainedVars.add(concludable.relation().owner()); // Now add it.

            return new ConjunctionAnswerCountEstimator.LocalEstimate.CoPlayerEstimate(constrainedVars, relationTypeEstimate, rolePlayerEstimates, rolePlayerCounts, inferredRelationsEstimate);
        }

        public long attributesCreatedByExplicitHas(Concludable concludable) {
            return iterate(answerCountEstimator.logicMgr.applicableRules(concludable).keySet())
                    .filter(rule -> rule.conclusion().isExplicitHas())
                    .map(rule -> rule.conclusion().asExplicitHas().value().value())
                    .toSet().size();
        }

        private long countPersistedRolePlayers(RelationConstraint.RolePlayer rolePlayer) {
            return graphMgr.data().stats().thingVertexSum(rolePlayer.inferredRoleTypes());
        }

        private long countPersistedThingsMatchingType(ThingVariable thingVar) {
            return graphMgr.data().stats().thingVertexSum(thingVar.inferredTypes());
        }

        private long countPersistedHasEdges(Set<Label> ownerTypes, Set<Label> attributeTypes) {
            return ownerTypes.stream().map(ownerType ->
                    attributeTypes.stream()
                            .map(attrType -> graphMgr.data().stats().hasEdgeCount(ownerType, attrType))
                            .reduce(0L, Long::sum)
            ).reduce(0L, Long::sum);
        }
    }
}