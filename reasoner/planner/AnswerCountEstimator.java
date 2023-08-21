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
 *
 */
package com.vaticle.typedb.core.reasoner.planner;

import com.vaticle.typedb.common.collection.Collections;
import com.vaticle.typedb.common.collection.Pair;
import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.parameters.Label;
import com.vaticle.typedb.core.graph.GraphManager;
import com.vaticle.typedb.core.logic.LogicManager;
import com.vaticle.typedb.core.logic.Rule;
import com.vaticle.typedb.core.logic.resolvable.Concludable;
import com.vaticle.typedb.core.logic.resolvable.Negated;
import com.vaticle.typedb.core.logic.resolvable.Resolvable;
import com.vaticle.typedb.core.logic.resolvable.ResolvableConjunction;
import com.vaticle.typedb.core.logic.resolvable.Retrievable;
import com.vaticle.typedb.core.logic.resolvable.Unifier;
import com.vaticle.typedb.core.pattern.constraint.Constraint;
import com.vaticle.typedb.core.pattern.constraint.thing.HasConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.IIDConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.IsConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.IsaConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.PredicateConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.RelationConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.ThingConstraint;
import com.vaticle.typedb.core.pattern.variable.ThingVariable;
import com.vaticle.typedb.core.pattern.variable.Variable;
import com.vaticle.typedb.core.reasoner.planner.ConjunctionGraph.ConjunctionNode;
import com.vaticle.typedb.core.traversal.common.Identifier;
import com.vaticle.typeql.lang.common.TypeQLToken;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import static com.vaticle.typedb.common.collection.Collections.list;
import static com.vaticle.typedb.common.collection.Collections.set;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.UNSUPPORTED_OPERATION;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;

public class AnswerCountEstimator {
    private final LogicManager logicMgr;
    private final ConjunctionModelFactory conjunctionModelFactory;
    private final ConjunctionGraph conjunctionGraph;
    private final Map<ResolvableConjunction, ConjunctionModel> conjunctionModels;
    private final Map<ResolvableConjunction, IncrementalEstimator> fullConjunctionEstimators;

    public AnswerCountEstimator(LogicManager logicMgr, GraphManager graph, ConjunctionGraph conjunctionGraph) {
        this.logicMgr = logicMgr;
        this.conjunctionModelFactory = new ConjunctionModelFactory(new LocalModelFactory(this, graph));
        this.conjunctionGraph = conjunctionGraph;
        this.conjunctionModels = new HashMap<>();
        this.fullConjunctionEstimators = new HashMap<>();
    }

    public void buildConjunctionModel(ResolvableConjunction conjunction) {
        if (!conjunctionModels.containsKey(conjunction)) {
            ConjunctionNode conjunctionNode = conjunctionGraph.conjunctionNode(conjunction);
            iterate(conjunctionNode.negateds()).flatMap(negated -> iterate(negated.disjunction().conjunctions()))
                    .forEachRemaining(this::buildConjunctionModel);
            iterate(conjunctionNode.acyclicConcludables()).flatMap(concludable -> iterate(conjunctionGraph.dependencies(concludable)))
                    .forEachRemaining(this::buildConjunctionModel);
            AnswerCountEstimator.ConjunctionModel acyclicModel = conjunctionModelFactory.buildAcyclicModel(conjunctionNode);
            conjunctionModels.put(conjunction, acyclicModel);

            iterate(conjunctionNode.cyclicConcludables()).flatMap(concludable -> iterate(conjunctionGraph.dependencies(concludable)))
                    .forEachRemaining(this::buildConjunctionModel);
            AnswerCountEstimator.ConjunctionModel cyclicModel = conjunctionModelFactory.buildCyclicModel(conjunctionNode, acyclicModel);
            conjunctionModels.put(conjunction, cyclicModel);
        }
    }

    public double estimateAnswers(ResolvableConjunction conjunction, Set<Variable> variables) {
        if (!conjunctionModels.containsKey(conjunction)) buildConjunctionModel(conjunction);
        if (!fullConjunctionEstimators.containsKey(conjunction)) {
            IncrementalEstimator incrementalEstimator = createIncrementalEstimator(conjunction);
            conjunctionModels.get(conjunction).conjunctionNode.resolvables().forEach(incrementalEstimator::extend);
            fullConjunctionEstimators.put(conjunction, incrementalEstimator);
        }
        IncrementalEstimator estimator = fullConjunctionEstimators.get(conjunction);
        Set<Variable> estimateableVariables = ReasonerPlanner.estimateableVariables(variables);
        return estimator.answerEstimate(estimateableVariables);
    }

    public double localEstimate(ResolvableConjunction conjunction, Resolvable<?> resolvable, Set<Variable> variables) {
        return conjunctionModels.get(conjunction).localEstimate(this, resolvable, variables);
    }

    public IncrementalEstimator createIncrementalEstimator(ResolvableConjunction conjunction) {
        return createIncrementalEstimator(conjunction, set());
    }

    public IncrementalEstimator createIncrementalEstimator(ResolvableConjunction conjunction, Set<Variable> mode) {
        if (!conjunctionModels.containsKey(conjunction)) buildConjunctionModel(conjunction);
        return new IncrementalEstimator(conjunctionModels.get(conjunction), conjunctionModelFactory.localModelFactory, mode);
    }

    public static class IncrementalEstimator {
        private final ConjunctionModel conjunctionModel;
        private final LocalModelFactory localModelFactory;
        private final Map<Variable, Double> minVariableEstimate;
        private final Map<Variable, Set<LocalModel.EdgeEstimate.Directed>> outgoingEdges;

        private IncrementalEstimator(ConjunctionModel conjunctionModel, LocalModelFactory localModelFactory, Set<Variable> initialBounds) {
            this.conjunctionModel = conjunctionModel;
            this.localModelFactory = localModelFactory;
            this.minVariableEstimate = new HashMap<>();
            this.outgoingEdges = new HashMap<>();
            initialBounds.forEach(v -> {
                this.minVariableEstimate.put(v, 1.0);
                this.outgoingEdges.put(v, new HashSet<>());
            });
        }

        public void extend(Resolvable<?> resolvable) {
            Map<Variable, Double> improvedVariableEstimates = new HashMap<>();
            List<LocalModel> models = iterate(conjunctionModel.modelsForResolvable(resolvable)).map(LocalModel::clone).toList();

            iterate(models).flatMap(model -> iterate(model.vertices))
                    .forEachRemaining(vertex -> outgoingEdges.computeIfAbsent(vertex.variable, v -> new HashSet<>()));
            iterate(models).flatMap(model -> iterate(model.edges))
                    .forEachRemaining(edge -> {
                        outgoingEdges.get(edge.directed[0].from()).add(edge.directed[0]);
                        outgoingEdges.get(edge.directed[1].from()).add(edge.directed[1]);
                    });

            iterate(models).flatMap(model -> iterate(model.vertices)).forEachRemaining(vertexEstimate -> {
                // We need to consider improved connectivity as a cause for propagation too.
                improvedVariableEstimates.merge(vertexEstimate.variable,
                        Math.min(minVariableEstimate.getOrDefault(vertexEstimate.variable, Double.MAX_VALUE), vertexEstimate.estimate),
                        Math::min);
            });

            propagate(improvedVariableEstimates);
        }

        private void propagate(Map<Variable, Double> firstUpdatesToApply) {
            int maxIters = Math.max(1, 2 * (firstUpdatesToApply.size() + minVariableEstimate.size()));
            Map<Variable, Double> updatesToApply = firstUpdatesToApply;
            while (!updatesToApply.isEmpty() && maxIters > 0) {
                assert iterate(updatesToApply.entrySet()).allMatch(update -> update.getValue() <= minVariableEstimate.getOrDefault(update.getKey(), Double.MAX_VALUE));
                minVariableEstimate.putAll(updatesToApply);
                Map<Variable, Double> improvedVariableEstimates = new HashMap<>();
                iterate(updatesToApply.keySet()).forEachRemaining(variable -> {
                    Map<Variable, Double> scaledEstimates = applyScaling(variable);
                    scaledEstimates.forEach((k, v) -> improvedVariableEstimates.merge(k, v, Math::min));
                });
                updatesToApply = improvedVariableEstimates;
                maxIters--;
            }
        }

        private Map<Variable, Double> applyScaling(Variable from) {
            Map<Variable, Double> cascadingEffects = new HashMap<>();
            Double newFromEstimate = minVariableEstimate.get(from);
            outgoingEdges.get(from).forEach(edge -> {
                edge.scaleDownFrom(newFromEstimate);
                double delta = (minVariableEstimate.get(edge.to()) - edge.toEstimate());
                if ( delta > 0.1 && delta / minVariableEstimate.get(edge.to()) > 0.01) { // Ignore reductions less than 1%
                    cascadingEffects.put(edge.to(), edge.toEstimate());
                }
            });
            return cascadingEffects;
        }

        public double answerEstimate(Set<Variable> variables) {
            Set<Variable> estimateableVariables = ReasonerPlanner.estimateableVariables(variables);
            if (estimateableVariables.isEmpty()) return 1;
            Set<Variable> remainingVars = new HashSet<>(estimateableVariables);
            double estimate = 1.0;
            while (!remainingVars.isEmpty()) {
                Variable start = remainingVars.stream().findAny().get();
                // Question: Does the tree which minimises the answer count for all variables also minimise it for the queried variables?
                // Ideally we'd figure out how to do the projection first, and then estimation should just be finding the MST.
                Map<Variable, Set<LocalModel.EdgeEstimate.Directed>> mdst = findTree(remainingVars, start);
                estimate *= minVariableEstimate.get(start) * effectiveConnectivityFromTree(estimateableVariables, mdst, start, 1.0, null).first();
            }
            return estimate;
        }

        private Map<Variable, Set<LocalModel.EdgeEstimate.Directed>> findTree(Set<Variable> remainingQueryVars, Variable start) {
            Map<Variable, Set<LocalModel.EdgeEstimate.Directed>> tree = new HashMap<>();
            tree.put(start, new HashSet<>());
            remainingQueryVars.remove(start);
            PriorityQueue<LocalModel.EdgeEstimate.Directed> fringe = new PriorityQueue<>(Comparator.comparing(LocalModel.EdgeEstimate.Directed::connectivity));
            fringe.addAll(outgoingEdges.get(start));
            while (!fringe.isEmpty()) {
                LocalModel.EdgeEstimate.Directed topEdge = fringe.poll();
                Variable nextVar = topEdge.to();

                if (tree.containsKey(nextVar)) continue;
                tree.put(nextVar, new HashSet<>());
                remainingQueryVars.remove(nextVar);
                tree.get(topEdge.from()).add(topEdge);

                fringe.addAll(outgoingEdges.get(nextVar));
            }
            return tree;
        }

        // Returns connectivity, upper-bound for connectivity
        // Something with the adaptive minVariableEstimate and the way we upper bound is being non-deterministic.
        private Pair<Double, Double> effectiveConnectivityFromTree(Set<Variable> queryVariables, Map<Variable, Set<LocalModel.EdgeEstimate.Directed>> tree, Variable at, double inputConnectivity, LocalModel.EdgeEstimate.Directed incomingEdge) {
            double upperBound = queryVariables.contains(at) ? minVariableEstimate.get(at) : 1.0;
            double connectivity = inputConnectivity;

            Set<LocalModel.EdgeEstimate.Directed> relevantEdges = new HashSet<>();

            for (LocalModel.EdgeEstimate.Directed edge : tree.get(at)) {
                Pair<Double, Double> branchEstimate = effectiveConnectivityFromTree(queryVariables, tree, edge.to(), Math.min(minVariableEstimate.get(edge.to()), edge.connectivity()), edge);
                if (branchEstimate != null) {
                    connectivity *= branchEstimate.first();
                    upperBound *= branchEstimate.second();
                    relevantEdges.add(edge);
                }
            }

            boolean isRelevantBranch = queryVariables.contains(at) || relevantEdges.size() > 0;
            if (!isRelevantBranch) return null;

            // Correct for repeated role-players
            if (at.isThing() && at.asThing().relation().isPresent()) {
                if (incomingEdge != null) relevantEdges.add(incomingEdge.reversed());

                Set<Set<LocalModel.EdgeEstimate.Directed>> groupedEdges = iterate(relevantEdges).map(LocalModel.EdgeEstimate.Directed::sameRoleTypeSet).distinct()
                        .map(sameRoleTypeSet -> Collections.intersection(sameRoleTypeSet, relevantEdges)).toSet();

                for (Set<LocalModel.EdgeEstimate.Directed> toCorrect : groupedEdges) {
                    if (toCorrect.size() > 1) {
                        double permutations = 1;
                        double nPowerN = 1;
                        for (int i = 1; i <= toCorrect.size(); i++) {
                            permutations *= i;
                            nPowerN *= toCorrect.size();
                        }
                        connectivity *= (permutations / nPowerN);
                    }
                }
            }

            connectivity = Math.min(connectivity, upperBound);
            return new Pair<>(connectivity, upperBound);
        }

        public double answerSetSize() {
            // TODO: ignore the anonymous variables iff/when ConjunctionController can ignore them when branching CompoundStreams
            return answerEstimate(minVariableEstimate.keySet());
        }

        public IncrementalEstimator clone() {
            // initialbounds = set() is ok, the next steps will take care of it.
            IncrementalEstimator cloned = new IncrementalEstimator(conjunctionModel, localModelFactory, set());
            cloned.minVariableEstimate.putAll(this.minVariableEstimate);
            this.outgoingEdges.forEach((k, v) -> cloned.outgoingEdges.put(k, new HashSet<>(v)));
            return cloned;
        }
    }

    private static class ConjunctionModel {
        private final ConjunctionNode conjunctionNode;
        private final Map<Resolvable<?>, List<LocalModel>> constraintModels;
        private final boolean isCyclic;

        private final Map<Resolvable<?>, IncrementalEstimator> resolvableEstimators;

        private ConjunctionModel(ConjunctionNode conjunctionNode, Map<Resolvable<?>, List<LocalModel>> constraintModels,
                                 boolean isCyclic) {
            this.conjunctionNode = conjunctionNode;
            this.constraintModels = constraintModels;
            this.isCyclic = isCyclic;
            this.resolvableEstimators = new HashMap<>();
        }

        private List<LocalModel> modelsForResolvable(Resolvable<?> resolvable) {
            return constraintModels.get(resolvable);
        }

        private double localEstimate(AnswerCountEstimator answerCountEstimator, Resolvable<?> resolvable, Set<Variable> variables) {
            return resolvableEstimators.computeIfAbsent(resolvable, res -> {
                IncrementalEstimator estimator = answerCountEstimator.createIncrementalEstimator(conjunctionNode.conjunction());
                estimator.extend(res);
                return estimator;
            }).answerEstimate(variables);
        }
    }

    private static class ConjunctionModelFactory {
        private final LocalModelFactory localModelFactory;

        private ConjunctionModelFactory(LocalModelFactory localModelFactory) {
            this.localModelFactory = localModelFactory;
        }

        private ConjunctionModel buildAcyclicModel(ConjunctionNode conjunctionNode) {
            Map<Resolvable<?>, List<LocalModel>> models = new HashMap<>();
            iterate(conjunctionNode.acyclicConcludables())
                    .forEachRemaining(concludable -> models.put(concludable, buildModelsForConcludable(concludable)));

            iterate(conjunctionNode.retrievables())
                    .forEachRemaining(retrievable -> models.put(retrievable, buildModelsForRetrievable(retrievable)));
            iterate(conjunctionNode.negateds())
                    .forEachRemaining(negated -> models.put(negated, buildModelsForNegated(negated)));
            // Should we recurse into the acyclic dependencies? Don't think so - Would over-constrain
            iterate(conjunctionNode.cyclicConcludables())
                    .forEachRemaining(concludable -> models.put(concludable, buildVariableModelsForCyclicConcludable(concludable)));

            assert !iterate(conjunctionNode.resolvables()).filter(resolvable -> !models.containsKey(resolvable)).hasNext();
            return new ConjunctionModel(conjunctionNode, models, false);
        }

        private ConjunctionModel buildCyclicModel(ConjunctionNode conjunctionNode, ConjunctionModel acyclicModel) {
            assert acyclicModel.conjunctionNode == conjunctionNode;
            assert !acyclicModel.isCyclic;
            Map<Resolvable<?>, List<LocalModel>> models = new HashMap<>(acyclicModel.constraintModels);
            iterate(conjunctionNode.cyclicConcludables())
                    .forEachRemaining(concludable -> models.put(concludable, buildModelsForConcludable(concludable)));

            assert !iterate(conjunctionNode.resolvables()).filter(resolvable -> !models.containsKey(resolvable)).hasNext();
            return new ConjunctionModel(conjunctionNode, models, true);
        }

        private List<LocalModel> buildModelsForRetrievable(Retrievable retrievable) {
            return iterate(extractConstraints(retrievable))
                    .map(constraint -> buildConstraintModel(constraint, null))
                    .toList();
        }

        // INACCURACY: We don't consider negations, which can reduce the number of answers retrieved.
        private List<LocalModel> buildModelsForNegated(Negated negated) {
            return list();
        }

        private List<LocalModel> buildModelsForConcludable(Concludable concludable) {
            return iterate(concludable.concludableConstraints()).filter(this::isModellable)
                    .map(constraint -> buildConstraintModel(constraint, concludable))
                    .toList();
        }

        private List<LocalModel> buildVariableModelsForCyclicConcludable(Concludable concludable) {
            return list(localModelFactory.variableModelForCyclicConcludable(concludable));
        }

        private LocalModel buildConstraintModel(Constraint constraint, @Nullable Concludable correspondingConcludable) {
            if (constraint.isThing()) {
                ThingConstraint asThingConstraint = constraint.asThing();
                if (asThingConstraint.isHas()) {
                    return localModelFactory.modelForHas(asThingConstraint.asHas(), correspondingConcludable);
                } else if (asThingConstraint.isRelation()) {
                    return localModelFactory.modelForRelation(asThingConstraint.asRelation(), correspondingConcludable);
                } else if (asThingConstraint.isIsa()) {
                    return localModelFactory.modelForIsa(asThingConstraint.asIsa(), correspondingConcludable);
                } else if (asThingConstraint.isIID()) {
                    return localModelFactory.modelForIID(asThingConstraint.asIID());
                } else if (asThingConstraint.isPredicate()) {
                    return localModelFactory.modelForPredicate(asThingConstraint.asPredicate(), correspondingConcludable);
                } else if (asThingConstraint.isIs()) {
                    return localModelFactory.modelForIs(asThingConstraint.asIs(), correspondingConcludable);
                } else throw TypeDBException.of(ILLEGAL_STATE);
            } else if (constraint.isValue()) {
                return new LocalModel(new HashSet<>(localModelFactory.variableModelsBasedOnType(new HashSet<>(constraint.asValue().variables()), null)), set());
            } else throw TypeDBException.of(UNSUPPORTED_OPERATION);
        }

        private Set<Constraint> extractConstraints(Retrievable retrievable) {
            Set<Constraint> constraints = new HashSet<>();
            iterate(retrievable.pattern().variables()).flatMap(v -> iterate(v.constraints())).filter(this::isModellable).forEachRemaining(constraints::add);
            return constraints;
        }

        private boolean isModellable(Constraint constraint) {
            return constraint.isThing() || constraint.isValue();
        }
    }

    private static class LocalModel {

        private final Set<VariableEstimate> vertices;
        private final Set<EdgeEstimate> edges;

        protected LocalModel(Set<VariableEstimate> vertices, Set<EdgeEstimate> edges) {
            this.vertices = vertices;
            this.edges = edges;

            Map<Variable, Double> vertexEstimates = new HashMap<>();
            this.vertices.forEach(vertex -> vertexEstimates.put(vertex.variable, vertex.estimate));
            this.edges.forEach(edge -> {
                edge.setEstimates(vertexEstimates.get(edge.vars[0]), vertexEstimates.get(edge.vars[1]));
            });
        }

        public LocalModel clone() {
            Map<EdgeEstimate, EdgeEstimate> clonedEdgeMap = new HashMap<>();
            Map<Set<EdgeEstimate.Directed>, Set<EdgeEstimate.Directed>> clonedSameRoleTypeSet = new HashMap<>();

            iterate(edges).forEachRemaining(edge -> clonedSameRoleTypeSet.computeIfAbsent(edge.sameRoleTypeSet, s -> new HashSet<>()));
            iterate(edges).forEachRemaining(edge -> clonedEdgeMap.put(edge, new EdgeEstimate(edge.vars[0], edge.vars[1], edge.nEdges, clonedSameRoleTypeSet.get(edge.sameRoleTypeSet))));
            iterate(edges).forEachRemaining(edge -> {
                iterate(edge.sameRoleTypeSet).forEachRemaining(directed -> {
                    EdgeEstimate.Directed clonedEdge = clonedEdgeMap.get(directed.undirected()).edgeStarting(directed.from());
                    clonedSameRoleTypeSet.get(edge.sameRoleTypeSet).add(clonedEdge);
                });
            });

            return new LocalModel(vertices, iterate(clonedEdgeMap.values()).toSet());
        }

        private static class VariableEstimate {
            private final Variable variable;
            private final double estimate;

            private VariableEstimate(Variable variable, double estimate) {
                this.variable = variable;
                this.estimate = estimate;
            }
        }

        private static class EdgeEstimate {
            private final Variable[] vars;
            private final Directed[] directed;
            private final Set<Directed> sameRoleTypeSet;

            private double nEdges;
            private double[] nodeEstimates;

            private EdgeEstimate(Variable v1, Variable v2, double nEdges) {
                this(v1, v2, nEdges, set());
            }

            private EdgeEstimate(Variable v1, Variable v2, double nEdges, Set<EdgeEstimate.Directed> sameRoleTypeSet) {
                vars = new Variable[]{v1, v2};
                this.nEdges = nEdges;
                this.directed = new Directed[]{new Directed(0), new Directed(1)};
                this.sameRoleTypeSet = sameRoleTypeSet;
            }

            private void setEstimates(double v1Estimate, double v2Estimate) {
                this.nodeEstimates = new double[]{v1Estimate, v2Estimate};
            }

            private Directed edgeStarting(Variable from) {
                return from == vars[0] ? directed[0] : directed[1];
            }

            private class Directed {
                private final int idx;
                private final int other;

                private Directed(int idx) {
                    this.idx = idx;
                    this.other = 1 - idx;
                }
                private EdgeEstimate undirected() { return EdgeEstimate.this; }

                Directed reversed() {
                    return directed[other];
                }

                Variable from() {
                    return vars[idx];
                }

                Variable to() {
                    return vars[other];
                }

                double fromEstimate() {
                    return nodeEstimates[idx];
                }

                double toEstimate() {
                    return nodeEstimates[other];
                }

                double connectivity() {
                    return fromEstimate() != 0 ? (nEdges / fromEstimate()) : 0;
                }

                void scaleDownFrom(double newFromEstimate) {
                    if (newFromEstimate >= fromEstimate()) return;
                    nEdges = fromEstimate() != 0 ? (newFromEstimate / fromEstimate() * nEdges) : 0;
                    nodeEstimates[idx] = newFromEstimate;
                    nodeEstimates[other] = Math.min(nodeEstimates[other], nEdges);
                }

                public Set<EdgeEstimate.Directed> sameRoleTypeSet() {
                    return sameRoleTypeSet;
                }
            }
        }
    }

    private static class LocalModelFactory {
        private final AnswerCountEstimator answerCountEstimator;
        private final GraphManager graphMgr;

        private LocalModelFactory(AnswerCountEstimator answerCountEstimator, GraphManager graphMgr) {
            this.answerCountEstimator = answerCountEstimator;
            this.graphMgr = graphMgr;
        }

        private LocalModel modelForRelation(RelationConstraint relationConstraint, @Nullable Concludable correspondingConcludable) {
            // May have oversimplified this compared to 2.17.0
            Set<RelationConstraint.RolePlayer> rolePlayers = relationConstraint.players();

            Map<ThingVariable, Long> typeMaximums = new HashMap<>();
            double typeBasedUpperBound = 1L;
            for (RelationConstraint.RolePlayer rp : rolePlayers) {
                typeMaximums.put(rp.player(), countPersistedThingsMatchingType(rp.player()));
                typeBasedUpperBound *= typeMaximums.get(rp.player());
            }

            long persistedRelationEstimate = countPersistedThingsMatchingType(relationConstraint.owner());
            double inferredRelationsEstimate = 0L;
            if (correspondingConcludable != null) {
                List<Variable> constrainedVars = new ArrayList<>();
                iterate(relationConstraint.players()).forEachRemaining(player -> constrainedVars.add(player.player()));
                if (relationConstraint.owner().id().isName()) {
                    constrainedVars.add(relationConstraint.owner());
                }
                inferredRelationsEstimate = estimateInferredAnswerCount(correspondingConcludable, new HashSet<>(constrainedVars));
            }

            inferredRelationsEstimate = Math.min(inferredRelationsEstimate, typeBasedUpperBound - persistedRelationEstimate);
            long inferredRelationsEstimateRounded = Double.valueOf(Math.ceil(inferredRelationsEstimate)).longValue();

            Map<Variable, LocalModel.VariableEstimate> variableEstimates = new HashMap<>();
            Map<RelationConstraint.RolePlayer, Long> roleEdges = new HashMap<>();
            for (RelationConstraint.RolePlayer rp : rolePlayers) {
                roleEdges.put(rp, countPersistedRolePlayers(rp) + inferredRelationsEstimateRounded);
                variableEstimates.put(rp.player(), new LocalModel.VariableEstimate(rp.player(), Math.min(typeMaximums.get(rp.player()), roleEdges.get(rp))));
            }
            variableEstimates.put(relationConstraint.owner(), new LocalModel.VariableEstimate(relationConstraint.owner(), persistedRelationEstimate + inferredRelationsEstimate));

            Map<Label, Set<LocalModel.EdgeEstimate.Directed>> sameRoleTypeSet = new HashMap<>();
            Set<LocalModel.EdgeEstimate> edges = new HashSet<>();
            roleEdges.forEach((rp, edgeEstimate) -> {
                Set<LocalModel.EdgeEstimate.Directed> sameRolePlayerEdges = sameRoleTypeSet.computeIfAbsent(getRoleType(rp), lbl -> new HashSet<>());
                LocalModel.EdgeEstimate edge = new LocalModel.EdgeEstimate(relationConstraint.owner(), rp.player(), edgeEstimate, sameRolePlayerEdges);
                edges.add(edge);
                sameRolePlayerEdges.add(edge.edgeStarting(relationConstraint.owner()));
            });

            return new LocalModel(new HashSet<>(variableEstimates.values()), edges);
        }

        private LocalModel modelForHas(HasConstraint hasConstraint, @Nullable Concludable correspondingConcludable) {
            double hasEdgeEstimate = countPersistedHasEdges(hasConstraint.owner().inferredTypes(), hasConstraint.attribute().inferredTypes());
            double ownerEstimate = countPersistedThingsMatchingType(hasConstraint.owner());
            double attributeEstimate = countPersistedThingsMatchingType(hasConstraint.attribute());
            if (correspondingConcludable != null) {
                hasEdgeEstimate += estimateInferredAnswerCount(correspondingConcludable, set(hasConstraint.owner(), hasConstraint.attribute()));
                attributeEstimate += attributesCreatedByHasWithIsa(correspondingConcludable);
                if (attributeEstimate != 0 && ownerEstimate < hasEdgeEstimate / attributeEstimate) {
                    // Try to handle inferred owners
                    boolean rulesConcludeOwner = iterate(hasConstraint.owner().inferredTypes()).flatMap(ownerType -> iterate(answerCountEstimator.logicMgr.rulesConcluding(ownerType))).hasNext();
                    if (rulesConcludeOwner) ownerEstimate = hasEdgeEstimate / attributeEstimate;
                }
            }
            ownerEstimate = Math.min(ownerEstimate, hasEdgeEstimate);
            attributeEstimate = Math.min(attributeEstimate, hasEdgeEstimate);
            return new LocalModel(
                    set(
                            new LocalModel.VariableEstimate(hasConstraint.owner(), ownerEstimate),
                            new LocalModel.VariableEstimate(hasConstraint.attribute(), attributeEstimate)),
                    set(
                            new LocalModel.EdgeEstimate(hasConstraint.owner(), hasConstraint.attribute(), hasEdgeEstimate)
                    ));
        }

        private LocalModel modelForIsa(IsaConstraint isaConstraint, @Nullable Concludable correspondingConcludable) {
            ThingVariable owner = isaConstraint.owner();
            double estimate = countPersistedThingsMatchingType(owner);
            if (correspondingConcludable != null) {
                estimate += estimateInferredAnswerCount(correspondingConcludable, set(owner));
            }
            return new LocalModel(set(new LocalModel.VariableEstimate(owner, estimate)), set());
        }

        public LocalModel modelForPredicate(PredicateConstraint predicateConstraint, @Nullable Concludable correspondingConcludable) {
            if (predicateConstraint.predicate().isValueIdentity()) {
                return new LocalModel(set(new LocalModel.VariableEstimate(predicateConstraint.owner(), 1.0)), set());
            } else {
                List<LocalModel.VariableEstimate> variableModels = variableModelsBasedOnType(predicateConstraint.variables(), correspondingConcludable);
                if ( predicateConstraint.predicate().isThingVar() && predicateConstraint.predicate().predicate().equals(TypeQLToken.Predicate.Equality.EQ)) {
                    double betterEstimate = Math.min(variableModels.get(0).estimate, variableModels.get(1).estimate);
                    return new LocalModel(
                            set(
                                    new LocalModel.VariableEstimate(variableModels.get(0).variable, betterEstimate),
                                    new LocalModel.VariableEstimate(variableModels.get(1).variable, betterEstimate)
                            ),
                            set(
                                    new LocalModel.EdgeEstimate(variableModels.get(0).variable, variableModels.get(1).variable, betterEstimate)
                            )
                    );
                } else {
                    return new LocalModel(new HashSet<>(variableModels), set());
                }
            }
        }

        public LocalModel modelForIID(IIDConstraint iidConstraint) {
            return new LocalModel(set(new LocalModel.VariableEstimate(iidConstraint.owner(), 1.0)), set());
        }

        public LocalModel modelForIs(IsConstraint isConstraint, @Nullable Concludable correspondingConcludable) {
            List<LocalModel.VariableEstimate> variableModels = variableModelsBasedOnType(isConstraint.variables(), correspondingConcludable);
            double betterEstimate = Math.min(variableModels.get(0).estimate, variableModels.get(1).estimate);
            return new LocalModel(
                    set(
                            new LocalModel.VariableEstimate(variableModels.get(0).variable, betterEstimate),
                            new LocalModel.VariableEstimate(variableModels.get(1).variable, betterEstimate)
                    ),
                    set(
                            new LocalModel.EdgeEstimate(variableModels.get(0).variable, variableModels.get(1).variable, 1)
                    )
            );
        }

        public LocalModel variableModelForCyclicConcludable(Concludable correspondingConcludable) {
            List<LocalModel.VariableEstimate> vertices = variableModelsBasedOnType(correspondingConcludable.variables(), correspondingConcludable);

            Set<LocalModel.EdgeEstimate> edges = new HashSet<>();
            if (correspondingConcludable.isHas()) {
                assert vertices.size() == 2;
                edges.add(new LocalModel.EdgeEstimate(vertices.get(0).variable, vertices.get(1).variable, vertices.get(0).estimate * vertices.get(1).estimate));
            } else if (correspondingConcludable.isRelation()) {
                Variable relationVar = correspondingConcludable.asRelation().relation().owner();
                LocalModel.VariableEstimate relationEstimate = iterate(vertices).filter(vertex -> vertex.variable == relationVar).next();
                vertices.remove(relationEstimate);

                double fullyConnectedUpperBound = iterate(vertices).map(vertex -> vertex.estimate).reduce(1.0, (x, y) -> x * y);
                for (LocalModel.VariableEstimate vertex : vertices) {
                    edges.add(new LocalModel.EdgeEstimate(relationVar, vertex.variable, fullyConnectedUpperBound));
                }
                List<LocalModel.VariableEstimate> oldVertices = vertices;
                vertices = new ArrayList<>();
                vertices.add(new LocalModel.VariableEstimate(relationVar, fullyConnectedUpperBound));
                iterate(oldVertices)
                        .map(oldEstimate -> new LocalModel.VariableEstimate(oldEstimate.variable, Math.min(fullyConnectedUpperBound, oldEstimate.estimate)))
                        .forEachRemaining(vertices::add);
            }

            return new LocalModel(new HashSet<>(vertices), edges);
        }

        private double estimateInferredAnswerCount(Concludable concludable, Set<Variable> variableFilter) {
            Map<Rule, Set<Unifier>> unifiers = answerCountEstimator.logicMgr.applicableRules(concludable);
            double inferredEstimate = 0;
            for (Rule rule : unifiers.keySet()) {
                for (Unifier unifier : unifiers.get(rule)) {
                    Set<Identifier.Variable> ruleSideIds = iterate(variableFilter).filter(v -> v.id().isRetrievable())
                            .flatMap(v -> iterate(unifier.mapping().get(v.id().asRetrievable()))).toSet();
                    if ((concludable.isRelation() || concludable.isIsa())
                            && rule.conclusion().generating().isPresent() && ruleSideIds.contains(rule.conclusion().generating().get().id())) {
                        // There is one generated variable per combination of ALL variables in the conclusion
                        ruleSideIds = new HashSet<>(rule.conclusion().conjunction().pattern().retrieves());
                    }

                    for (Rule.Condition.ConditionBranch conditionBranch : rule.condition().branches()) {
                        Set<Variable> ruleSideVariables = iterate(ruleSideIds)
                                .filter(id -> conditionBranch.conjunction().pattern().retrieves().contains(id))
                                .map(id -> conditionBranch.conjunction().pattern().variable(id)).toSet();
                        double inferredEstimateForThisBranch = answerCountEstimator.estimateAnswers(conditionBranch.conjunction(), ruleSideVariables);

                        Set<Concludable> cyclicConcludables = answerCountEstimator.conjunctionGraph.conjunctionNode(conditionBranch.conjunction()).cyclicConcludables();
                        if (concludable.isRelation() && inferredEstimateForThisBranch > 0 && !cyclicConcludables.isEmpty()) {
                            Set<Variable> recursivePlayers = iterate(cyclicConcludables).flatMap(c -> iterate(c.variables()))
                                    .filter(v -> v.isThing() && ruleSideVariables.contains(v))
                                    .toSet();
                            Set<Variable> nonRecursivePlayers = iterate(ruleSideVariables).filter(v -> v.isThing() && !recursivePlayers.contains(v)).toSet();

                            Map<Variable, Double> estimateForRecursivePlayer = new HashMap<>();
                            // TODO: we might get better estimates by only considering non-recursive cases, but getting it right may be more complicated.
                            recursivePlayers.forEach(v -> estimateForRecursivePlayer.put(v, answerCountEstimator.estimateAnswers(conditionBranch.conjunction(), set(v))));

                            // All possible combinations (of non-recursive players) assumes full-connectivity, producing an unrealistically large/worst-case estimate.
                            // Instead, we model each role-player as being recursively related to sqrt(|r_i|) instances of each other role-player r_i.
                            double rootOfAll = Math.max(1.0, Math.sqrt(iterate(estimateForRecursivePlayer.values()).reduce(1.0, (x, y) -> x * y)));
                            double recursivelyConnectedEstimate = iterate(estimateForRecursivePlayer.values()).map(x -> rootOfAll * Math.max(1.0, Math.sqrt(x))).reduce(0.0, Double::sum);

                            double estimateForNonRecursivePlayers = answerCountEstimator.estimateAnswers(conditionBranch.conjunction(), nonRecursivePlayers);
                            double heuristicUpperBound = Math.ceil(estimateForNonRecursivePlayers * recursivelyConnectedEstimate);
                            inferredEstimate += Math.min(inferredEstimateForThisBranch, heuristicUpperBound);
                        } else {
                            inferredEstimate += inferredEstimateForThisBranch;
                        }
                    }
                }
            }

            return inferredEstimate;
        }

        private List<LocalModel.VariableEstimate> variableModelsBasedOnType(Set<Variable> variables, @Nullable Concludable correspondingConcludable) {
            List<LocalModel.VariableEstimate> variableModels = new ArrayList<>();
            iterate(variables).filter(Variable::isThing).map(Variable::asThing)
                    .forEachRemaining(variable -> {
                        double estimate = countPersistedThingsMatchingType(variable);
                        if (correspondingConcludable != null && (
                                (correspondingConcludable.isHas() && variable.equals(correspondingConcludable.asHas().attribute())) ||
                                        (correspondingConcludable.isAttribute() && variable.equals(correspondingConcludable.asAttribute().attribute()))
                        )) {
                            estimate += attributesCreatedByHasWithIsa(correspondingConcludable);
                        }
                        variableModels.add(new LocalModel.VariableEstimate(variable, estimate));
                    });
            return variableModels;
        }

        private static Label getRoleType(RelationConstraint.RolePlayer player) {
            if (player.roleType().isPresent() && player.roleType().get().label().isPresent()) {
                return player.roleType().get().label().get().properLabel();
            } else if (player.inferredRoleTypes().size() == 1) return iterate(player.inferredRoleTypes()).next();
            else return null;
        }

        private long attributesCreatedByHasWithIsa(Concludable concludable) {
            return iterate(answerCountEstimator.logicMgr.applicableRules(concludable).keySet())
                    .filter(rule -> rule.conclusion().isHasWithIsa())
                    .map(rule -> rule.conclusion().asHasWithIsa().value().predicate().value())
                    .toSet().size();
        }

        private long countPersistedRolePlayers(RelationConstraint.RolePlayer rolePlayer) {
            return graphMgr.data().stats().thingVertexSum(rolePlayer.inferredRoleTypes());
        }

        private long countPersistedThingsMatchingType(ThingVariable thingVar) {
            return graphMgr.data().stats().thingVertexSum(thingVar.inferredTypes());
        }

        private long countPersistedHasEdges(Set<Label> ownerTypes, Set<Label> attributeTypes) {
            return iterate(ownerTypes).map(ownerType ->
                    iterate(attributeTypes)
                            .map(attrType -> graphMgr.data().stats().hasEdgeCount(ownerType, attrType))
                            .reduce(0L, Long::sum)
            ).reduce(0L, Long::sum);
        }
    }
}
