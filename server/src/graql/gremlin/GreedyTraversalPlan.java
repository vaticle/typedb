/*
 * GRAKN.AI - THE KNOWLEDGE GRAPH
 * Copyright (C) 2018 Grakn Labs Ltd
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

package grakn.core.graql.gremlin;

import com.google.common.collect.Iterators;
import com.google.common.collect.Sets;
import grakn.core.concept.type.Type;
import grakn.core.graql.gremlin.fragment.Fragment;
import grakn.core.graql.gremlin.fragment.InIsaFragment;
import grakn.core.graql.gremlin.fragment.InSubFragment;
import grakn.core.graql.gremlin.fragment.LabelFragment;
import grakn.core.graql.gremlin.fragment.ValueFragment;
import grakn.core.graql.gremlin.spanningtree.Arborescence;
import grakn.core.graql.gremlin.spanningtree.ChuLiuEdmonds;
import grakn.core.graql.gremlin.spanningtree.graph.DirectedEdge;
import grakn.core.graql.gremlin.spanningtree.graph.Node;
import grakn.core.graql.gremlin.spanningtree.graph.NodeId;
import grakn.core.graql.gremlin.spanningtree.graph.SparseWeightedGraph;
import grakn.core.graql.gremlin.spanningtree.util.Weighted;
import grakn.core.server.session.TransactionOLTP;
import graql.lang.pattern.Conjunction;
import graql.lang.pattern.Pattern;
import graql.lang.statement.Statement;
import graql.lang.statement.Variable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static grakn.core.common.util.CommonUtil.toImmutableSet;
import static grakn.core.graql.gremlin.RelationTypeInference.inferRelationTypes;
import static grakn.core.graql.gremlin.fragment.Fragment.SHARD_LOAD_FACTOR;

/**
 * Class for generating greedy traversal plans
 *
 */
public class GreedyTraversalPlan {

    protected static final Logger LOG = LoggerFactory.getLogger(GreedyTraversalPlan.class);

    /**
     * Create a traversal plan.
     *
     * @param pattern a pattern to find a query plan for
     * @return a semi-optimal traversal plan
     */
    public static GraqlTraversal createTraversal(Pattern pattern, TransactionOLTP tx) {
        Collection<Conjunction<Statement>> patterns = pattern.getDisjunctiveNormalForm().getPatterns();

        Set<? extends List<Fragment>> fragments = patterns.stream()
                .map(conjunction -> new ConjunctionQuery(conjunction, tx))
                .map((ConjunctionQuery query) -> planForConjunction(query, tx))
                .collect(toImmutableSet());

        return GraqlTraversal.create(fragments);
    }

    /**
     * Create a plan using Edmonds' algorithm with greedy approach to execute a single conjunction
     *
     * @param query the conjunction query to find a traversal plan
     * @return a semi-optimal traversal plan to execute the given conjunction
     */
    private static List<Fragment> planForConjunction(ConjunctionQuery query, TransactionOLTP tx) {

        final List<Fragment> plan = new ArrayList<>(); // this will be the final plan

        final Set<Node> connectedNodes = new HashSet<>();
        final Map<Node, Double> nodesWithFixedCost = new HashMap<>();

        // getting all the fragments from the conjunction query
        final Set<Fragment> allFragments = query.getEquivalentFragmentSets().stream()
                .flatMap(EquivalentFragmentSet::stream).collect(Collectors.toSet());

        // if role p[ayers' types are known, we can infer the types of the relation
        // then add a label fragment to the fragment set
        Set<Fragment> inferredFragments = inferRelationTypes(tx, allFragments);
        allFragments.addAll(inferredFragments);

        // initialise all the nodes for the spanning tree
        final Map<NodeId, Node> allNodes = new HashMap<>(); // all the nodes in the spanning tree
        for (Fragment fragment : allFragments) {
            fragment.getNodes().forEach(node -> allNodes.put(node.getNodeId(), node));
        }

        // it's possible that some (or all) fragments are disconnect
        // e.g. $x isa person; $y isa dog;
        // these are valid conjunctions and useful when inserting new data
        Collection<Set<Fragment>> connectedFragmentSets =
                getConnectedFragmentSets(plan, allFragments, allNodes, connectedNodes,  nodesWithFixedCost, tx);

        // generate plan for each connected set of fragments
        // since each set is independent, order of the set doesn't matter
        connectedFragmentSets.forEach(fragmentSet -> {

            final Map<Node, Map<Node, Fragment>> edges = new HashMap<>();

            final Set<Node> highPriorityStartingNodeSet = new HashSet<>();
            final Set<Node> lowPriorityStartingNodeSet = new HashSet<>();
            final Set<Fragment> edgeFragmentSet = new HashSet<>();

            fragmentSet.forEach(fragment -> {
                if (fragment.end() != null) {
                    edgeFragmentSet.add(fragment);
                    // when we are have more info from the cache, e.g. instance count,
                    // we can have a better estimate on the cost of the fragment
                    updateFragmentCost(allNodes, nodesWithFixedCost, fragment);

                } else if (fragment.hasFixedFragmentCost()) {
                    Node node = allNodes.get(new NodeId(NodeId.NodeType.VAR, fragment.start()));
                    if (fragment instanceof LabelFragment) {
                        Type type = tx.getType(Iterators.getOnlyElement(((LabelFragment) fragment).labels().iterator()));
                        if (type != null && type.isImplicit()) {
                            // implicit types have low priority because their instances may be edges
                            lowPriorityStartingNodeSet.add(node);
                        } else {
                            // other labels/types are the ideal starting point as they are indexed
                            highPriorityStartingNodeSet.add(node);
                        }
                    } else {
                        highPriorityStartingNodeSet.add(node);
                    }
                }
            });

            // convert fragments to a connected graph
            Set<Weighted<DirectedEdge>> weightedGraph = buildWeightedGraph(
                    allNodes, connectedNodes, edges, edgeFragmentSet);

            if (!weightedGraph.isEmpty()) {
                // sparse graph for better performance
                SparseWeightedGraph sparseWeightedGraph = SparseWeightedGraph.from(weightedGraph);

                // selecting starting points
                Collection<Node> startingNodes;
                if (!highPriorityStartingNodeSet.isEmpty()) {
                    startingNodes = highPriorityStartingNodeSet;
                } else if (!lowPriorityStartingNodeSet.isEmpty()) {
                    startingNodes = lowPriorityStartingNodeSet;
                } else {
                    // if all else fails, use any valid nodes
                    startingNodes = sparseWeightedGraph.getNodes().stream()
                            .filter(Node::isValidStartingPoint).collect(Collectors.toSet());
                }

                // find the minimum spanning tree for each root
                // then get the tree with minimum weight
                Arborescence<Node> arborescence = startingNodes.stream()
                        .map(node -> ChuLiuEdmonds.getMaxArborescence(sparseWeightedGraph, node))
                        .max(Comparator.comparingDouble(tree -> tree.weight))
                        .map(arborescenceInside -> arborescenceInside.val).orElse(Arborescence.empty());
                greedyTraversal(plan, arborescence, allNodes, edges);
            }
            addUnvisitedNodeFragments(plan, allNodes, connectedNodes);
        });


        // add disconnected fragment set with no edge fragment
        addUnvisitedNodeFragments(plan, allNodes, allNodes.values());
        LOG.trace("Greedy Plan = {}", plan);
        return plan;
    }


    // add unvisited node fragments to plan for each connected fragment set
    private static void addUnvisitedNodeFragments(List<Fragment> plan,
                                                  Map<NodeId, Node> allNodes,
                                                  Collection<Node> connectedNodes) {

        Set<Node> nodeWithFragment = connectedNodes.stream()
                // make sure the fragment either have no dependency or dependencies have been dealt with
                .filter(node -> !node.getFragmentsWithoutDependency().isEmpty() ||
                        !node.getFragmentsWithDependencyVisited().isEmpty())
                .collect(Collectors.toSet());
        while (!nodeWithFragment.isEmpty()) {
            nodeWithFragment.forEach(node -> addNodeFragmentToPlan(node, plan, allNodes, false));
            nodeWithFragment = connectedNodes.stream()
                    .filter(node -> !node.getFragmentsWithoutDependency().isEmpty() ||
                            !node.getFragmentsWithDependencyVisited().isEmpty())
                    .collect(Collectors.toSet());
        }
    }

    // return a collection of set, in each set, all the fragments are connected
    private static Collection<Set<Fragment>> getConnectedFragmentSets(
            List<Fragment> plan, Set<Fragment> allFragments,
            Map<NodeId, Node> allNodes, Set<Node> connectedNodes,
            Map<Node, Double> nodesWithFixedCost, TransactionOLTP tx) {

        allFragments.forEach(fragment -> {
            if (fragment.end() == null) {
                processFragmentWithFixedCost(plan, allNodes, connectedNodes, nodesWithFixedCost, tx, fragment);
            }

            if (!fragment.dependencies().isEmpty()) {
                processFragmentWithDependencies(allNodes, fragment);
            }
        });

        // process sub fragments here as we probably need to break the query tree
        processSubFragment(allNodes, nodesWithFixedCost, allFragments);


        // TODO this could be implemented in a more readable way (ie using a graph + BFS etc.)

        final Map<Integer, Set<Variable>> varSetMap = new HashMap<>();
        final Map<Integer, Set<Fragment>> fragmentSetMap = new HashMap<>();
        final int[] index = {0};
        allFragments.forEach(fragment -> {
            Set<Variable> fragmentVarNameSet = Sets.newHashSet(fragment.vars());
            List<Integer> setsWithVarInCommon = new ArrayList<>();
            varSetMap.forEach((setIndex, varNameSet) -> {
                if (!Collections.disjoint(varNameSet, fragmentVarNameSet)) {
                    setsWithVarInCommon.add(setIndex);
                }
            });

            if (setsWithVarInCommon.isEmpty()) {
                index[0] += 1;
                varSetMap.put(index[0], fragmentVarNameSet);
                fragmentSetMap.put(index[0], Sets.newHashSet(fragment));
            } else {
                Iterator<Integer> iterator = setsWithVarInCommon.iterator();
                Integer firstSet = iterator.next();
                varSetMap.get(firstSet).addAll(fragmentVarNameSet);
                fragmentSetMap.get(firstSet).add(fragment);
                while (iterator.hasNext()) {
                    Integer nextSet = iterator.next();
                    varSetMap.get(firstSet).addAll(varSetMap.remove(nextSet));
                    fragmentSetMap.get(firstSet).addAll(fragmentSetMap.remove(nextSet));
                }
            }
        });
        return fragmentSetMap.values();
    }

    private static void processFragmentWithFixedCost(List<Fragment> plan,
                                                     Map<NodeId, Node> allNodes,
                                                     Set<Node> connectedNodes,
                                                     Map<Node, Double> nodesWithFixedCost,
                                                     TransactionOLTP tx, Fragment fragment) {

        Node start = allNodes.get(new NodeId(NodeId.NodeType.VAR, fragment.start()));
        connectedNodes.add(start);

        if (fragment.hasFixedFragmentCost()) {
            // fragments that are constant time access should be computed first
            plan.add(fragment);

            // set the weight of the node as a starting point based on log(number of this node)
            double logInstanceCount;
            if (fragment instanceof LabelFragment) {
                // only LabelFragment (corresponding to type vertices) can be sharded
                Long shardCount = ((LabelFragment) fragment).getShardCount(tx);
                logInstanceCount = Math.log(shardCount - 1D + SHARD_LOAD_FACTOR) +
                        Math.log(tx.shardingThreshold());
            } else {
                logInstanceCount = -1D;
            }
            nodesWithFixedCost.put(start, logInstanceCount);
            start.setFixedFragmentCost(fragment.fragmentCost());

        } else if (fragment.dependencies().isEmpty()) {
            //fragments that should be done when a node has been visited
            start.getFragmentsWithoutDependency().add(fragment);
        }
    }

    private static void processFragmentWithDependencies(Map<NodeId, Node> allNodes, Fragment fragment) {
        // it's either neq or value fragment
        Node start = allNodes.get(new NodeId(NodeId.NodeType.VAR, fragment.start()));
        Node other = allNodes.get(new NodeId(NodeId.NodeType.VAR, fragment.dependencies().iterator().next()));

        start.getFragmentsWithDependency().add(fragment);
        other.getDependants().add(fragment);

        // check whether it's value fragment
        if (fragment instanceof ValueFragment) {
            // as value fragment is not symmetric, we need to add it again
            other.getFragmentsWithDependency().add(fragment);
            start.getDependants().add(fragment);
        }
    }

    // if in-sub starts from an indexed supertype, update the fragment cost of in-isa starting from the subtypes
    private static void processSubFragment(Map<NodeId, Node> allNodes,
                                           Map<Node, Double> nodesWithFixedCost,
                                           Set<Fragment> allFragments) {

        Set<Fragment> validSubFragments = allFragments.stream().filter(fragment -> {
            if (fragment instanceof InSubFragment) {
                Node superType = allNodes.get(new NodeId(NodeId.NodeType.VAR, fragment.start()));
                if (nodesWithFixedCost.containsKey(superType) && nodesWithFixedCost.get(superType) > 0D) {
                    Node subType = allNodes.get(new NodeId(NodeId.NodeType.VAR, fragment.end()));
                    return !nodesWithFixedCost.containsKey(subType);
                }
            }
            return false;
        }).collect(Collectors.toSet());

        if (!validSubFragments.isEmpty()) {
            validSubFragments.forEach(fragment -> {
                // TODO: should decrease the weight of sub type after each level
                nodesWithFixedCost.put(new Node(new NodeId(NodeId.NodeType.VAR, fragment.end())),
                        nodesWithFixedCost.get(new Node(new NodeId(NodeId.NodeType.VAR, fragment.start()))));
            });
            // recursively process all the sub fragments
            processSubFragment(allNodes, nodesWithFixedCost, allFragments);
        }
    }

    private static void updateFragmentCost(Map<NodeId, Node> allNodes,
                                           Map<Node, Double> nodesWithFixedCost,
                                           Fragment fragment) {

        // ideally, this is where we update fragment cost after we get more info and statistics of the graph
        // however, for now, only shard count is available, which is used to infer number of instances of a type
        if (fragment instanceof InIsaFragment) {
            Node type = allNodes.get(new NodeId(NodeId.NodeType.VAR, fragment.start()));
            if (nodesWithFixedCost.containsKey(type) && nodesWithFixedCost.get(type) > 0) {
                fragment.setAccurateFragmentCost(nodesWithFixedCost.get(type));
            }
        }
    }

    private static Set<Weighted<DirectedEdge>> buildWeightedGraph(Map<NodeId, Node> allNodes,
                                                                        Set<Node> connectedNodes,
                                                                        Map<Node, Map<Node, Fragment>> edges,
                                                                        Set<Fragment> edgeFragmentSet) {

        final Set<Weighted<DirectedEdge>> weightedGraph = new HashSet<>();
        edgeFragmentSet.stream()
                .flatMap(fragment -> fragment.directedEdges(allNodes, edges).stream())
                // add each edge together with its weight
                .forEach(weightedDirectedEdge -> {
                    weightedGraph.add(weightedDirectedEdge);
                    connectedNodes.add(weightedDirectedEdge.val.destination);
                    connectedNodes.add(weightedDirectedEdge.val.source);
                });
        return weightedGraph;
    }

    // standard tree traversal from the root node
    // always visit the branch/node with smaller cost
    private static void greedyTraversal(List<Fragment> plan, Arborescence<Node> arborescence,
                                        Map<NodeId, Node> nodes,
                                        Map<Node, Map<Node, Fragment>> edgeFragmentChildToParent) {

        Map<Node, Set<Node>> edgesParentToChild = new HashMap<>();
        arborescence.getParents().forEach((child, parent) -> {
            if (!edgesParentToChild.containsKey(parent)) {
                edgesParentToChild.put(parent, new HashSet<>());
            }
            edgesParentToChild.get(parent).add(child);
        });

        Node root = arborescence.getRoot();

        Set<Node> reachableNodes = Sets.newHashSet(root);
        // expanding from the root until all nodes have been visited
        while (!reachableNodes.isEmpty()) {

            Node nodeWithMinCost = reachableNodes.stream().min(Comparator.comparingDouble(node ->
                    branchWeight(node, arborescence, edgesParentToChild, edgeFragmentChildToParent))).orElse(null);

            assert nodeWithMinCost != null : "reachableNodes is never empty, so there is always a minimum";

            // add edge fragment first, then node fragments
            Fragment fragment = getEdgeFragment(nodeWithMinCost, arborescence, edgeFragmentChildToParent);
            if (fragment != null) plan.add(fragment);

            addNodeFragmentToPlan(nodeWithMinCost, plan, nodes, true);

            reachableNodes.remove(nodeWithMinCost);
            if (edgesParentToChild.containsKey(nodeWithMinCost)) {
                reachableNodes.addAll(edgesParentToChild.get(nodeWithMinCost));
            }
        }
    }

    // recursively compute the weight of a branch
    private static double branchWeight(Node node, Arborescence<Node> arborescence,
                                       Map<Node, Set<Node>> edgesParentToChild,
                                       Map<Node, Map<Node, Fragment>> edgeFragmentChildToParent) {

        Double nodeWeight = node.getNodeWeight();

        if (nodeWeight == null) {
            nodeWeight = getEdgeFragmentCost(node, arborescence, edgeFragmentChildToParent) + nodeFragmentWeight(node);
            node.setNodeWeight(nodeWeight);
        }

        Double branchWeight = node.getBranchWeight();

        if (branchWeight == null) {
            final double[] weight = {nodeWeight};
            if (edgesParentToChild.containsKey(node)) {
                edgesParentToChild.get(node).forEach(child ->
                        weight[0] += branchWeight(child, arborescence, edgesParentToChild, edgeFragmentChildToParent));
            }
            branchWeight = weight[0];
            node.setBranchWeight(branchWeight);
        }

        return branchWeight;
    }

    // compute the total cost of a node
    private static double nodeFragmentWeight(Node node) {
        double costFragmentsWithoutDependency = node.getFragmentsWithoutDependency().stream()
                .mapToDouble(Fragment::fragmentCost).sum();
        double costFragmentsWithDependencyVisited = node.getFragmentsWithDependencyVisited().stream()
                .mapToDouble(Fragment::fragmentCost).sum();
        double costFragmentsWithDependency = node.getFragmentsWithDependency().stream()
                .mapToDouble(Fragment::fragmentCost).sum();
        return costFragmentsWithoutDependency + node.getFixedFragmentCost() +
                (costFragmentsWithDependencyVisited + costFragmentsWithDependency) / 2D;
    }

    // adding a node's fragments to plan, updating dependants' dependency map
    private static void addNodeFragmentToPlan(Node node, List<Fragment> plan, Map<NodeId, Node> nodes,
                                              boolean visited) {
        if (!visited) {
            node.getFragmentsWithoutDependency().stream()
                    .min(Comparator.comparingDouble(Fragment::fragmentCost))
                    .ifPresent(firstNodeFragment -> {
                        plan.add(firstNodeFragment);
                        node.getFragmentsWithoutDependency().remove(firstNodeFragment);
                    });
        }
        node.getFragmentsWithoutDependency().addAll(node.getFragmentsWithDependencyVisited());
        plan.addAll(node.getFragmentsWithoutDependency().stream()
                .sorted(Comparator.comparingDouble(Fragment::fragmentCost))
                .collect(Collectors.toList()));

        node.getFragmentsWithoutDependency().clear();
        node.getFragmentsWithDependencyVisited().clear();

        // telling their dependants that they have been visited
        node.getDependants().forEach(fragment -> {
            Node otherNode = nodes.get(new NodeId(NodeId.NodeType.VAR, fragment.start()));
            if (node.equals(otherNode)) {
                otherNode = nodes.get(new NodeId(NodeId.NodeType.VAR, fragment.dependencies().iterator().next()));
            }
            otherNode.getDependants().remove(fragment.getInverse());
            otherNode.getFragmentsWithDependencyVisited().add(fragment);

        });
        node.getDependants().clear();
    }

    // get edge fragment cost in order to map branch cost
    private static double getEdgeFragmentCost(Node node, Arborescence<Node> arborescence,
                                              Map<Node, Map<Node, Fragment>> edgeToFragment) {

        Fragment fragment = getEdgeFragment(node, arborescence, edgeToFragment);
        if (fragment != null) return fragment.fragmentCost();

        return 0D;
    }

    @Nullable
    private static Fragment getEdgeFragment(Node node, Arborescence<Node> arborescence,
                                                      Map<Node, Map<Node, Fragment>> edgeToFragment) {
        if (edgeToFragment.containsKey(node) &&
                edgeToFragment.get(node).containsKey(arborescence.getParents().get(node))) {
            return edgeToFragment.get(node).get(arborescence.getParents().get(node));
        }
        return null;
    }
}
