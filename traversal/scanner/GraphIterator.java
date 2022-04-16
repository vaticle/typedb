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

package com.vaticle.typedb.core.traversal.scanner;

import com.vaticle.typedb.core.common.collection.KeyValue;
import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.AbstractFunctionalIterator;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.common.iterator.sorted.SortedIterator.Forwardable;
import com.vaticle.typedb.core.common.iterator.sorted.SortedIterator.Order;
import com.vaticle.typedb.core.graph.GraphManager;
import com.vaticle.typedb.core.graph.vertex.ThingVertex;
import com.vaticle.typedb.core.graph.vertex.Vertex;
import com.vaticle.typedb.core.traversal.Traversal;
import com.vaticle.typedb.core.traversal.common.Identifier;
import com.vaticle.typedb.core.traversal.common.VertexMap;
import com.vaticle.typedb.core.traversal.procedure.GraphProcedure;
import com.vaticle.typedb.core.traversal.procedure.ProcedureEdge;
import com.vaticle.typedb.core.traversal.procedure.ProcedureVertex;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.stream.Collectors;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.RESOURCE_CLOSED;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;
import static com.vaticle.typedb.core.common.iterator.sorted.SortedIterator.ASC;
import static com.vaticle.typedb.core.common.iterator.sorted.SortedIterators.Forwardable.intersect;
import static com.vaticle.typedb.core.common.iterator.sorted.SortedIterators.Forwardable.iterateSorted;
import static java.util.stream.Collectors.toMap;

public class GraphIterator extends AbstractFunctionalIterator<VertexMap> {

    private static final Logger LOG = LoggerFactory.getLogger(GraphIterator.class);

    private final GraphManager graphMgr;
    private final GraphProcedure procedure;
    private final Traversal.Parameters params;
    private final Set<Identifier.Variable.Retrievable> filter;
    private final Map<Identifier, Vertex<?, ?>> answer;
    private final Map<Identifier, Forwardable<Vertex<?, ?>, Order.Asc>> iterators;
    private final Scopes scopes;
    private final int vertexCount;
    private final Vertex<?, ?> start;
    private State state;

    enum State {INIT, EMPTY, FETCHED, COMPLETED}

    public GraphIterator(GraphManager graphMgr, Vertex<?, ?> start, GraphProcedure procedure,
                         Traversal.Parameters params, Set<Identifier.Variable.Retrievable> filter) {
        assert procedure.vertexCount() > 1;
        System.out.println(procedure.toString());
        this.graphMgr = graphMgr;
        this.procedure = procedure;
        this.params = params;
        this.filter = filter;
        this.scopes = new Scopes();
        this.state = State.INIT;
        this.answer = new HashMap<>();
        this.iterators = new HashMap<>();
        this.start = start;
        this.vertexCount = procedure.vertexCount();
    }

    @Override
    public boolean hasNext() {
        try {
            if (state == State.COMPLETED) return false;
            else if (state == State.FETCHED) return true;
            else if (state == State.INIT) {
                initialiseStart();
                if (computeFirst(0)) state = State.FETCHED;
                else setCompleted();
            } else if (state == State.EMPTY) {
                if (computeNext(vertexCount - 1)) state = State.FETCHED;
                else setCompleted();
            } else {
                throw TypeDBException.of(ILLEGAL_STATE);
            }
            return state == State.FETCHED;
        } catch (Throwable e) {
            // note: catching runtime exception until we can gracefully interrupt running queries on tx close
            if (e instanceof TypeDBException && ((TypeDBException) e).code().isPresent() &&
                    ((TypeDBException) e).code().get().equals(RESOURCE_CLOSED.code())) {
                LOG.debug("Transaction was closed during graph iteration");
            } else {
                LOG.error("Parameters: " + params.toString());
                LOG.error("GraphProcedure: " + procedure.toString());
            }
            throw e;
        }
    }

    private void initialiseStart() {
        if (procedure.startVertex().id().isScoped()) {
            Scopes.Scoped scoped = scopes.getOrInitialise(procedure.startVertex().id().asScoped().scope());
            recordScoped(scoped, procedure.startVertex(), start.asThing());
        }
        iterators.put(procedure.startVertex().id(), iterateSorted(ASC, start));
    }

    private boolean computeFirst(int pos) {
        if (pos == vertexCount) return true;
        ProcedureVertex<?, ?> vertex = procedure.vertex(pos);
        Forwardable<Vertex<?, ?>, Order.Asc> iterator = iterators.get(vertex.id());
        assert iterator.hasNext();

        Vertex<?, ?> candidate = iterator.next();

        while (true) {
            boolean verified = verify(pos, vertex, candidate);
            if (verified) {
                answer.put(vertex.id(), candidate);
                if (!computeFirst(pos + 1)) {
                    verified = false;
                }
            }
            if (!verified) {
                mayUnscope(vertex);
                if (iterator.hasNext()) candidate = iterator.next();
                else {
                    iterators.remove(vertex.id());
                    return false;
                }
            } else return true;
        }
    }

    private boolean computeNext(int pos) {
        assert pos < vertexCount;
        if (pos == -1) return false;

        ProcedureVertex<?, ?> vertex = procedure.vertex(pos);
        Forwardable<Vertex<?, ?>, Order.Asc> iterator = iterators.get(vertex.id());
        boolean verified = false;
        Vertex<?, ?> candidate = null;
        while (!verified) {
            if (!iterator.hasNext()) {
                iterators.remove(vertex.id());
                mayUnscope(vertex);
                mayUnscopeIns(vertex);
                if (!computeNext(pos - 1)) return false;
                else {
                    if (!iterators.containsKey(vertex.id())) renewIteratorFromIns(vertex, pos);
                    iterator = iterators.get(vertex.id());
                }
            }
            candidate = iterator.next();
            verified = verify(pos, vertex, candidate);
        }

        answer.put(vertex.id(), candidate);
        return true;
    }

    private boolean verify(int pos, ProcedureVertex<?, ?> vertex, Vertex<?, ?> candidate) {
        // TODO vertex should cache self-closures from ins and outs
        for (ProcedureEdge<?, ?> edge : vertex.outs()) {
            if (edge.to().equals(vertex) && !isClosure(edge, candidate, candidate)) {
                return false;
            }
        }

        Set<ProcedureEdge<?, ?>> forwardVerified = new HashSet<>();
        // TODO for the backtracking to be correct when getting scope multiplicity, we must go over the out edges in order of destination, otherwise we lose answers due to scoping filtering
        for (ProcedureEdge<?, ?> edge : vertex.orderedOuts()) {
            ProcedureVertex<?, ?> to = edge.to();
            if (!to.equals(vertex)) {
                Forwardable<Vertex<?, ?>, Order.Asc> toIter = iterators.containsKey(to.id()) ?
                        intersect(branch(candidate, edge), iterators.get(to.id())) :
                        branch(candidate, edge);
                if (!toIter.hasNext()) {
                    forwardVerified.forEach(e -> {
                        iterators.remove(e.to().id());
                        renewIteratorFromIns(e.to(), pos);
                    });
                    return false;
                } else {
                    forwardVerified.add(edge);
                    iterators.put(to.id(), toIter);
                }
            }
        }
        return true;
    }

    private void mayUnscope(ProcedureVertex<?, ?> vertex) {
        if (vertex.id().isScoped()) {
            scopes.get(vertex.id().asScoped().scope()).removeSource(vertex);
        }
    }

    private void mayUnscopeIns(ProcedureVertex<?, ?> vertex) {
        for (ProcedureEdge<?, ?> edge : vertex.ins()) {
            if (edge.isRolePlayer()) {
                Scopes.Scoped scoped = scopes.get(edge.asRolePlayer().scope());
                if (scoped.containsSource(edge)) scoped.removeSource(edge);
            }
        }
    }

    private void renewIteratorFromIns(ProcedureVertex<?, ?> vertex, int maxInOrder) {
        mayUnscopeIns(vertex);
        List<Forwardable<Vertex<?, ?>, Order.Asc>> iters = new ArrayList<>();
        for (ProcedureEdge<?, ?> edge : vertex.ins()) {
            if (edge.from().equals(vertex) || edge.from().order() >= maxInOrder) continue;
            iters.add(branch(answer.get(edge.from().id()), edge));
        }
        iterators.put(vertex.id(), intersect(iterate(iters), ASC));
    }

    @Override
    public VertexMap next() {
        if (!hasNext()) throw new NoSuchElementException();
        state = State.EMPTY;
        return toVertexMap(answer);
    }

    private void setCompleted() {
        state = State.COMPLETED;
        recycle();
    }

    private boolean isClosure(ProcedureEdge<?, ?> edge, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex) {
        if (edge.isRolePlayer()) {
            Scopes.Scoped scoped = scopes.getOrInitialise(edge.asRolePlayer().scope());
            return edge.asRolePlayer().isClosure(graphMgr, fromVertex, toVertex, params, scoped);
        } else {
            return edge.isClosure(graphMgr, fromVertex, toVertex, params);
        }
    }

    private Forwardable<Vertex<?, ?>, Order.Asc> branch(Vertex<?, ?> fromVertex, ProcedureEdge<?, ?> edge) {
        Forwardable<? extends Vertex<?, ?>, Order.Asc> toIter;
        if (edge.to().id().isScoped()) {
            Identifier.Variable scope = edge.to().id().asScoped().scope();
            Scopes.Scoped scoped = scopes.getOrInitialise(scope);
            toIter = edge.branch(graphMgr, fromVertex, params).filter(role -> {
                if (!scoped.isScopedBy(edge.to(), role.asThing()) && scoped.contains(role.asThing())) return false;
                else {
                    recordScoped(scoped, edge.to(), role.asThing());
                    return true;
                }
            });
        } else if (edge.isRolePlayer()) {
            Identifier.Variable scope = edge.asRolePlayer().scope();
            Scopes.Scoped scoped = scopes.getOrInitialise(scope);
            toIter = edge.asRolePlayer().branchEdge(graphMgr, fromVertex, params).filter(thingAndRole -> {
                if (scoped.contains(thingAndRole.value())) return false;
                else {
                    recordScoped(scoped, edge, thingAndRole.value());
                    return true;
                }
            }).mapSorted(KeyValue::key, key -> KeyValue.of(key, null), ASC);
        } else {
            toIter = edge.branch(graphMgr, fromVertex, params);
        }
        if (!edge.to().id().isName() && edge.to().outs().isEmpty() && edge.to().ins().size() == 1) {
            // TODO: This optimisation can apply to more situations, such as to
            //       an entire tree, where none of the leaves are referenced by name
            toIter = toIter.limit(1);
        }

        // TODO: this cast is a tradeoff between losing a lot of type safety in the ProcedureEdge branch() return type vs having a cast
        return (Forwardable<Vertex<?, ?>, Order.Asc>) toIter;
    }

    private void recordScoped(Scopes.Scoped scoped, ProcedureVertex<?, ?> source, ThingVertex role) {
        if (scoped.containsSource(source)) scoped.replace(source, role.asThing());
        else scoped.record(source, role.asThing());
    }

    private void recordScoped(Scopes.Scoped scoped, ProcedureEdge<?, ?> source, ThingVertex role) {
        if (scoped.containsSource(source)) scoped.replace(source, role);
        else scoped.record(source, role);
    }

    private VertexMap toVertexMap(Map<Identifier, Vertex<?, ?>> answer) {
        return VertexMap.of(
                answer.entrySet().stream()
                        .filter(e -> e.getKey().isRetrievable() && filter.contains(e.getKey().asVariable().asRetrievable()))
                        .collect(toMap(e -> e.getKey().asVariable().asRetrievable(), Map.Entry::getValue))
        );
    }

    @Override
    public void recycle() {
        iterators.values().forEach(FunctionalIterator::recycle);
    }


    public static class Scopes {

        private final Map<Identifier.Variable, Scoped> scoped;

        public Scopes() {
            this.scoped = new HashMap<>();
        }

        public Scoped getOrInitialise(Identifier.Variable scope) {
            return scoped.computeIfAbsent(scope, s -> new Scoped());
        }

        public Scoped get(Identifier.Variable scope) {
            assert scoped.containsKey(scope);
            return scoped.get(scope);
        }

        public static class Scoped {

            Set<ThingVertex> roles;
            Map<ProcedureVertex<?, ?>, ThingVertex> vertexSources;
            Map<ProcedureEdge<?, ?>, ThingVertex> edgeSources;

            private Scoped() {
                roles = new HashSet<>();
                vertexSources = new HashMap<>();
                edgeSources = new HashMap<>();
            }

            public boolean isEmpty() {
                return roles.isEmpty();
            }

            public boolean contains(ThingVertex role) {
                return roles.contains(role);
            }

            public boolean containsSource(ProcedureVertex<?, ?> vertex) {
                return vertexSources.containsKey(vertex);
            }

            public boolean containsSource(ProcedureEdge<?, ?> edge) {
                return edgeSources.containsKey(edge);
            }

            public boolean isScopedBy(ProcedureVertex<?, ?> source, ThingVertex role) {
                ThingVertex scopedBySource = vertexSources.get(source);
                return scopedBySource != null && scopedBySource.equals(role);
            }

            public void record(ProcedureEdge<?, ?> source, ThingVertex role) {
                assert !roles.contains(role) && source.isRolePlayer();
                roles.add(role);
                edgeSources.put(source, role);
            }

            public void record(ProcedureVertex<?, ?> source, ThingVertex role) {
                assert !roles.contains(role) && source.id().isScoped();
                roles.add(role);
                vertexSources.put(source, role);
            }

            public void removeSource(ProcedureEdge<?, ?> edge) {
                assert edge.isRolePlayer() && edgeSources.containsKey(edge);
                ThingVertex role = edgeSources.remove(edge);
                roles.remove(role);
            }

            public void removeSource(ProcedureVertex<?, ?> vertex) {
                assert vertex.id().isScoped() && vertexSources.containsKey(vertex);
                ThingVertex role = vertexSources.remove(vertex);
                roles.remove(role);
            }

            public void replace(ProcedureEdge<?, ?> edge, ThingVertex role) {
                assert edge.isRolePlayer();
                ThingVertex oldRole = edgeSources.remove(edge);
                assert roles.contains(oldRole);
                roles.remove(oldRole);
                edgeSources.put(edge, role);
                roles.add(role);
            }

            public void replace(ProcedureVertex<?, ?> vertex, ThingVertex role) {
                assert vertex.id().isScoped();
                ThingVertex oldRole = vertexSources.remove(vertex);
                assert roles.contains(oldRole);
                roles.remove(oldRole);
                vertexSources.put(vertex, role);
                roles.add(role);
            }

            public void clear() {
                roles.clear();
                vertexSources.clear();
                edgeSources.clear();
            }
        }
    }
}
