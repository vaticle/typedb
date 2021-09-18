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

package com.vaticle.typedb.core.traversal.procedure;

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.common.parameters.Label;
import com.vaticle.typedb.core.graph.GraphManager;
import com.vaticle.typedb.core.graph.TypeGraph;
import com.vaticle.typedb.core.graph.adjacency.ThingAdjacency;
import com.vaticle.typedb.core.graph.common.Encoding;
import com.vaticle.typedb.core.graph.edge.ThingEdge;
import com.vaticle.typedb.core.graph.edge.TypeEdge;
import com.vaticle.typedb.core.graph.iid.PrefixIID;
import com.vaticle.typedb.core.graph.iid.VertexIID;
import com.vaticle.typedb.core.graph.vertex.AttributeVertex;
import com.vaticle.typedb.core.graph.vertex.ThingVertex;
import com.vaticle.typedb.core.graph.vertex.TypeVertex;
import com.vaticle.typedb.core.graph.vertex.Vertex;
import com.vaticle.typedb.core.traversal.GraphTraversal;
import com.vaticle.typedb.core.traversal.common.Identifier;
import com.vaticle.typedb.core.traversal.graph.TraversalEdge;
import com.vaticle.typedb.core.traversal.scanner.GraphIterator;
import com.vaticle.typedb.core.traversal.planner.PlannerEdge;
import com.vaticle.typedb.core.traversal.predicate.Predicate;
import com.vaticle.typeql.lang.common.TypeQLToken;

import java.util.HashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import static com.vaticle.typedb.common.util.Objects.className;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_CAST;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_OPERATION;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.UNRECOGNISED_VALUE;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.UNSUPPORTED_OPERATION;
import static com.vaticle.typedb.core.common.iterator.Iterators.empty;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;
import static com.vaticle.typedb.core.common.iterator.Iterators.link;
import static com.vaticle.typedb.core.common.iterator.Iterators.loop;
import static com.vaticle.typedb.core.common.iterator.Iterators.single;
import static com.vaticle.typedb.core.common.iterator.Iterators.tree;
import static com.vaticle.typedb.core.graph.common.Encoding.Direction.Edge.BACKWARD;
import static com.vaticle.typedb.core.graph.common.Encoding.Direction.Edge.FORWARD;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.ISA;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Thing.Base.HAS;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Thing.Base.PLAYING;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Thing.Base.RELATING;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Thing.Optimised.ROLEPLAYER;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Type.OWNS;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Type.OWNS_KEY;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Type.PLAYS;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Type.RELATES;
import static com.vaticle.typedb.core.graph.common.Encoding.Edge.Type.SUB;
import static com.vaticle.typedb.core.graph.common.Encoding.Prefix.VERTEX_ATTRIBUTE;
import static com.vaticle.typedb.core.graph.common.Encoding.Prefix.VERTEX_ROLE;
import static com.vaticle.typedb.core.graph.common.Encoding.Vertex.Thing.RELATION;
import static com.vaticle.typedb.core.traversal.predicate.PredicateOperator.Equality.EQ;
import static com.vaticle.typedb.core.traversal.procedure.ProcedureVertex.Thing.filterAttributes;

public abstract class ProcedureEdge<
        VERTEX_FROM extends ProcedureVertex<?, ?>, VERTEX_TO extends ProcedureVertex<?, ?>
        > extends TraversalEdge<VERTEX_FROM, VERTEX_TO> {

    private final int order;
    private final Encoding.Direction.Edge direction;

    private ProcedureEdge(VERTEX_FROM from, VERTEX_TO to, int order, Encoding.Direction.Edge direction, String symbol) {
        super(from, to, symbol);
        this.order = order;
        this.direction = direction;
    }

    public static ProcedureEdge<?, ?> of(ProcedureVertex<?, ?> from, ProcedureVertex<?, ?> to,
                                         PlannerEdge.Directional<?, ?> plannerEdge) {
        int order = plannerEdge.orderNumber();
        Encoding.Direction.Edge dir = plannerEdge.direction();
        if (plannerEdge.isEqual()) {
            return new Equal(from, to, order, dir);
        } else if (plannerEdge.isPredicate()) {
            return new Predicate(from.asThing(), to.asThing(), order, dir, plannerEdge.asPredicate().predicate());
        } else if (plannerEdge.isNative()) {
            return Native.of(from, to, plannerEdge.asNative());
        } else {
            throw TypeDBException.of(UNRECOGNISED_VALUE);
        }
    }

    public abstract FunctionalIterator<? extends Vertex<?, ?>> branch(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                                                      GraphTraversal.Thing.Parameters params);

    public abstract boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                      GraphTraversal.Thing.Parameters params);

    public int order() {
        return order;
    }

    public Encoding.Direction.Edge direction() {
        return direction;
    }

    public boolean isClosureEdge() {
        return to().isStartingVertex() || order() > to().branchEdge().order();
    }

    public boolean onlyStartsFromAttribute() {
        return false;
    }

    public boolean onlyStartsFromRelation() {
        return false;
    }

    public boolean onlyEndsAtRelation() {
        return false;
    }

    public boolean onlyStartsFromAttributeType() {
        return false;
    }

    public boolean onlyStartsFromRelationType() {
        return false;
    }

    public boolean onlyStartsFromRoleType() {
        return false;
    }

    public boolean onlyStartsFromThingType() {
        return false;
    }

    public boolean isRolePlayer() {
        return false;
    }

    public Native.Thing.RolePlayer asRolePlayer() {
        throw TypeDBException.of(ILLEGAL_CAST, className(getClass()), className(Native.Thing.RolePlayer.class));
    }

    @Override
    public String toString() {
        if (direction.isForward()) {
            return String.format("%s: (%s *--[%s]--> %s)", order, from.id(), symbol, to.id());
        } else {
            return String.format("%s: (%s <--[%s]--* %s)", order, from.id(), symbol, to.id());
        }
    }

    public abstract ProcedureEdge<?,?> reverse();

    public static class Equal extends ProcedureEdge<ProcedureVertex<?, ?>, ProcedureVertex<?, ?>> {

        Equal(ProcedureVertex<?, ?> from, ProcedureVertex<?, ?> to,
              int order, Encoding.Direction.Edge direction) {
            super(from, to, order, direction, TypeQLToken.Predicate.Equality.EQ.toString());
        }

        @Override
        public FunctionalIterator<? extends Vertex<?, ?>> branch(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                                                 GraphTraversal.Thing.Parameters params) {
            if (fromVertex.isThing()) {
                if (to.isType()) return empty();
                else return to.asThing().filter(single(fromVertex.asThing()), params);
            } else if (fromVertex.isType()) {
                if (to.isThing()) return empty();
                else return to.asType().filter(single(fromVertex.asType()));
            } else {
                throw TypeDBException.of(ILLEGAL_STATE);
            }
        }

        @Override
        public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                 Vertex<?, ?> toVertex, GraphTraversal.Thing.Parameters params) {
            assert fromVertex != null && toVertex != null;
            return fromVertex.equals(toVertex);
        }

        @Override
        public ProcedureEdge<?, ?> reverse() {
            Encoding.Direction.Edge reverseDirection = direction().isForward() ? BACKWARD : FORWARD;
            return new Equal(to, from, order(), reverseDirection);
        }
    }

    static class Predicate extends ProcedureEdge<ProcedureVertex.Thing, ProcedureVertex.Thing> {

        private final com.vaticle.typedb.core.traversal.predicate.Predicate.Variable predicate;

        private Predicate(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order,
                          Encoding.Direction.Edge direction, com.vaticle.typedb.core.traversal.predicate.Predicate.Variable predicate) {
            super(from, to, order, direction, predicate.toString());
            this.predicate = predicate;
        }

        @Override
        public boolean onlyStartsFromAttribute() {
            return true;
        }

        @Override
        public FunctionalIterator<? extends Vertex<?, ?>> branch(
                GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
            assert fromVertex.isThing() && fromVertex.asThing().isAttribute();
            FunctionalIterator<? extends AttributeVertex<?>> toIter;

            if (to.props().hasIID()) {
                toIter = to.iterateAndFilterFromIID(graphMgr, params)
                        .filter(ThingVertex::isAttribute).map(ThingVertex::asAttribute);
            } else if (!to.props().types().isEmpty()) {
                toIter = to.iterateAndFilterFromTypes(graphMgr, params)
                        .filter(ThingVertex::isAttribute).map(ThingVertex::asAttribute);
            } else {
                assert !to.isStartingVertex();
                toIter = iterate(fromVertex.asThing().asAttribute().valueType().comparables())
                        .flatMap(vt -> graphMgr.schema().attributeTypes(vt))
                        .flatMap(at -> graphMgr.data().getReadable(at)).map(ThingVertex::asAttribute);
                if (!to.props().predicates().isEmpty()) {
                    toIter = to.filterPredicates(toIter, params);
                }
            }

            return toIter.filter(toVertex -> predicate.apply(fromVertex.asThing().asAttribute(), toVertex));
        }

        @Override
        public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                 GraphTraversal.Thing.Parameters params) {
            assert fromVertex.isThing() && fromVertex.asThing().isAttribute() &&
                    toVertex.isThing() && toVertex.asThing().isAttribute();
            return predicate.apply(fromVertex.asThing().asAttribute(), toVertex.asThing().asAttribute());
        }

        @Override
        public ProcedureEdge<?, ?> reverse() {
            throw TypeDBException.of(UNSUPPORTED_OPERATION);
        }
    }

    public static abstract class Native<
            VERTEX_NATIVE_FROM extends ProcedureVertex<?, ?>, VERTEX_NATIVE_TO extends ProcedureVertex<?, ?>
            > extends ProcedureEdge<VERTEX_NATIVE_FROM, VERTEX_NATIVE_TO> {

        private final Encoding.Edge encoding;

        private Native(VERTEX_NATIVE_FROM from, VERTEX_NATIVE_TO to,
                       int order, Encoding.Direction.Edge direction, Encoding.Edge encoding) {
            super(from, to, order, direction, encoding.name());
            this.encoding = encoding;
        }

        static Native<?, ?> of(ProcedureVertex<?, ?> from, ProcedureVertex<?, ?> to,
                               PlannerEdge.Native.Directional<?, ?> edge) {
            boolean isForward = edge.direction().isForward();
            if (edge.isIsa()) {
                int orderNumber = edge.orderNumber();
                boolean isTransitive = edge.asIsa().isTransitive();
                if (isForward) return new Isa.Forward(from.asThing(), to.asType(), orderNumber, isTransitive);
                else return new Isa.Backward(from.asType(), to.asThing(), orderNumber, isTransitive);
            } else if (edge.isType()) {
                return Native.Type.of(from.asType(), to.asType(), edge.asType());
            } else if (edge.isThing()) {
                return Native.Thing.of(from.asThing(), to.asThing(), edge.asThing());
            } else {
                throw TypeDBException.of(UNRECOGNISED_VALUE);
            }
        }

        static abstract class Isa<
                VERTEX_ISA_FROM extends ProcedureVertex<?, ?>, VERTEX_ISA_TO extends ProcedureVertex<?, ?>
                > extends Native<VERTEX_ISA_FROM, VERTEX_ISA_TO> {

            final boolean isTransitive;

            private Isa(VERTEX_ISA_FROM from, VERTEX_ISA_TO to, int order,
                        Encoding.Direction.Edge direction, boolean isTransitive) {
                super(from, to, order, direction, ISA);
                this.isTransitive = isTransitive;
            }

            FunctionalIterator<TypeVertex> isaTypes(ThingVertex thing) {
                if (!isTransitive) return single(thing.type());
                else return loop(thing.type(), Objects::nonNull, v -> v.outs().edge(SUB).to().firstOrNull());
            }

            @Override
            public String toString() {
                return super.toString() + String.format(" { isTransitive: %s }", isTransitive);
            }

            @Override
            public ProcedureEdge<?, ?> reverse() {
                throw TypeDBException.of(UNSUPPORTED_OPERATION);
            }

            static class Forward extends Isa<ProcedureVertex.Thing, ProcedureVertex.Type> {

                Forward(ProcedureVertex.Thing thing, ProcedureVertex.Type type, int order, boolean isTransitive) {
                    super(thing, type, order, FORWARD, isTransitive);
                }

                @Override
                public FunctionalIterator<? extends Vertex<?, ?>> branch(
                        GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                    assert fromVertex.isThing();
                    FunctionalIterator<TypeVertex> iter = isaTypes(fromVertex.asThing());
                    return to.filter(iter);
                }

                @Override
                public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                         GraphTraversal.Thing.Parameters params) {
                    assert fromVertex.isThing() && toVertex.isType();
                    return isaTypes(fromVertex.asThing()).anyMatch(s -> s.equals(toVertex));
                }
            }

            static class Backward extends Isa<ProcedureVertex.Type, ProcedureVertex.Thing> {

                Backward(ProcedureVertex.Type type, ProcedureVertex.Thing thing, int order, boolean isTransitive) {
                    super(type, thing, order, BACKWARD, isTransitive);
                }

                @Override
                public FunctionalIterator<? extends Vertex<?, ?>> branch(
                        GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                    assert fromVertex.isType();
                    TypeVertex type = fromVertex.asType();
                    Set<Label> toTypes = to.props().types();
                    FunctionalIterator<TypeVertex> typeIter;

                    if (!isTransitive) typeIter = single(type);
                    else typeIter = tree(type, v -> v.ins().edge(SUB).from());

                    if (!toTypes.isEmpty()) typeIter = typeIter.filter(t -> toTypes.contains(t.properLabel()));

                    FunctionalIterator<? extends ThingVertex> iter = typeIter.flatMap(t -> graphMgr.data().getReadable(t));
                    if (to.id().isVariable()) iter = to.filterReferableThings(iter);
                    if (to.props().hasIID()) iter = to.filterIID(iter, params);
                    if (!to.props().predicates().isEmpty()) iter = to.filterPredicates(filterAttributes(iter), params);
                    return iter;
                }

                @Override
                public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                         GraphTraversal.Thing.Parameters params) {
                    assert fromVertex.isType() && toVertex.isThing();
                    return isaTypes(toVertex.asThing()).anyMatch(s -> s.equals(fromVertex));
                }
            }
        }

        public static abstract class Type extends Native<ProcedureVertex.Type, ProcedureVertex.Type> {

            private Type(ProcedureVertex.Type from, ProcedureVertex.Type to, int order,
                         Encoding.Direction.Edge direction, Encoding.Edge encoding) {
                super(from, to, order, direction, encoding);
            }

            static Native.Type of(ProcedureVertex.Type from, ProcedureVertex.Type to,
                                  PlannerEdge.Native.Type.Directional edge) {
                boolean isForward = edge.direction().isForward();
                boolean isTransitive = edge.isTransitive();
                int orderNumber = edge.orderNumber();

                if (edge.isSub()) {
                    if (isForward) return new Sub.Forward(from, to, orderNumber, isTransitive);
                    else return new Sub.Backward(from, to, orderNumber, isTransitive);
                } else if (edge.isOwns()) {
                    if (isForward) return new Owns.Forward(from, to, orderNumber, edge.asOwns().isKey());
                    else return new Owns.Backward(from, to, orderNumber, edge.asOwns().isKey());
                } else if (edge.isPlays()) {
                    if (isForward) return new Plays.Forward(from, to, orderNumber);
                    else return new Plays.Backward(from, to, orderNumber);
                } else if (edge.isRelates()) {
                    if (isForward) return new Relates.Forward(from, to, orderNumber);
                    else return new Relates.Backward(from, to, orderNumber);
                } else {
                    throw TypeDBException.of(UNRECOGNISED_VALUE);
                }
            }

            static abstract class Sub extends Type {

                final boolean isTransitive;

                private Sub(ProcedureVertex.Type from, ProcedureVertex.Type to, int order,
                            Encoding.Direction.Edge direction, boolean isTransitive) {
                    super(from, to, order, direction, SUB);
                    this.isTransitive = isTransitive;
                }

                FunctionalIterator<TypeVertex> superTypes(TypeVertex type) {
                    if (!isTransitive) return type.outs().edge(SUB).to();
                    else return loop(type, Objects::nonNull, v -> v.outs().edge(SUB).to().firstOrNull());
                }

                @Override
                public String toString() {
                    return super.toString() + String.format(" { isTransitive: %s }", isTransitive);
                }

                static class Forward extends Sub {

                    Forward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order, boolean isTransitive) {
                        super(from, to, order, FORWARD, isTransitive);
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        FunctionalIterator<TypeVertex> iterator = superTypes(fromVertex.asType());
                        return to.filter(iterator);
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return superTypes(fromVertex.asType()).anyMatch(v -> v.equals(toVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Sub.Backward(to, from, order(), isTransitive);
                    }
                }

                static class Backward extends Sub {

                    Backward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order, boolean isTransitive) {
                        super(from, to, order, BACKWARD, isTransitive);
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isType();
                        FunctionalIterator<TypeVertex> iter;
                        TypeVertex type = fromVertex.asType();
                        if (!isTransitive) iter = type.ins().edge(SUB).from();
                        else iter = tree(type, t -> t.ins().edge(SUB).from());
                        return to.filter(iter);
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return superTypes(toVertex.asType()).anyMatch(v -> v.equals(fromVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Sub.Forward(to, from, order(), isTransitive);
                    }
                }
            }

            static abstract class Owns extends Type {

                final boolean isKey;

                private Owns(ProcedureVertex.Type from, ProcedureVertex.Type to, int order,
                             Encoding.Direction.Edge direction, boolean isKey) {
                    super(from, to, order, direction, OWNS);
                    this.isKey = isKey;
                }

                @Override
                public String toString() {
                    return super.toString() + String.format(" { isKey: %s }", isKey);
                }

                static class Forward extends Owns {

                    Forward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order, boolean isKey) {
                        super(from, to, order, FORWARD, isKey);
                    }

                    private FunctionalIterator<TypeEdge> ownsEdges(TypeVertex owner) {
                        if (isKey) return owner.outs().edge(OWNS_KEY).edge();
                        else return link(owner.outs().edge(OWNS).edge(), owner.outs().edge(OWNS_KEY).edge());
                    }

                    private FunctionalIterator<TypeVertex> ownedAttributeTypes(TypeVertex owner) {
                        Set<TypeVertex> overriddens = new HashSet<>();
                        FunctionalIterator<TypeVertex> supertypes, iterator;

                        supertypes = loop(owner, Objects::nonNull, o -> o.outs().edge(SUB).to().firstOrNull());
                        iterator = supertypes.flatMap(o -> ownsEdges(o).map(e -> {
                            if (e.overridden() != null) overriddens.add(e.overridden());
                            if (!overriddens.contains(e.to())) return e.to();
                            else return null;
                        }).noNulls());
                        return iterator;
                    }

                    @Override
                    public boolean onlyStartsFromThingType() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isType();
                        return to.filter(ownedAttributeTypes(fromVertex.asType()));
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return ownedAttributeTypes(fromVertex.asType()).anyMatch(at -> at.equals(toVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Owns.Backward(to, from, order(), isKey);
                    }
                }

                static class Backward extends Owns {

                    Backward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order, boolean isKey) {
                        super(from, to, order, BACKWARD, isKey);
                    }

                    private FunctionalIterator<TypeVertex> overriddens(TypeVertex owner) {
                        if (isKey) return owner.outs().edge(OWNS_KEY).overridden().noNulls();
                        else return link(owner.outs().edge(OWNS).overridden().noNulls(),
                                owner.outs().edge(OWNS_KEY).overridden().noNulls());
                    }

                    private FunctionalIterator<TypeVertex> declaredOwnersOfAttType(TypeVertex attType) {
                        if (isKey) return attType.ins().edge(OWNS_KEY).from();
                        else return link(attType.ins().edge(OWNS).from(), attType.ins().edge(OWNS_KEY).from());
                    }


                    private FunctionalIterator<TypeVertex> ownersOfAttType(TypeVertex attType) {
                        return declaredOwnersOfAttType(attType).flatMap(owner -> tree(owner, o ->
                                o.ins().edge(SUB).from().filter(s -> overriddens(s).noneMatch(ov -> ov.equals(attType)))
                        ));
                    }

                    @Override
                    public boolean onlyStartsFromAttributeType() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isType();
                        return to.filter(ownersOfAttType(fromVertex.asType()));
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return ownersOfAttType(fromVertex.asType()).anyMatch(o -> o.equals(toVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Owns.Forward(to, from, order(), isKey);
                    }
                }
            }

            static abstract class Plays extends Type {

                private Plays(ProcedureVertex.Type from, ProcedureVertex.Type to, int order,
                              Encoding.Direction.Edge direction) {
                    super(from, to, order, direction, PLAYS);
                }

                static class Forward extends Plays {

                    Forward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order) {
                        super(from, to, order, FORWARD);
                    }

                    private FunctionalIterator<TypeVertex> playedRoleTypes(TypeVertex player) {
                        Set<TypeVertex> overriddens = new HashSet<>();
                        FunctionalIterator<TypeVertex> supertypes, iterator;

                        supertypes = loop(player, Objects::nonNull, p -> p.outs().edge(SUB).to().firstOrNull());
                        iterator = supertypes.flatMap(s -> s.outs().edge(PLAYS).edge().map(e -> {
                            if (e.overridden() != null) overriddens.add(e.overridden());
                            if (!overriddens.contains(e.to())) return e.to();
                            else return null;
                        }).noNulls());
                        return iterator;
                    }

                    @Override
                    public boolean onlyStartsFromThingType() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isType();
                        return to.filter(playedRoleTypes(fromVertex.asType()));
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return playedRoleTypes(fromVertex.asType()).anyMatch(rt -> rt.equals(toVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Plays.Backward(to, from, order());
                    }
                }

                static class Backward extends Plays {

                    Backward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order) {
                        super(from, to, order, BACKWARD);
                    }

                    private FunctionalIterator<TypeVertex> playersOfRoleType(TypeVertex roleType) {
                        return roleType.ins().edge(PLAYS).from().flatMap(player -> tree(player, p ->
                                p.ins().edge(SUB).from().filter(s -> s.outs().edge(PLAYS).overridden()
                                        .noNulls().noneMatch(ov -> ov.equals(roleType)))));
                    }

                    @Override
                    public boolean onlyStartsFromRoleType() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isType();
                        return to.filter(playersOfRoleType(fromVertex.asType()));
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return playersOfRoleType(fromVertex.asType()).anyMatch(p -> p.equals(toVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Plays.Forward(to, from, order());
                    }
                }
            }

            static abstract class Relates extends Type {

                private Relates(ProcedureVertex.Type from, ProcedureVertex.Type to, int order,
                                Encoding.Direction.Edge direction) {
                    super(from, to, order, direction, RELATES);
                }

                static class Forward extends Relates {

                    Forward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order) {
                        super(from, to, order, FORWARD);
                    }

                    private FunctionalIterator<TypeVertex> relatedRoleTypes(TypeVertex relation) {
                        Set<TypeVertex> overriddens = new HashSet<>();
                        FunctionalIterator<TypeVertex> supertypes, iterator;

                        supertypes = loop(relation, Objects::nonNull, r -> r.outs().edge(SUB).to().firstOrNull());
                        iterator = supertypes.flatMap(s -> s.outs().edge(RELATES).edge().map(e -> {
                            if (e.overridden() != null) overriddens.add(e.overridden());
                            if (!overriddens.contains(e.to())) return e.to();
                            else return null;
                        }).noNulls());
                        return iterator;
                    }

                    @Override
                    public boolean onlyStartsFromRelationType() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isType();
                        return to.filter(relatedRoleTypes(fromVertex.asType()));
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return relatedRoleTypes(fromVertex.asType()).anyMatch(rt -> rt.equals(toVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Relates.Backward(to, from, order());
                    }
                }

                static class Backward extends Relates {

                    Backward(ProcedureVertex.Type from, ProcedureVertex.Type to, int order) {
                        super(from, to, order, BACKWARD);
                    }

                    private FunctionalIterator<TypeVertex> relationsOfRoleType(TypeVertex roleType) {
                        return roleType.ins().edge(RELATES).from().flatMap(relation -> tree(relation, r ->
                                r.ins().edge(SUB).from().filter(s -> s.outs().edge(RELATES).overridden()
                                        .noNulls().noneMatch(ov -> ov.equals(roleType)))));
                    }

                    @Override
                    public boolean onlyStartsFromRoleType() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<TypeVertex> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isType();
                        return to.filter(relationsOfRoleType(fromVertex.asType()));
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return relationsOfRoleType(fromVertex.asType()).anyMatch(rel -> rel.equals(toVertex.asType()));
                    }

                    @Override
                    public ProcedureEdge<?, ?> reverse() {
                        return new Relates.Forward(to, from, order());
                    }
                }
            }
        }

        static abstract class Thing extends Native<ProcedureVertex.Thing, ProcedureVertex.Thing> {

            private Thing(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order,
                          Encoding.Direction.Edge direction, Encoding.Edge encoding) {
                super(from, to, order, direction, encoding);
            }

            static Thing of(ProcedureVertex.Thing from, ProcedureVertex.Thing to,
                            PlannerEdge.Native.Thing.Directional edge) {
                boolean isForward = edge.direction().isForward();
                int orderNumber = edge.orderNumber();

                if (edge.isHas()) {
                    if (isForward) return new Has.Forward(from, to, orderNumber);
                    else return new Has.Backward(from, to, orderNumber);
                } else if (edge.isPlaying()) {
                    if (isForward) return new Playing.Forward(from, to, orderNumber);
                    else return new Playing.Backward(from, to, orderNumber);
                } else if (edge.isRelating()) {
                    if (isForward) return new Relating.Forward(from, to, orderNumber);
                    else return new Relating.Backward(from, to, orderNumber);
                } else if (edge.isRolePlayer()) {
                    PlannerEdge.Native.Thing.RolePlayer.Directional rp = edge.asRolePlayer();
                    if (isForward) return new RolePlayer.Forward(from, to, orderNumber, rp.roleTypes());
                    else return new RolePlayer.Backward(from, to, orderNumber, rp.roleTypes());
                } else {
                    throw TypeDBException.of(UNRECOGNISED_VALUE);
                }
            }

            @Override
            public ProcedureEdge<?, ?> reverse() {
                throw TypeDBException.of(UNSUPPORTED_OPERATION);
            }

            FunctionalIterator<? extends ThingVertex> backwardBranchToIIDFiltered(
                    GraphManager graphMgr, ThingVertex fromVertex,
                    Encoding.Edge.Thing encoding, VertexIID.Thing toIID, Set<Label> allowedToTypes) {
                ThingVertex toVertex = graphMgr.data().getReadable(toIID);
                if (toVertex != null && fromVertex.ins().edge(encoding, toVertex) != null &&
                        (allowedToTypes.isEmpty() || allowedToTypes.contains(toVertex.type().properLabel()))) {
                    return single(toVertex);
                } else {
                    return empty();
                }
            }

            FunctionalIterator<? extends Vertex<?, ?>> forwardBranchToRole(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                                                           Encoding.Edge.Thing.Base encoding) {
                assert !to.props().hasIID() && to.props().predicates().isEmpty();
                ThingVertex relation = fromVertex.asThing();
                if (!to.props().types().isEmpty()) {
                    return iterate(to.props().types()).map(l -> graphMgr.schema().getType(l)).noNulls()
                            .flatMap(t -> relation.outs().edge(encoding, PrefixIID.of(VERTEX_ROLE), t.iid()).to());
                } else {
                    return relation.outs().edge(encoding).to();
                }
            }

            static abstract class Has extends Thing {

                private Has(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order,
                            Encoding.Direction.Edge direction) {
                    super(from, to, order, direction, HAS);
                }

                static class Forward extends Has {

                    Forward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order) {
                        super(from, to, order, FORWARD);
                    }

                    @Override
                    public FunctionalIterator<? extends Vertex<?, ?>> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing();
                        com.vaticle.typedb.core.traversal.predicate.Predicate.Value<?> eq = null;
                        FunctionalIterator<? extends AttributeVertex<?>> iter;
                        ThingVertex owner = fromVertex.asThing();
                        if (to.props().hasIID()) {
                            assert to.id().isVariable();
                            VertexIID.Thing iid = params.getIID(to.id().asVariable());
                            AttributeVertex<?> att;
                            if (!iid.isAttribute()) att = null;
                            else att = graphMgr.data().getReadable(iid.asAttribute());
                            if (att != null && owner.outs().edge(HAS, att) != null &&
                                    (to.props().types().isEmpty() || to.props().types().contains(att.type().properLabel()))) {
                                iter = single(att);
                            } else {
                                return empty();
                            }
                        } else if (!to.props().types().isEmpty()) {
                            eq = iterate(to.props().predicates()).filter(p -> p.operator().equals(EQ)).firstOrNull();
                            if (eq != null) {
                                iter = to.iteratorOfAttributesWithTypes(graphMgr, params, eq)
                                        .filter(a -> owner.outs().edge(HAS, a) != null);
                            } else {
                                iter = iterate(to.props().types()).map(l -> graphMgr.schema().getType(l)).noNulls()
                                        .flatMap(t -> owner.outs().edge(HAS, PrefixIID.of(VERTEX_ATTRIBUTE), t.iid()).to())
                                        .map(ThingVertex::asAttribute);
                            }
                        } else {
                            iter = owner.outs().edge(HAS).to().map(ThingVertex::asAttribute);
                        }

                        if (to.props().predicates().isEmpty()) return iter;
                        else return to.filterPredicates(iter, params, eq);
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return fromVertex.asThing().outs().edge(HAS, toVertex.asThing()) != null;
                    }
                }

                static class Backward extends Has {

                    Backward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order) {
                        super(from, to, order, BACKWARD);
                    }

                    @Override
                    public boolean onlyStartsFromAttribute() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<? extends Vertex<?, ?>> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing() && fromVertex.asThing().isAttribute();
                        FunctionalIterator<? extends ThingVertex> iter;
                        AttributeVertex<?> att = fromVertex.asThing().asAttribute();

                        if (to.props().hasIID()) {
                            iter = backwardBranchToIIDFiltered(graphMgr, att, HAS, params.getIID(to.id().asVariable()), to.props().types());
                        } else if (!to.props().types().isEmpty()) {
                            com.vaticle.typedb.core.traversal.predicate.Predicate.Value<?> eq = iterate(to.props().predicates()).filter(p -> p.operator().equals(EQ)).firstOrNull();
                            if (eq != null) {
                                iter = to.iteratorOfAttributesWithTypes(graphMgr, params, eq).filter(a -> att.ins().edge(HAS, a) != null);
                            } else {
                                iter = iterate(to.props().types()).map(l -> graphMgr.schema().getType(l)).noNulls()
                                        .flatMap(t -> att.ins().edge(HAS, PrefixIID.of(t.encoding().instance()), t.iid()).from());
                            }
                        } else {
                            iter = att.ins().edge(HAS).from();
                        }
                        if (to.props().predicates().isEmpty()) return iter;
                        else return to.filterPredicates(filterAttributes(iter), params);
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                             Vertex<?, ?> toVertex, GraphTraversal.Thing.Parameters params) {
                        return fromVertex.asThing().ins().edge(HAS, toVertex.asThing()) != null;
                    }
                }
            }

            static abstract class Playing extends Thing {

                private Playing(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order,
                                Encoding.Direction.Edge direction) {
                    super(from, to, order, direction, PLAYING);
                }

                static class Forward extends Playing {

                    Forward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order) {
                        super(from, to, order, FORWARD);
                    }

                    @Override
                    public FunctionalIterator<? extends Vertex<?, ?>> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing();
                        return forwardBranchToRole(graphMgr, fromVertex, PLAYING);
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return fromVertex.asThing().outs().edge(PLAYING, toVertex.asThing()) != null;
                    }
                }

                static class Backward extends Playing {

                    Backward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order) {
                        super(from, to, order, BACKWARD);
                    }

                    @Override
                    public FunctionalIterator<? extends Vertex<?, ?>> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing();
                        ThingVertex role = fromVertex.asThing();
                        Set<Label> toTypes = to.props().types();
                        FunctionalIterator<? extends ThingVertex> iter;

                        if (to.props().hasIID()) {
                            assert to.id().isVariable();
                            iter = backwardBranchToIIDFiltered(graphMgr, role, PLAYING, params.getIID(to.id().asVariable()), toTypes);
                        } else if (!toTypes.isEmpty()) {
                            iter = iterate(toTypes).map(l -> graphMgr.schema().getType(l)).noNulls()
                                    .flatMap(t -> role.ins().edge(PLAYING, PrefixIID.of(t.encoding().instance()), t.iid()).from());
                        } else {
                            iter = role.ins().edge(PLAYING).from();
                        }

                        if (to.props().predicates().isEmpty()) return iter;
                        else return to.filterPredicates(filterAttributes(iter), params);
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return fromVertex.asThing().ins().edge(PLAYING, toVertex.asThing()) != null;
                    }
                }
            }

            static abstract class Relating extends Thing {

                private Relating(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order,
                                 Encoding.Direction.Edge direction) {
                    super(from, to, order, direction, RELATING);
                }

                static class Forward extends Relating {

                    Forward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order) {
                        super(from, to, order, FORWARD);
                    }

                    @Override
                    public boolean onlyStartsFromRelation() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<? extends Vertex<?, ?>> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing();
                        return forwardBranchToRole(graphMgr, fromVertex, RELATING);
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return fromVertex.asThing().outs().edge(RELATING, toVertex.asThing()) != null;
                    }
                }

                static class Backward extends Relating {

                    Backward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order) {
                        super(from, to, order, BACKWARD);
                    }

                    @Override
                    public FunctionalIterator<? extends Vertex<?, ?>> branch(
                            GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing() && to.props().predicates().isEmpty();
                        ThingVertex role = fromVertex.asThing();
                        Set<Label> toTypes = to.props().types();
                        FunctionalIterator<? extends ThingVertex> iter;

                        if (to.props().hasIID()) {
                            assert to.id().isVariable();
                            iter = backwardBranchToIIDFiltered(graphMgr, role, RELATING, params.getIID(to.id().asVariable()), toTypes);
                        } else if (!toTypes.isEmpty()) {
                            iter = iterate(toTypes).map(l -> graphMgr.schema().getType(l)).noNulls()
                                    .flatMap(t -> role.ins().edge(RELATING, PrefixIID.of(RELATION), t.iid()).from());
                        } else {
                            iter = role.ins().edge(RELATING).from();
                        }
                        return iter;
                    }

                    @Override
                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params) {
                        return fromVertex.asThing().ins().edge(RELATING, toVertex.asThing()) != null;
                    }

                    @Override
                    public boolean onlyEndsAtRelation() {
                        return true;
                    }
                }
            }

            public static abstract class RolePlayer extends Thing {

                final Set<Label> roleTypes;
                Set<TypeVertex> resolvedRoleTypes;

                private RolePlayer(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order,
                                   Encoding.Direction.Edge direction, Set<Label> roleTypes) {
                    super(from, to, order, direction, ROLEPLAYER);
                    this.roleTypes = roleTypes;
                }

                Set<TypeVertex> resolvedRoleTypes(TypeGraph graph) {
                    // TODO: a duplicate of this code exists in PlannerEdge.Native.Thing.RolePlayer,
                    //       which is another indicator that we should:
                    // TODO: Merge PlannerVertex, PlannerEdge, ProcedureVertex, and ProcedureEdge into some
                    //       Vertex and Edge data structure (in `//traversal/fragment`) that aggregate their
                    //       'planner' and 'procedure' logic for each class following the variable //pattern data structure.
                    if (resolvedRoleTypes == null) {
                        resolvedRoleTypes = iterate(roleTypes).map(graph::getType)
                                .flatMap(rt -> tree(rt, r -> r.ins().edge(SUB).from())).toSet();
                    }
                    return resolvedRoleTypes;
                }

                public abstract FunctionalIterator<ThingEdge> branchEdge(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                                                         GraphTraversal.Thing.Parameters params);

                public abstract boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                                  Vertex<?, ?> toVertex, GraphTraversal.Thing.Parameters params,
                                                  GraphIterator.Scopes.Scoped withinScope);

                @Override
                public FunctionalIterator<? extends Vertex<?, ?>> branch(
                        GraphManager graphMgr, Vertex<?, ?> fromVertex, GraphTraversal.Thing.Parameters params) {
                    throw TypeDBException.of(ILLEGAL_OPERATION);
                }

                @Override
                public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                         Vertex<?, ?> toVertex, GraphTraversal.Thing.Parameters params) {
                    throw TypeDBException.of(ILLEGAL_OPERATION);
                }

                @Override
                public boolean isRolePlayer() {
                    return true;
                }

                @Override
                public RolePlayer asRolePlayer() {
                    return this;
                }

                public Identifier.Variable scope() {
                    if (direction().isForward()) return from.id().asVariable();
                    else return to.id().asVariable();
                }

                @Override
                public String toString() {
                    return super.toString() + String.format(" { roleTypes: %s }", roleTypes);
                }

                static class Forward extends RolePlayer {

                    Forward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order, Set<Label> roleTypes) {
                        super(from, to, order, FORWARD, roleTypes);
                    }

                    @Override
                    public boolean onlyStartsFromRelation() {
                        return true;
                    }

                    @Override
                    public FunctionalIterator<ThingEdge> branchEdge(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                                                    GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing();
                        ThingVertex rel = fromVertex.asThing();
                        FunctionalIterator<ThingEdge> iter;
                        boolean filteredIID = false, filteredTypes = false;

                        if (!roleTypes.isEmpty()) {
                            FunctionalIterator<TypeVertex> resolveRoleTypesIter = iterate(resolvedRoleTypes(graphMgr.schema()));
                            if (to.props().hasIID()) {
                                assert to.id().isVariable();
                                filteredIID = true;
                                ThingVertex player = graphMgr.data().getReadable(params.getIID(to.id().asVariable()));
                                if (player == null) return empty();
                                // TODO: the following code can be optimised if we have an API to directly get the
                                //       roleplayer edge when we have the roleplayer vertex
                                iter = resolveRoleTypesIter.flatMap(
                                        rt -> rel.outs()
                                                .edge(ROLEPLAYER, rt, player.iid().prefix(), player.iid().type()).get()
                                                .map(ThingAdjacency.DirectedEdge::get)
                                ).filter(e -> e.to().equals(player));
                            } else if (!to.props().types().isEmpty()) {
                                filteredTypes = true;
                                iter = resolveRoleTypesIter.flatMap(
                                        rt -> iterate(to.props().types()).map(l -> graphMgr.schema().getType(l)).noNulls()
                                                .flatMap(t -> rel.outs()
                                                        .edge(ROLEPLAYER, rt, PrefixIID.of(t.encoding().instance()), t.iid()).get()
                                                        .map(ThingAdjacency.DirectedEdge::get))
                                );
                            } else {
                                iter = resolveRoleTypesIter.flatMap(rt -> rel.outs()
                                        .edge(ROLEPLAYER, rt).get()
                                        .map(ThingAdjacency.DirectedEdge::get));
                            }
                        } else {
                            iter = rel.outs().edge(ROLEPLAYER).get();
                        }

                        if (!filteredIID && to.props().hasIID()) iter = to.filterIIDOnEdge(iter, params, true);
                        if (!filteredTypes && !to.props().types().isEmpty()) iter = to.filterTypesOnEdge(iter, true);
                        if (!to.props().predicates().isEmpty()) iter = to.filterPredicatesOnEdge(iter, params, true);
                        return iter;
                    }

                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params, GraphIterator.Scopes.Scoped scoped) {
                        ThingVertex rel = fromVertex.asThing();
                        ThingVertex player = toVertex.asThing();
                        Optional<ThingEdge> validEdge;
                        if (!roleTypes.isEmpty()) {
                            validEdge = iterate(resolvedRoleTypes(graphMgr.schema())).flatMap(
                                    rt -> rel.outs()
                                            .edge(ROLEPLAYER, rt, player.iid().prefix(), player.iid().type()).get()
                                            .map(ThingAdjacency.DirectedEdge::get)
                                            .filter(e -> e.to().equals(player) && !scoped.contains(e.optimised().get())))
                                    .first();
                        } else {
                            validEdge = rel.outs().edge(ROLEPLAYER).get().filter(
                                    e -> e.to().equals(player) && !scoped.contains(e.optimised().get())
                            ).first();
                        }
                        validEdge.ifPresent(e -> scoped.push(e.optimised().get(), order()));
                        return validEdge.isPresent();
                    }
                }

                static class Backward extends RolePlayer {

                    Backward(ProcedureVertex.Thing from, ProcedureVertex.Thing to, int order, Set<Label> roleTypes) {
                        super(from, to, order, BACKWARD, roleTypes);
                    }

                    @Override
                    public FunctionalIterator<ThingEdge> branchEdge(GraphManager graphMgr, Vertex<?, ?> fromVertex,
                                                                    GraphTraversal.Thing.Parameters params) {
                        assert fromVertex.isThing() && to.props().predicates().isEmpty();
                        ThingVertex player = fromVertex.asThing();
                        FunctionalIterator<ThingEdge> iter;
                        boolean filteredIID = false, filteredTypes = false;

                        if (!roleTypes.isEmpty()) {
                            FunctionalIterator<TypeVertex> resolveRoleTypesIter = iterate(resolvedRoleTypes(graphMgr.schema()));
                            if (to.props().hasIID()) {
                                assert to.id().isVariable();
                                filteredIID = true;
                                ThingVertex relation = graphMgr.data().getReadable(params.getIID(to.id().asVariable()));
                                if (relation == null) return empty();
                                iter = resolveRoleTypesIter.flatMap(
                                        rt -> player.ins()
                                                .edge(ROLEPLAYER, rt, relation.iid().prefix(), relation.iid().type()).get()
                                                .map(ThingAdjacency.DirectedEdge::get)
                                                .filter(r -> r.from().equals(relation)));
                            } else if (!to.props().types().isEmpty()) {
                                filteredTypes = true;
                                iter = resolveRoleTypesIter.flatMap(
                                        rt -> iterate(to.props().types()).map(l -> graphMgr.schema().getType(l)).noNulls()
                                                .flatMap(t -> player.ins()
                                                        .edge(ROLEPLAYER, rt, PrefixIID.of(t.encoding().instance()), t.iid()).get()
                                                        .map(ThingAdjacency.DirectedEdge::get)));
                            } else {
                                iter = resolveRoleTypesIter.flatMap(rt -> player.ins().edge(ROLEPLAYER, rt).get().map(ThingAdjacency.DirectedEdge::get));
                            }
                        } else {
                            iter = player.ins().edge(ROLEPLAYER).get();
                        }

                        if (!filteredIID && to.props().hasIID()) iter = to.filterIIDOnEdge(iter, params, false);
                        if (!filteredTypes && !to.props().types().isEmpty()) iter = to.filterTypesOnEdge(iter, false);
                        return iter;
                    }

                    public boolean isClosure(GraphManager graphMgr, Vertex<?, ?> fromVertex, Vertex<?, ?> toVertex,
                                             GraphTraversal.Thing.Parameters params, GraphIterator.Scopes.Scoped scoped) {
                        ThingVertex player = fromVertex.asThing();
                        ThingVertex rel = toVertex.asThing();
                        Optional<ThingEdge> validEdge;
                        if (!roleTypes.isEmpty()) {
                            validEdge = iterate(resolvedRoleTypes(graphMgr.schema())).flatMap(
                                    rt -> player.ins().edge(ROLEPLAYER, rt, rel.iid().prefix(), rel.iid().type()).get()
                                            .map(ThingAdjacency.DirectedEdge::get)
                                            .filter(e -> e.from().equals(rel) && !scoped.contains(e.optimised().get())))
                                    .first();
                        } else {
                            validEdge = player.ins().edge(ROLEPLAYER).get().filter(
                                    e -> e.from().equals(rel) && !scoped.contains(e.optimised().get())
                            ).first();
                        }
                        validEdge.ifPresent(e -> scoped.push(e.optimised().get(), order()));
                        return validEdge.isPresent();
                    }

                    @Override
                    public boolean onlyEndsAtRelation() {
                        return true;
                    }
                }
            }
        }
    }
}
