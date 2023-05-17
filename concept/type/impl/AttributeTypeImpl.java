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

package com.vaticle.typedb.core.concept.type.impl;

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.sorted.SortedIterator.Forwardable;
import com.vaticle.typedb.core.common.parameters.Order;
import com.vaticle.typedb.core.concept.ConceptManager;
import com.vaticle.typedb.core.concept.thing.Attribute;
import com.vaticle.typedb.core.concept.thing.impl.AttributeImpl;
import com.vaticle.typedb.core.concept.type.AttributeType;
import com.vaticle.typedb.core.concept.type.RoleType;
import com.vaticle.typedb.core.encoding.Encoding;
import com.vaticle.typedb.core.graph.GraphManager;
import com.vaticle.typedb.core.graph.vertex.AttributeVertex;
import com.vaticle.typedb.core.graph.vertex.TypeVertex;
import com.vaticle.typeql.lang.common.TypeQLToken;

import java.time.LocalDateTime;
import java.util.Objects;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.vaticle.typedb.common.util.Objects.className;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.UNRECOGNISED_VALUE;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.ThingWrite.ATTRIBUTE_VALUE_UNSATISFIES_REGEX;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeRead.INVALID_TYPE_CASTING;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeRead.TYPE_ROOT_MISMATCH;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeRead.VALUE_TYPE_MISMATCH;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeWrite.ATTRIBUTE_NEW_SUPERTYPE_NOT_ABSTRACT;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeWrite.ATTRIBUTE_REGEX_UNSATISFIES_INSTANCES;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeWrite.ATTRIBUTE_SUPERTYPE_VALUE_TYPE;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeWrite.ATTRIBUTE_UNSET_ABSTRACT_HAS_SUBTYPES;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.TypeWrite.ROOT_TYPE_MUTATION;
import static com.vaticle.typedb.core.common.iterator.sorted.SortedIterators.Forwardable.emptySorted;
import static com.vaticle.typedb.core.common.iterator.sorted.SortedIterators.Forwardable.iterateSorted;
import static com.vaticle.typedb.core.common.iterator.sorted.SortedIterators.Forwardable.merge;
import static com.vaticle.typedb.core.common.parameters.Order.Asc.ASC;
import static com.vaticle.typedb.core.encoding.Encoding.Edge.Type.OWNS;
import static com.vaticle.typedb.core.encoding.Encoding.Edge.Type.OWNS_KEY;
import static com.vaticle.typedb.core.encoding.Encoding.Edge.Type.SUB;
import static com.vaticle.typedb.core.encoding.Encoding.ValueType.BOOLEAN;
import static com.vaticle.typedb.core.encoding.Encoding.ValueType.DATETIME;
import static com.vaticle.typedb.core.encoding.Encoding.ValueType.DOUBLE;
import static com.vaticle.typedb.core.encoding.Encoding.ValueType.LONG;
import static com.vaticle.typedb.core.encoding.Encoding.ValueType.OBJECT;
import static com.vaticle.typedb.core.encoding.Encoding.ValueType.STRING;
import static com.vaticle.typedb.core.encoding.Encoding.Vertex.Type.ATTRIBUTE_TYPE;
import static com.vaticle.typedb.core.encoding.Encoding.Vertex.Type.Root.ATTRIBUTE;
import static com.vaticle.typeql.lang.common.TypeQLToken.Char.COMMA;
import static com.vaticle.typeql.lang.common.TypeQLToken.Char.NEW_LINE;
import static com.vaticle.typeql.lang.common.TypeQLToken.Char.SEMICOLON;
import static com.vaticle.typeql.lang.common.TypeQLToken.Char.SPACE;
import static com.vaticle.typeql.lang.common.util.Strings.escapeRegex;
import static com.vaticle.typeql.lang.common.util.Strings.quoteString;

public abstract class AttributeTypeImpl extends ThingTypeImpl implements AttributeType {

    private AttributeTypeImpl(ConceptManager conceptMgr, TypeVertex vertex) {
        super(conceptMgr, vertex);
        if (vertex.encoding() != ATTRIBUTE_TYPE) {
            throw exception(TypeDBException.of(TYPE_ROOT_MISMATCH, vertex.label(),
                    ATTRIBUTE_TYPE.root().label(),
                    vertex.encoding().root().label()));
        }
    }

    private AttributeTypeImpl(ConceptManager conceptMgr, java.lang.String label, Class<?> valueType) {
        super(conceptMgr, label, ATTRIBUTE_TYPE);
        vertex.valueType(Encoding.ValueType.of(valueType));
    }

    public static AttributeTypeImpl of(ConceptManager conceptMgr, TypeVertex vertex) {
        Encoding.ValueType<?> valueType = vertex.valueType();
        if (valueType == OBJECT) return new Root(conceptMgr, vertex);
        else if (valueType == BOOLEAN) return Boolean.of(conceptMgr, vertex);
        else if (valueType == LONG) return Long.of(conceptMgr, vertex);
        else if (valueType == DOUBLE) return Double.of(conceptMgr, vertex);
        else if (valueType == STRING) return String.of(conceptMgr, vertex);
        else if (valueType == DATETIME) return DateTime.of(conceptMgr, vertex);
        throw conceptMgr.exception(TypeDBException.of(UNRECOGNISED_VALUE));
    }

    @Override
    public void unsetAbstract() {
        if (getSubtypes().anyMatch(sub -> !sub.equals(this))) {
            throw exception(TypeDBException.of(ATTRIBUTE_UNSET_ABSTRACT_HAS_SUBTYPES, getLabel()));
        }
        vertex.isAbstract(false);
    }

    @Override
    public abstract Forwardable<? extends AttributeTypeImpl, Order.Asc> getSubtypes();

    @Override
    public abstract Forwardable<? extends AttributeTypeImpl, Order.Asc> getSubtypesExplicit();

    @Override
    public abstract Forwardable<? extends AttributeImpl<?>, Order.Asc> getInstances();

    Forwardable<TypeVertex, Order.Asc> getSubtypeVertices(Encoding.ValueType<?> valueType) {
        return iterateSorted(graphMgr().schema().getSubtypes(vertex), ASC)
                .filter(sv -> sv.valueType().equals(valueType));
    }

    Forwardable<TypeVertex, Order.Asc> getSubtypeVerticesDirect(Encoding.ValueType<?> valueType) {
        return vertex.ins().edge(SUB).from().filter(sv -> sv.valueType().equals(valueType));
    }

    @Override
    public void setSupertype(AttributeType superType) {
        validateIsNotDeleted();
        if (!superType.isRoot() && !Objects.equals(this.getValueType(), superType.getValueType())) {
            throw exception(TypeDBException.of(ATTRIBUTE_SUPERTYPE_VALUE_TYPE, getLabel(), getValueType().name(),
                    superType.getLabel(), superType.getValueType().name()));
        } else if (!superType.isAbstract()) {
            throw exception(TypeDBException.of(ATTRIBUTE_NEW_SUPERTYPE_NOT_ABSTRACT, superType.getLabel()));
        }
        setSuperTypeVertex(((AttributeTypeImpl) superType).vertex);
    }

    @Override
    public abstract ValueType getValueType();

    @Override
    public Forwardable<? extends ThingTypeImpl, Order.Asc> getOwners(Set<TypeQLToken.Annotation> annotations) {
        if (isRoot()) return emptySorted();
        else {
            return iterateSorted(graphMgr().schema().ownersOfAttributeType(vertex), ASC)
                    .mapSorted(v -> ThingTypeImpl.of(conceptMgr, v), thingType -> thingType.vertex, ASC)
                    .filter(thingType -> thingType.getOwns(this)
                            .map(owns -> owns.effectiveAnnotations().containsAll(annotations))
                            .orElse(false)
                    );
        }
    }

    @Override
    public Forwardable<? extends ThingTypeImpl, Order.Asc> getOwnersExplicit(Set<TypeQLToken.Annotation> annotations) {
        if (isRoot()) return emptySorted();
        Forwardable<TypeVertex, Order.Asc> iterator = vertex.ins().edge(OWNS_KEY).from().merge(vertex.ins().edge(OWNS).from());
        return iterator.mapSorted(v -> ThingTypeImpl.of(conceptMgr, v), thingType -> thingType.vertex, ASC)
                .filter(thingType -> thingType.getOwnsExplicit(this)
                        .map(owns -> owns.effectiveAnnotations().containsAll(annotations))
                        .orElse(false)
                );
    }

    @Override
    public boolean isAttributeType() {
        return true;
    }

    @Override
    public AttributeTypeImpl asAttributeType() {
        return this;
    }

    @Override
    public boolean isBoolean() {
        return false;
    }

    @Override
    public boolean isLong() {
        return false;
    }

    @Override
    public boolean isDouble() {
        return false;
    }

    @Override
    public boolean isString() {
        return false;
    }

    @Override
    public boolean isDateTime() {
        return false;
    }

    @Override
    public AttributeTypeImpl.Boolean asBoolean() {
        throw exception(TypeDBException.of(INVALID_TYPE_CASTING, className(this.getClass()),
                className(AttributeType.Boolean.class)));
    }

    @Override
    public AttributeTypeImpl.Long asLong() {
        throw exception(TypeDBException.of(INVALID_TYPE_CASTING, className(this.getClass()),
                className(AttributeType.Long.class)));
    }

    @Override
    public AttributeTypeImpl.Double asDouble() {
        throw exception(TypeDBException.of(INVALID_TYPE_CASTING, className(this.getClass()),
                className(AttributeType.Double.class)));
    }

    @Override
    public AttributeTypeImpl.String asString() {
        throw exception(TypeDBException.of(INVALID_TYPE_CASTING, className(this.getClass()),
                className(AttributeType.String.class)));
    }

    @Override
    public AttributeTypeImpl.DateTime asDateTime() {
        throw exception(TypeDBException.of(INVALID_TYPE_CASTING, className(this.getClass()),
                className(AttributeType.DateTime.class)));
    }

    @Override
    public void getSyntax(StringBuilder builder) {
        writeSupertype(builder);
        writeAbstract(builder);
        if (!isRoot()) {
            builder.append(COMMA).append(SPACE)
                    .append(TypeQLToken.Constraint.VALUE_TYPE).append(SPACE)
                    .append(getValueType().syntax());
            if (isString()) {
                java.util.regex.Pattern regex = asString().getRegex();
                if (regex != null) builder.append(COMMA).append(SPACE)
                        .append(TypeQLToken.Constraint.REGEX).append(SPACE)
                        .append(quoteString(escapeRegex(regex.pattern())));
            }
        }
        writeOwns(builder);
        writePlays(builder);
        builder.append(SEMICOLON).append(NEW_LINE);
    }

    @Override
    public boolean equals(java.lang.Object object) {
        if (this == object) return true;
        if (!(object instanceof AttributeTypeImpl)) return false;
        // We do the above, as opposed to checking if (object == null || getClass() != object.getClass())
        // because it is possible to compare a attribute root types wrapped in different type classes
        // such as: root type wrapped in AttributeTypeImpl.Root and as in AttributeType.Boolean.Root

        AttributeTypeImpl that = (AttributeTypeImpl) object;
        return vertex.equals(that.vertex);
    }

    private static class Root extends AttributeTypeImpl {

        private Root(ConceptManager conceptMgr, TypeVertex vertex) {
            super(conceptMgr, vertex);
            assert vertex.valueType().equals(OBJECT);
            assert vertex.label().equals(ATTRIBUTE.label());
        }

        public ValueType getValueType() {
            return ValueType.OBJECT;
        }

        @Override
        public AttributeTypeImpl.Boolean asBoolean() {
            return AttributeTypeImpl.Boolean.of(conceptMgr, vertex);
        }

        @Override
        public AttributeTypeImpl.Long asLong() {
            return AttributeTypeImpl.Long.of(conceptMgr, vertex);
        }

        @Override
        public AttributeTypeImpl.Double asDouble() {
            return AttributeTypeImpl.Double.of(conceptMgr, vertex);
        }

        @Override
        public AttributeTypeImpl.String asString() {
            return AttributeTypeImpl.String.of(conceptMgr, vertex);
        }

        @Override
        public AttributeTypeImpl.DateTime asDateTime() {
            return AttributeTypeImpl.DateTime.of(conceptMgr, vertex);
        }

        @Override
        public boolean isRoot() {
            return true;
        }

        @Override
        public void delete() {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public void setLabel(java.lang.String label) {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public void unsetAbstract() {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public void setSupertype(AttributeType superType) {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public Forwardable<ThingTypeImpl, Order.Asc> getSupertypes() {
            return iterateSorted(ASC, this);
        }

        @Override
        public Forwardable<AttributeTypeImpl, Order.Asc> getSubtypes() {
            return iterateSorted(graphMgr().schema().getSubtypes(vertex), ASC).mapSorted(v -> {
                Encoding.ValueType<?> valueType = v.valueType();
                if (valueType == OBJECT) {
                    assert vertex == v;
                    return this;
                } else if (valueType == BOOLEAN) return AttributeTypeImpl.Boolean.of(conceptMgr, v);
                else if (valueType == LONG) return AttributeTypeImpl.Long.of(conceptMgr, v);
                else if (valueType == DOUBLE) return AttributeTypeImpl.Double.of(conceptMgr, v);
                else if (valueType == STRING) return AttributeTypeImpl.String.of(conceptMgr, v);
                else if (valueType == DATETIME) return AttributeTypeImpl.DateTime.of(conceptMgr, v);
                throw exception(TypeDBException.of(UNRECOGNISED_VALUE));
            }, attrType -> attrType.vertex, ASC);
        }

        @Override
        public Forwardable<AttributeTypeImpl, Order.Asc> getSubtypesExplicit() {
            return getSubtypesExplicit(v -> {
                Encoding.ValueType<?> valueType = v.valueType();
                if (valueType == BOOLEAN) return AttributeTypeImpl.Boolean.of(conceptMgr, v);
                else if (valueType == LONG) return AttributeTypeImpl.Long.of(conceptMgr, v);
                else if (valueType == DOUBLE) return AttributeTypeImpl.Double.of(conceptMgr, v);
                else if (valueType == STRING) return AttributeTypeImpl.String.of(conceptMgr, v);
                else if (valueType == DATETIME) return AttributeTypeImpl.DateTime.of(conceptMgr, v);
                throw exception(TypeDBException.of(UNRECOGNISED_VALUE));
            });
        }

        @Override
        public Forwardable<AttributeImpl<?>, Order.Asc> getInstances() {
            return instances(v -> AttributeImpl.of(conceptMgr, v.asAttribute()));
        }

        @Override
        public Forwardable<AttributeImpl<?>, Order.Asc> getInstancesExplicit() {
            return emptySorted();
        }

        @Override
        public void setOwns(AttributeType attributeType, Set<TypeQLToken.Annotation> annotations) {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public void setOwns(AttributeType attributeType, AttributeType overriddenType, Set<TypeQLToken.Annotation> annotations) {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public void setPlays(RoleType roleType) {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public void setPlays(RoleType roleType, RoleType overriddenType) {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }

        @Override
        public void unsetPlays(RoleType roleType) {
            throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
        }
    }

    public static class Boolean extends AttributeTypeImpl implements AttributeType.Boolean {

        public Boolean(ConceptManager conceptMgr, java.lang.String label) {
            super(conceptMgr, label, java.lang.Boolean.class);
        }

        private Boolean(ConceptManager conceptMgr, TypeVertex vertex) {
            super(conceptMgr, vertex);
            if (!vertex.label().equals(ATTRIBUTE.label()) &&
                    !vertex.valueType().equals(BOOLEAN)) {
                throw exception(TypeDBException.of(VALUE_TYPE_MISMATCH, vertex.label(),
                        BOOLEAN.name(), vertex.valueType().name()));
            }
        }

        public static AttributeTypeImpl.Boolean of(ConceptManager conceptMgr, TypeVertex vertex) {
            return vertex.label().equals(ATTRIBUTE.label()) ?
                    new Root(conceptMgr, vertex) :
                    new AttributeTypeImpl.Boolean(conceptMgr, vertex);
        }

        @Override
        public Forwardable<AttributeTypeImpl.Boolean, Order.Asc> getSubtypes() {
            return iterateSorted(graphMgr().schema().getSubtypes(vertex), ASC)
                    .mapSorted(v -> AttributeTypeImpl.Boolean.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
        }

        @Override
        public Forwardable<AttributeTypeImpl.Boolean, Order.Asc> getSubtypesExplicit() {
            return super.getSubtypesExplicit(v -> AttributeTypeImpl.Boolean.of(conceptMgr, v));
        }

        @Override
        public Forwardable<AttributeImpl.Boolean, Order.Asc> getInstances() {
            return instances(v -> new AttributeImpl.Boolean(conceptMgr, v.asAttribute().asBoolean()));
        }

        @Override
        public Forwardable<AttributeImpl.Boolean, Order.Asc> getInstancesExplicit() {
            return instancesExplicit(v -> new AttributeImpl.Boolean(conceptMgr, v.asAttribute().asBoolean()));
        }

        @Override
        public ValueType getValueType() {
            return ValueType.BOOLEAN;
        }

        @Override
        public boolean isBoolean() {
            return true;
        }

        @Override
        public AttributeTypeImpl.Boolean asBoolean() {
            return this;
        }

        @Override
        public Attribute.Boolean put(boolean value) {
            return put(value, false);
        }

        @Override
        public Attribute.Boolean put(boolean value, boolean isInferred) {
            validateCanHaveInstances(Attribute.class);
            AttributeVertex.Write<java.lang.Boolean> attVertex = graphMgr().data().put(vertex, value, isInferred);
            return new AttributeImpl.Boolean(conceptMgr, attVertex);
        }

        @Override
        public Attribute.Boolean get(boolean value) {
            AttributeVertex<java.lang.Boolean> attVertex = graphMgr().data().getReadable(vertex, value);
            if (attVertex != null) return new AttributeImpl.Boolean(conceptMgr, attVertex);
            else return null;
        }

        private static class Root extends AttributeTypeImpl.Boolean {

            private Root(ConceptManager conceptMgr, TypeVertex vertex) {
                super(conceptMgr, vertex);
                assert vertex.label().equals(ATTRIBUTE.label());
            }

            @Override
            public boolean isRoot() {
                return true;
            }

            @Override
            public Forwardable<AttributeTypeImpl.Boolean, Order.Asc> getSubtypes() {
                return merge(
                        iterateSorted(ASC, this),
                        super.getSubtypeVertices(BOOLEAN).mapSorted(v ->
                                AttributeTypeImpl.Boolean.of(conceptMgr, v), attrType -> attrType.vertex, ASC
                        )
                );
            }

            @Override
            public Forwardable<AttributeTypeImpl.Boolean, Order.Asc> getSubtypesExplicit() {
                return super.getSubtypeVerticesDirect(BOOLEAN)
                        .mapSorted(v -> AttributeTypeImpl.Boolean.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
            }

            @Override
            public void delete() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setLabel(java.lang.String label) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetAbstract() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setSupertype(AttributeType superType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, AttributeType overriddenType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType, RoleType overriddenType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }
        }
    }

    public static class Long extends AttributeTypeImpl implements AttributeType.Long {

        public Long(ConceptManager conceptMgr, java.lang.String label) {
            super(conceptMgr, label, java.lang.Long.class);
        }

        private Long(ConceptManager conceptMgr, TypeVertex vertex) {
            super(conceptMgr, vertex);
            if (!vertex.label().equals(ATTRIBUTE.label()) && !vertex.valueType().equals(LONG)) {
                throw exception(TypeDBException.of(VALUE_TYPE_MISMATCH, vertex.label(),
                        LONG.name(), vertex.valueType().name()));
            }
        }

        public static AttributeTypeImpl.Long of(ConceptManager conceptMgr, TypeVertex vertex) {
            return vertex.label().equals(ATTRIBUTE.label()) ?
                    new Root(conceptMgr, vertex) :
                    new AttributeTypeImpl.Long(conceptMgr, vertex);
        }

        @Override
        public Forwardable<AttributeTypeImpl.Long, Order.Asc> getSubtypes() {
            return iterateSorted(graphMgr().schema().getSubtypes(vertex), ASC)
                    .mapSorted(v -> AttributeTypeImpl.Long.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
        }

        @Override
        public Forwardable<AttributeTypeImpl.Long, Order.Asc> getSubtypesExplicit() {
            return super.getSubtypesExplicit(v -> AttributeTypeImpl.Long.of(conceptMgr, v));
        }

        @Override
        public Forwardable<AttributeImpl.Long, Order.Asc> getInstances() {
            return instances(v -> new AttributeImpl.Long(conceptMgr, v.asAttribute().asLong()));
        }

        @Override
        public Forwardable<AttributeImpl.Long, Order.Asc> getInstancesExplicit() {
            return instancesExplicit(v -> new AttributeImpl.Long(conceptMgr, v.asAttribute().asLong()));
        }

        @Override
        public ValueType getValueType() {
            return ValueType.LONG;
        }

        @Override
        public boolean isLong() {
            return true;
        }

        @Override
        public AttributeTypeImpl.Long asLong() {
            return this;
        }

        @Override
        public Attribute.Long put(long value) {
            return put(value, false);
        }

        @Override
        public Attribute.Long put(long value, boolean isInferred) {
            validateCanHaveInstances(Attribute.class);
            AttributeVertex.Write<java.lang.Long> attVertex = graphMgr().data().put(vertex, value, isInferred);
            return new AttributeImpl.Long(conceptMgr, attVertex);
        }

        @Override
        public Attribute.Long get(long value) {
            AttributeVertex<java.lang.Long> attVertex = graphMgr().data().getReadable(vertex, value);
            if (attVertex != null) return new AttributeImpl.Long(conceptMgr, attVertex);
            else return null;
        }

        private static class Root extends AttributeTypeImpl.Long {

            private Root(ConceptManager conceptMgr, TypeVertex vertex) {
                super(conceptMgr, vertex);
                assert vertex.label().equals(ATTRIBUTE.label());
            }

            @Override
            public boolean isRoot() {
                return true;
            }

            @Override
            public Forwardable<AttributeTypeImpl.Long, Order.Asc> getSubtypes() {
                return merge(
                        iterateSorted(ASC, this),
                        super.getSubtypeVertices(LONG).mapSorted(v ->
                                AttributeTypeImpl.Long.of(conceptMgr, v), attrType -> attrType.vertex, ASC
                        )
                );
            }

            @Override
            public Forwardable<AttributeTypeImpl.Long, Order.Asc> getSubtypesExplicit() {
                return super.getSubtypeVerticesDirect(LONG)
                        .mapSorted(v -> AttributeTypeImpl.Long.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
            }

            @Override
            public void delete() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setLabel(java.lang.String label) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetAbstract() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setSupertype(AttributeType superType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, AttributeType overriddenType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType, RoleType overriddenType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }
        }
    }

    public static class Double extends AttributeTypeImpl implements AttributeType.Double {

        public Double(ConceptManager conceptMgr, java.lang.String label) {
            super(conceptMgr, label, java.lang.Double.class);
        }

        private Double(ConceptManager conceptMgr, TypeVertex vertex) {
            super(conceptMgr, vertex);
            if (!vertex.label().equals(ATTRIBUTE.label()) && !vertex.valueType().equals(DOUBLE)) {
                throw exception(TypeDBException.of(VALUE_TYPE_MISMATCH, vertex.label(),
                        DOUBLE.name(), vertex.valueType().name()));
            }
        }

        public static AttributeTypeImpl.Double of(ConceptManager conceptMgr, TypeVertex vertex) {
            return vertex.label().equals(ATTRIBUTE.label()) ?
                    new Root(conceptMgr, vertex) :
                    new AttributeTypeImpl.Double(conceptMgr, vertex);
        }

        @Override
        public Forwardable<AttributeTypeImpl.Double, Order.Asc> getSubtypes() {
            return iterateSorted(graphMgr().schema().getSubtypes(vertex), ASC)
                    .mapSorted(v -> AttributeTypeImpl.Double.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
        }

        @Override
        public Forwardable<AttributeTypeImpl.Double, Order.Asc> getSubtypesExplicit() {
            return super.getSubtypesExplicit(v -> AttributeTypeImpl.Double.of(conceptMgr, v));
        }

        @Override
        public Forwardable<AttributeImpl.Double, Order.Asc> getInstances() {
            return instances(v -> new AttributeImpl.Double(conceptMgr, v.asAttribute().asDouble()));
        }

        @Override
        public Forwardable<AttributeImpl.Double, Order.Asc> getInstancesExplicit() {
            return instancesExplicit(v -> new AttributeImpl.Double(conceptMgr, v.asAttribute().asDouble()));
        }

        @Override
        public ValueType getValueType() {
            return ValueType.DOUBLE;
        }

        @Override
        public boolean isDouble() {
            return true;
        }

        @Override
        public AttributeTypeImpl.Double asDouble() {
            return this;
        }

        @Override
        public Attribute.Double put(double value) {
            return put(value, false);
        }

        @Override
        public Attribute.Double put(double value, boolean isInferred) {
            validateCanHaveInstances(Attribute.class);
            AttributeVertex.Write<java.lang.Double> attVertex = graphMgr().data().put(vertex, value, isInferred);
            return new AttributeImpl.Double(conceptMgr, attVertex);
        }

        @Override
        public Attribute.Double get(double value) {
            AttributeVertex<java.lang.Double> attVertex = graphMgr().data().getReadable(this.vertex, value);
            if (attVertex != null) return new AttributeImpl.Double(conceptMgr, attVertex);
            else return null;
        }

        private static class Root extends AttributeTypeImpl.Double {

            private Root(ConceptManager conceptMgr, TypeVertex vertex) {
                super(conceptMgr, vertex);
                assert vertex.label().equals(ATTRIBUTE.label());
            }

            @Override
            public boolean isRoot() {
                return true;
            }

            @Override
            public Forwardable<AttributeTypeImpl.Double, Order.Asc> getSubtypes() {
                return merge(
                        iterateSorted(ASC, this),
                        super.getSubtypeVertices(DOUBLE).mapSorted(v ->
                                AttributeTypeImpl.Double.of(conceptMgr, v), attrType -> attrType.vertex, ASC
                        )
                );
            }

            @Override
            public Forwardable<AttributeTypeImpl.Double, Order.Asc> getSubtypesExplicit() {
                return super.getSubtypeVerticesDirect(DOUBLE)
                        .mapSorted(v -> AttributeTypeImpl.Double.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
            }

            @Override
            public void delete() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setLabel(java.lang.String label) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetAbstract() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setSupertype(AttributeType superType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, AttributeType overriddenType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType, RoleType overriddenType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }
        }
    }

    public static class String extends AttributeTypeImpl implements AttributeType.String {

        public String(ConceptManager conceptMgr, java.lang.String label) {
            super(conceptMgr, label, java.lang.String.class);
        }

        private String(ConceptManager conceptMgr, TypeVertex vertex) {
            super(conceptMgr, vertex);
            if (!vertex.label().equals(ATTRIBUTE.label()) && !vertex.valueType().equals(STRING)) {
                throw exception(TypeDBException.of(VALUE_TYPE_MISMATCH, vertex.label(),
                        STRING.name(), vertex.valueType().name()));
            }
        }

        public static AttributeTypeImpl.String of(ConceptManager conceptMgr, TypeVertex vertex) {
            return vertex.label().equals(ATTRIBUTE.label()) ?
                    new Root(conceptMgr, vertex) :
                    new AttributeTypeImpl.String(conceptMgr, vertex);
        }

        @Override
        public Forwardable<AttributeTypeImpl.String, Order.Asc> getSubtypes() {
            return iterateSorted(graphMgr().schema().getSubtypes(vertex), ASC)
                    .mapSorted(v -> AttributeTypeImpl.String.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
        }

        @Override
        public Forwardable<AttributeTypeImpl.String, Order.Asc> getSubtypesExplicit() {
            return super.getSubtypesExplicit(v -> AttributeTypeImpl.String.of(conceptMgr, v));
        }

        @Override
        public Forwardable<AttributeImpl.String, Order.Asc> getInstances() {
            return instances(v -> new AttributeImpl.String(conceptMgr, v.asAttribute().asString()));
        }

        @Override
        public Forwardable<AttributeImpl.String, Order.Asc> getInstancesExplicit() {
            return instancesExplicit(v -> new AttributeImpl.String(conceptMgr, v.asAttribute().asString()));
        }

        @Override
        public boolean isString() {
            return true;
        }

        @Override
        public AttributeTypeImpl.String asString() {
            return this;
        }

        @Override
        public void setRegex(Pattern regex) {
            if (regex != null) {
                // TODO: can we do this in parallel as it was before?
                getInstances().forEachRemaining(attribute -> {
                    Matcher matcher = regex.matcher(attribute.getValue());
                    if (!matcher.matches()) {
                        throw exception(TypeDBException.of(
                                ATTRIBUTE_REGEX_UNSATISFIES_INSTANCES, getLabel(), regex, attribute.getValue()
                        ));
                    }
                });
            }
            vertex.regex(regex);
        }

        @Override
        public void unsetRegex() {
            vertex.regex(null);
        }

        @Override
        public Pattern getRegex() {
            return vertex.regex();
        }

        @Override
        public Attribute.String put(java.lang.String value) {
            return put(value, false);
        }

        @Override
        public Attribute.String put(java.lang.String value, boolean isInferred) {
            validateCanHaveInstances(Attribute.class);
            if (vertex.regex() != null && !getRegex().matcher(value).matches()) {
                throw exception(TypeDBException.of(ATTRIBUTE_VALUE_UNSATISFIES_REGEX, getLabel(), value, getRegex()));
            }
            AttributeVertex.Write<java.lang.String> attVertex = graphMgr().data().put(vertex, value, isInferred);
            return new AttributeImpl.String(conceptMgr, attVertex);
        }

        @Override
        public Attribute.String get(java.lang.String value) {
            AttributeVertex<java.lang.String> attVertex = graphMgr().data().getReadable(vertex, value);
            if (attVertex != null) return new AttributeImpl.String(conceptMgr, attVertex);
            else return null;
        }

        @Override
        public ValueType getValueType() {
            return ValueType.STRING;
        }

        private static class Root extends AttributeTypeImpl.String {

            private Root(ConceptManager conceptMgr, TypeVertex vertex) {
                super(conceptMgr, vertex);
                assert vertex.label().equals(ATTRIBUTE.label());
            }

            @Override
            public boolean isRoot() {
                return true;
            }

            @Override
            public Forwardable<AttributeTypeImpl.String, Order.Asc> getSubtypes() {
                return merge(
                        iterateSorted(ASC, this),
                        super.getSubtypeVertices(STRING).mapSorted(v ->
                                AttributeTypeImpl.String.of(conceptMgr, v), attrType -> attrType.vertex, ASC
                        )
                );
            }

            @Override
            public Forwardable<AttributeTypeImpl.String, Order.Asc> getSubtypesExplicit() {
                return super.getSubtypeVerticesDirect(STRING)
                        .mapSorted(v -> AttributeTypeImpl.String.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
            }

            @Override
            public void delete() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setLabel(java.lang.String label) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetAbstract() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setSupertype(AttributeType superType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, AttributeType overriddenType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType, RoleType overriddenType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setRegex(Pattern regex) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetRegex() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }
        }
    }

    public static class DateTime extends AttributeTypeImpl implements AttributeType.DateTime {

        public DateTime(ConceptManager conceptMgr, java.lang.String label) {
            super(conceptMgr, label, LocalDateTime.class);
        }

        private DateTime(ConceptManager conceptMgr, TypeVertex vertex) {
            super(conceptMgr, vertex);
            if (!vertex.label().equals(ATTRIBUTE.label()) && !vertex.valueType().equals(DATETIME)) {
                throw exception(TypeDBException.of(VALUE_TYPE_MISMATCH, vertex.label(),
                        DATETIME.name(), vertex.valueType().name()));
            }
        }

        public static AttributeTypeImpl.DateTime of(ConceptManager conceptMgr, TypeVertex vertex) {
            return vertex.label().equals(ATTRIBUTE.label()) ?
                    new Root(conceptMgr, vertex) :
                    new AttributeTypeImpl.DateTime(conceptMgr, vertex);
        }

        @Override
        public Forwardable<AttributeTypeImpl.DateTime, Order.Asc> getSubtypes() {
            return iterateSorted(graphMgr().schema().getSubtypes(vertex), ASC)
                    .mapSorted(v -> AttributeTypeImpl.DateTime.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
        }

        @Override
        public Forwardable<AttributeTypeImpl.DateTime, Order.Asc> getSubtypesExplicit() {
            return super.getSubtypesExplicit(v -> AttributeTypeImpl.DateTime.of(conceptMgr, v));
        }

        @Override
        public Forwardable<AttributeImpl.DateTime, Order.Asc> getInstances() {
            return instances(v -> new AttributeImpl.DateTime(conceptMgr, v.asAttribute().asDateTime()));
        }

        @Override
        public Forwardable<AttributeImpl.DateTime, Order.Asc> getInstancesExplicit() {
            return instancesExplicit(v -> new AttributeImpl.DateTime(conceptMgr, v.asAttribute().asDateTime()));
        }

        @Override
        public ValueType getValueType() {
            return ValueType.DATETIME;
        }

        @Override
        public boolean isDateTime() {
            return true;
        }

        @Override
        public AttributeTypeImpl.DateTime asDateTime() {
            return this;
        }

        @Override
        public Attribute.DateTime put(LocalDateTime value) {
            return put(value, false);
        }

        @Override
        public Attribute.DateTime put(LocalDateTime value, boolean isInferred) {
            validateCanHaveInstances(Attribute.class);
            AttributeVertex.Write<LocalDateTime> attVertex = graphMgr().data().put(vertex, value, isInferred);
            return new AttributeImpl.DateTime(conceptMgr, attVertex);
        }

        @Override
        public Attribute.DateTime get(LocalDateTime value) {
            AttributeVertex<java.time.LocalDateTime> attVertex = graphMgr().data().getReadable(vertex, value);
            if (attVertex != null) return new AttributeImpl.DateTime(conceptMgr, attVertex);
            else return null;
        }

        private static class Root extends AttributeTypeImpl.DateTime {

            private Root(ConceptManager conceptMgr, TypeVertex vertex) {
                super(conceptMgr, vertex);
                assert vertex.label().equals(ATTRIBUTE.label());
            }

            @Override
            public boolean isRoot() {
                return true;
            }

            @Override
            public Forwardable<AttributeTypeImpl.DateTime, Order.Asc> getSubtypes() {
                return merge(
                        iterateSorted(ASC, this),
                        super.getSubtypeVertices(DATETIME).mapSorted(v ->
                                AttributeTypeImpl.DateTime.of(conceptMgr, v), attrType -> attrType.vertex, ASC
                        )
                );
            }

            @Override
            public Forwardable<AttributeTypeImpl.DateTime, Order.Asc> getSubtypesExplicit() {
                return super.getSubtypeVerticesDirect(DATETIME)
                        .mapSorted(v -> AttributeTypeImpl.DateTime.of(conceptMgr, v), attrType -> attrType.vertex, ASC);
            }

            @Override
            public void delete() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setLabel(java.lang.String label) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetAbstract() {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setSupertype(AttributeType superType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setOwns(AttributeType attributeType, AttributeType overriddenType, Set<TypeQLToken.Annotation> annotations) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void setPlays(RoleType roleType, RoleType overriddenType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }

            @Override
            public void unsetPlays(RoleType roleType) {
                throw exception(TypeDBException.of(ROOT_TYPE_MUTATION));
            }
        }
    }
}
