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

package com.vaticle.typedb.core.traversal.graph;

import com.vaticle.typedb.core.common.parameters.Label;
import com.vaticle.typedb.core.graph.common.Encoding;
import com.vaticle.typedb.core.traversal.common.Identifier;
import com.vaticle.typedb.core.traversal.predicate.Predicate;

import java.util.HashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

public abstract class TraversalVertex<EDGE extends TraversalEdge<?, ?>, PROPERTIES extends TraversalVertex.Properties> {

    private final Identifier identifier;
    private final Set<EDGE> outgoing;
    private final Set<EDGE> incoming;
    private final int hash;
    private PROPERTIES properties;

    public TraversalVertex(Identifier identifier) {
        this.identifier = identifier;
        this.outgoing = new HashSet<>();
        this.incoming = new HashSet<>();
        this.properties = newProperties();
        this.hash = Objects.hash(identifier);
    }

    protected abstract PROPERTIES newProperties();

    public boolean isThing() { return false; }

    public boolean isType() { return false; }

    public Identifier id() {
        return identifier;
    }

    public Set<EDGE> outs() {
        return outgoing;
    }

    public Set<EDGE> ins() {
        return incoming;
    }

    public void out(EDGE edge) {
        assert edge.from().equals(this);
        outgoing.add(edge);
    }

    public void in(EDGE edge) {
        assert edge.to().equals(this);
        incoming.add(edge);
    }

    public PROPERTIES props() {
        return properties;
    }

    public void props(PROPERTIES properties) {
        this.properties = properties;
    }

    @Override
    public String toString() {
        return identifier.toString() + " " + properties.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TraversalVertex<?, ?> that = (TraversalVertex<?, ?>) o;
        return this.identifier.equals(that.identifier);
        // We do not consider the properties stored in the vertex as doing that
        // would result in an inconsistent identity (hash/equality)
        // (and screw up with HashMaps or HashSets)
    }

    @Override
    public int hashCode() {
        return hash;
    }

    public static abstract class Properties {

        @Override
        public abstract String toString();

        @Override
        public abstract boolean equals(Object o);

        @Override
        public abstract int hashCode();

        public static class Thing extends Properties {

            private boolean hasIID;
            private boolean hasEqualityPredicate;
            private final Set<Label> types;
            private final Set<Predicate.Value<?>> predicates;

            public Thing() {
                hasIID = false;
                hasEqualityPredicate = false;
                types = new HashSet<>();
                predicates = new HashSet<>();
            }

            public boolean hasIID() {
                return hasIID;
            }

            public void hasIID(boolean hasIID) {
                this.hasIID = hasIID;
            }

            public Set<Label> types() {
                return types;
            }

            public void types(Set<Label> types) {
                this.types.addAll(types);
            }

            public boolean hasEqualityPredicate() {
                return hasEqualityPredicate;
            }

            public Set<Predicate.Value<?>> predicates() {
                return predicates;
            }

            public void predicate(Predicate.Value<?> predicate) {
                if (predicate.operator().isEquality()) hasEqualityPredicate = true;
                predicates.add(predicate);
            }

            @Override
            public String toString() {
                return String.format("[thing] { hasIID: %s, types: %s, predicates: %s }",
                                     hasIID, types, predicates);
            }

            @Override
            public boolean equals(Object o) {
                if (this == o) return true;
                if (o == null || getClass() != o.getClass()) return false;

                Properties.Thing that = (Properties.Thing) o;
                return (this.hasIID == that.hasIID &&
                        this.types.equals(that.types) &&
                        this.predicates.equals(that.predicates));
            }

            @Override
            public int hashCode() {
                return Objects.hash(this.hasIID, this.types, this.predicates);
            }
        }

        public static class Type extends Properties {

            private boolean isAbstract;
            private final Set<Label> labels;
            private final Set<Encoding.ValueType> valueTypes;
            private String regex;

            public Type() {
                labels = new HashSet<>();
                valueTypes = new HashSet<>();
            }

            public void clearLabels() {
                labels.clear();
            }

            public Set<Label> labels() {
                return labels;
            }

            public void labels(Label label) {
                this.labels.add(label);
            }

            public void labels(Set<Label> labels) {
                this.labels.addAll(labels);
            }

            public boolean isAbstract() {
                return isAbstract;
            }

            public void setAbstract() {
                assert !this.isAbstract;
                this.isAbstract = true;
            }

            public Set<Encoding.ValueType> valueTypes() {
                return valueTypes;
            }

            public void valueType(Encoding.ValueType valueType) {
                this.valueTypes.add(valueType);
            }

            public Optional<String> regex() {
                return Optional.ofNullable(regex);
            }

            public void regex(String regex) {
                this.regex = regex;
            }

            @Override
            public String toString() {
                return String.format("[type] { labels: %s, abstract: %s, value: %s, regex: %s }",
                                     labels, isAbstract, valueTypes, regex);
            }

            @Override
            public boolean equals(Object o) {
                if (this == o) return true;
                if (o == null || getClass() != o.getClass()) return false;

                Properties.Type that = (Properties.Type) o;
                return (this.isAbstract == that.isAbstract &&
                        this.labels.equals(that.labels) &&
                        this.valueTypes.equals(that.valueTypes) &&
                        Objects.equals(this.regex, that.regex));
            }

            @Override
            public int hashCode() {
                return Objects.hash(this.isAbstract, this.labels, this.valueTypes, this.regex);
            }
        }
    }
}
