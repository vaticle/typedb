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

package com.vaticle.typedb.core.traversal.predicate;

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.traversal.GraphTraversal;
import com.vaticle.typeql.lang.common.TypeQLToken;

import java.util.Map;

import static com.vaticle.typedb.common.collection.Collections.map;
import static com.vaticle.typedb.common.collection.Collections.pair;
import static com.vaticle.typedb.common.util.Objects.className;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_CAST;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;

public abstract class PredicateOperator {

    private final TypeQLToken.Predicate token;

    protected PredicateOperator(TypeQLToken.Predicate token) {
        this.token = token;
    }

    public static PredicateOperator of(TypeQLToken.Predicate token) {
        if (token.isEquality()) return Equality.of(token.asEquality());
        else if (token.isSubString()) return SubString.of(token.asSubString());
        else throw TypeDBException.of(ILLEGAL_STATE);
    }

    public boolean isEquality() { return false; }

    boolean isSubString() { return false; }

    Equality asEquality() {
        throw TypeDBException.of(ILLEGAL_CAST, className(this.getClass()), className(Equality.class));
    }

    SubString asSubString() {
        throw TypeDBException.of(ILLEGAL_CAST, className(this.getClass()), className(SubString.class));
    }

    @Override
    public String toString() {
        return token.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PredicateOperator that = (PredicateOperator) o;
        return this.token.equals(that.token);
    }

    @Override
    public int hashCode() {
        return token.hashCode();
    }

    public static abstract class Equality extends PredicateOperator {

        public Equality(TypeQLToken.Predicate.Equality token) {
            super(token);
        }

        abstract boolean apply(int comparisonResult);

        abstract Equality reflection();

        @Override
        public boolean isEquality() { return true; }

        @Override
        Equality asEquality() { return this; }

        public static final Equality EQ = new Equality(TypeQLToken.Predicate.Equality.EQ) {
            @Override
            boolean apply(int comparisonResult) { return comparisonResult == 0; }

            @Override
            Equality reflection() { return this; }
        };

        public static final Equality NEQ = new Equality(TypeQLToken.Predicate.Equality.NEQ) {
            @Override
            boolean apply(int comparisonResult) { return comparisonResult != 0; }

            @Override
            Equality reflection() { return this; }
        };

        public static final Equality GT = new Equality(TypeQLToken.Predicate.Equality.GT) {
            @Override
            boolean apply(int comparisonResult) { return comparisonResult > 0; }

            @Override
            Equality reflection() { return LT; }
        };

        public static final Equality GTE = new Equality(TypeQLToken.Predicate.Equality.GTE) {
            @Override
            boolean apply(int comparisonResult) { return comparisonResult >= 0; }

            @Override
            Equality reflection() { return LTE; }
        };

        public static final Equality LT = new Equality(TypeQLToken.Predicate.Equality.LT) {
            @Override
            boolean apply(int comparisonResult) { return comparisonResult < 0; }

            @Override
            Equality reflection() { return GT; }
        };

        public static final Equality LTE = new Equality(TypeQLToken.Predicate.Equality.LTE) {
            @Override
            boolean apply(int comparisonResult) { return comparisonResult <= 0; }

            @Override
            Equality reflection() { return GTE; }
        };

        private static final Map<TypeQLToken.Predicate.Equality, Equality> operators = map(
                pair(TypeQLToken.Predicate.Equality.EQ, Equality.EQ),
                pair(TypeQLToken.Predicate.Equality.NEQ, Equality.NEQ),
                pair(TypeQLToken.Predicate.Equality.GT, Equality.GT),
                pair(TypeQLToken.Predicate.Equality.GTE, Equality.GTE),
                pair(TypeQLToken.Predicate.Equality.LT, Equality.LT),
                pair(TypeQLToken.Predicate.Equality.LTE, Equality.LTE)
        );

        public static Equality of(TypeQLToken.Predicate.Equality operator) {
            return Equality.operators.get(operator);
        }
    }

    public static abstract class SubString extends PredicateOperator {

        public SubString(TypeQLToken.Predicate.SubString token) {
            super(token);
        }

        abstract boolean apply(String vertexValue, GraphTraversal.Thing.Parameters.Value predicateValue);

        @Override
        boolean isSubString() { return true; }

        @Override
        SubString asSubString() { return this; }

        private static final SubString CONTAINS = new SubString(TypeQLToken.Predicate.SubString.CONTAINS) {
            @Override
            boolean apply(String vertexValue, GraphTraversal.Thing.Parameters.Value predicateValue) {
                assert predicateValue.isString();
                return containsIgnoreCase(vertexValue, predicateValue.getString());
            }

            private boolean containsIgnoreCase(String str1, String str2) {
                int len2 = str2.length();
                if (len2 == 0) return true; // Empty string is contained

                char first2Lo = Character.toLowerCase(str2.charAt(0));
                char first2Up = Character.toUpperCase(str2.charAt(0));

                for (int i = 0; i <= str1.length() - len2; i++) {
                    // Quick check before calling the more expensive regionMatches() method:
                    char first1 = str1.charAt(i);
                    if (first1 != first2Lo && first1 != first2Up) continue;
                    if (str1.regionMatches(true, i, str2, 0, len2)) return true;
                }
                return false;
            }
        };

        private static final SubString LIKE = new SubString(TypeQLToken.Predicate.SubString.LIKE) {
            @Override
            boolean apply(String vertexValue, GraphTraversal.Thing.Parameters.Value predicateValue) {
                assert predicateValue.isRegex();
                return predicateValue.getRegex().matcher(vertexValue).matches();
            }
        };

        private static final Map<TypeQLToken.Predicate.SubString, SubString> operators = map(
                pair(TypeQLToken.Predicate.SubString.CONTAINS, SubString.CONTAINS),
                pair(TypeQLToken.Predicate.SubString.LIKE, SubString.LIKE)
        );

        private static SubString of(TypeQLToken.Predicate.SubString token) {
            return operators.get(token);
        }
    }
}
