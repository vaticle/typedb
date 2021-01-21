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

package grakn.core.pattern.constraint.type;

import grakn.core.pattern.Conjunction;
import grakn.core.pattern.equivalence.AlphaEquivalence;
import grakn.core.pattern.equivalence.AlphaEquivalent;
import grakn.core.pattern.variable.TypeVariable;
import grakn.core.traversal.Traversal;
import graql.lang.common.GraqlArg;

import java.util.Objects;

import static grakn.common.collection.Collections.set;
import static graql.lang.common.GraqlToken.Char.SPACE;
import static graql.lang.common.GraqlToken.Constraint.VALUE_TYPE;

public class ValueTypeConstraint extends TypeConstraint implements AlphaEquivalent<ValueTypeConstraint> {

    private final GraqlArg.ValueType valueType;
    private final int hash;

    public ValueTypeConstraint(TypeVariable owner, GraqlArg.ValueType valueType) {
        super(owner, set());
        this.valueType = valueType;
        this.hash = Objects.hash(ValueTypeConstraint.class, this.owner, this.valueType);
    }

    static ValueTypeConstraint of(TypeVariable owner,
                                  graql.lang.pattern.constraint.TypeConstraint.ValueType constraint) {
        return new ValueTypeConstraint(owner, constraint.valueType());
    }

    static ValueTypeConstraint of(TypeVariable owner, ValueTypeConstraint clone) {
        return new ValueTypeConstraint(owner, clone.valueType());
    }

    public GraqlArg.ValueType valueType() {
        return valueType;
    }

    @Override
    public void addTo(Traversal traversal) {
        traversal.valueType(owner.id(), valueType);
    }

    @Override
    public boolean isValueType() {
        return true;
    }

    @Override
    public ValueTypeConstraint asValueType() {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ValueTypeConstraint that = (ValueTypeConstraint) o;
        return (this.owner.equals(that.owner) && this.valueType.equals(that.valueType));
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public String toString() {
        return owner.toString() + SPACE + VALUE_TYPE + SPACE + valueType.toString();
    }

    @Override
    public AlphaEquivalence alphaEquals(ValueTypeConstraint that) {
        return AlphaEquivalence.valid().validIf(valueType().equals(that.valueType()));
    }

    @Override
    public ValueTypeConstraint clone(Conjunction.Cloner cloner) {
        return cloner.cloneVariable(owner).valueType(valueType);
    }
}
