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

import grakn.core.common.parameters.Label;
import grakn.core.pattern.Conjunction;
import grakn.core.pattern.variable.TypeVariable;
import grakn.core.pattern.variable.VariableCloner;
import grakn.core.pattern.variable.VariableRegistry;
import grakn.core.traversal.Traversal;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import static grakn.common.collection.Collections.set;
import static graql.lang.common.GraqlToken.Char.SPACE;
import static graql.lang.common.GraqlToken.Constraint.SUB;
import static graql.lang.common.GraqlToken.Constraint.SUBX;

public class SubConstraint extends TypeConstraint {

    private final TypeVariable type;
    private final boolean isExplicit;
    private final int hash;
    private final Set<Label> typeHints;

    public SubConstraint(TypeVariable owner, TypeVariable type, boolean isExplicit) {
        super(owner, set(type));
        if (type == null) throw new NullPointerException("Null superType");
        this.type = type;
        this.isExplicit = isExplicit;
        this.hash = Objects.hash(SubConstraint.class, this.owner, this.type, this.isExplicit);
        this.typeHints = new HashSet<>();
        type.constraining(this);
    }

    static SubConstraint of(TypeVariable owner, graql.lang.pattern.constraint.TypeConstraint.Sub constraint,
                            VariableRegistry registry) {
        return new SubConstraint(owner, registry.register(constraint.type()), constraint.isExplicit());
    }

    static SubConstraint of(TypeVariable owner, SubConstraint clone, VariableCloner cloner) {
        return new SubConstraint(owner, cloner.clone(clone.type()), clone.isExplicit());
    }

    public TypeVariable type() {
        return type;
    }

    @Override
    public void addTo(Traversal traversal) {
        // TODO: is there a scenario where we are able to skip this edge with the help of TypeResolver?
        traversal.sub(owner.id(), type.id(), !isExplicit);
    }

    @Override
    public boolean isSub() {
        return true;
    }

    public boolean isExplicit() {
        return isExplicit;
    }

    @Override
    public SubConstraint asSub() {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        final SubConstraint that = (SubConstraint) o;
        return (this.owner.equals(that.owner) &&
                this.type.equals(that.type) &&
                this.isExplicit == that.isExplicit);
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public String toString() {
        return "" + (isExplicit ? SUBX : SUB) + SPACE + type.referenceSyntax();
    }

    @Override
    public SubConstraint clone(Conjunction.Cloner cloner) {
        return cloner.cloneVariable(owner).sub(cloner.cloneVariable(type), isExplicit);
    }
}
