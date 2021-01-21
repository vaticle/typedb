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

import grakn.core.common.exception.GraknException;
import grakn.core.pattern.Conjunction;
import grakn.core.pattern.variable.TypeVariable;
import grakn.core.pattern.variable.VariableCloner;
import grakn.core.pattern.variable.VariableRegistry;
import grakn.core.traversal.Traversal;

import javax.annotation.Nullable;
import java.util.HashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import static grakn.core.common.exception.ErrorMessage.TypeRead.OVERRIDDEN_TYPES_IN_TRAVERSAL;
import static graql.lang.common.GraqlToken.Char.COLON;
import static graql.lang.common.GraqlToken.Char.SPACE;
import static graql.lang.common.GraqlToken.Constraint.AS;
import static graql.lang.common.GraqlToken.Constraint.PLAYS;

public class PlaysConstraint extends TypeConstraint {

    private final TypeVariable relationType;
    private final TypeVariable roleType;
    private final TypeVariable overriddenRoleType;
    private final int hash;

    public PlaysConstraint(TypeVariable owner, @Nullable TypeVariable relationType,
                           TypeVariable roleType, @Nullable TypeVariable overriddenRoleType) {
        super(owner, additionalTypes(roleType, relationType, overriddenRoleType));
        if (roleType == null) throw new NullPointerException("Null role");
        this.relationType = relationType;
        this.roleType = roleType;
        this.overriddenRoleType = overriddenRoleType;
        this.hash = Objects.hash(PlaysConstraint.class, this.owner, this.relationType,
                                 this.roleType, this.overriddenRoleType);
        if (relationType != null) relationType.constraining(this);
        roleType.constraining(this);
        if (overriddenRoleType != null) overriddenRoleType.constraining(this);
    }

    static PlaysConstraint of(TypeVariable owner, graql.lang.pattern.constraint.TypeConstraint.Plays constraint,
                              VariableRegistry registry) {
        TypeVariable roleType = registry.register(constraint.role());
        TypeVariable relationType = constraint.relation().map(registry::register).orElse(null);
        TypeVariable overriddenType = constraint.overridden().map(registry::register).orElse(null);
        return new PlaysConstraint(owner, relationType, roleType, overriddenType);
    }

    static PlaysConstraint of(TypeVariable owner, PlaysConstraint role, VariableCloner cloner) {
        TypeVariable roleType = cloner.clone(role.role());
        TypeVariable relationType = role.relation().map(cloner::clone).orElse(null);
        TypeVariable overriddenType = role.overridden().map(cloner::clone).orElse(null);
        return new PlaysConstraint(owner, relationType, roleType, overriddenType);
    }

    public Optional<TypeVariable> relation() {
        return Optional.ofNullable(relationType);
    }

    public TypeVariable role() {
        return roleType;
    }

    public Optional<TypeVariable> overridden() {
        return Optional.ofNullable(overriddenRoleType);
    }

    @Override
    public void addTo(Traversal traversal) {
        if (overridden().isPresent()) throw GraknException.of(OVERRIDDEN_TYPES_IN_TRAVERSAL);
        traversal.plays(owner.id(), roleType.id());
    }

    @Override
    public boolean isPlays() {
        return true;
    }

    @Override
    public PlaysConstraint asPlays() {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        PlaysConstraint that = (PlaysConstraint) o;
        return (this.owner.equals(that.owner) &&
                this.roleType.equals(that.roleType) &&
                Objects.equals(this.relationType, that.relationType) &&
                Objects.equals(this.overriddenRoleType, that.overriddenRoleType));
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public String toString() {
        return owner.toString() + SPACE + PLAYS
                + (relation().isPresent() ? "" + SPACE + relationType + COLON : "") + SPACE + roleType.toString()
                + (overridden().isPresent() ? "" + SPACE + AS + SPACE + overriddenRoleType.toString() : "");
    }

    @Override
    public PlaysConstraint clone(Conjunction.Cloner cloner) {
        return cloner.cloneVariable(owner).plays(
                relationType == null ? null : cloner.cloneVariable(relationType),
                cloner.cloneVariable(roleType),
                overriddenRoleType == null ? null : cloner.cloneVariable(overriddenRoleType)
        );
    }

    private static Set<TypeVariable> additionalTypes(TypeVariable roleType, TypeVariable relationType, TypeVariable overriddenRoleType) {
        Set<TypeVariable> variables = new HashSet<>();
        variables.add(roleType);
        if (relationType != null) variables.add(relationType);
        if (overriddenRoleType != null) variables.add(overriddenRoleType);
        return variables;
    }

}
