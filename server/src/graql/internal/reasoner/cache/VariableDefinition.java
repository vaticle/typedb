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

package grakn.core.graql.internal.reasoner.cache;

import com.google.common.collect.Sets;
import grakn.core.graql.concept.Role;
import grakn.core.graql.concept.Type;
import grakn.core.graql.internal.reasoner.atom.predicate.ValuePredicate;
import java.util.Objects;
import java.util.Set;
import javax.annotation.Nullable;

/**
 * Defines a variable specification in the form:
 * - type,
 * - role (if corresponds to role variable
 * - roles it plays (if corresponds to roleplayer variable)
 * - valuePredicates it has
 *
 * @author Kasper Piskorski
 *
 */
public class VariableDefinition {

    final private Type type;
    final private Role role;
    final private Set<Role> playedRoles;
    final private Set<ValuePredicate> vps;

    public VariableDefinition(@Nullable Type type, @Nullable Role role, Set<Role> playedRoles, Set<ValuePredicate> vps){
        this.type = type;
        this.role = role;
        this.playedRoles = playedRoles;
        this.vps = vps;
    }

    @Override
    public String toString(){
        return "{" +
                "type: " + type + ", " +
                "role: " + role + ", " +
                "playedRoles: " + playedRoles + ", " +
                "vps: " + vps +
                "}";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        VariableDefinition that = (VariableDefinition) o;
        return Objects.equals(type, that.type) &&
                Objects.equals(role, that.role) &&
                Objects.equals(playedRoles, that.playedRoles) &&
                Objects.equals(vps, that.vps);
    }

    @Override
    public int hashCode() {
        return Objects.hash(type, role, playedRoles, vps);
    }

    public Type type(){ return type;}
    public Role role(){ return role;}
    public Set<Role> playedRoles(){ return playedRoles;}
    public Set<ValuePredicate> valuePredicates(){ return vps;}

    public VariableDefinition merge(VariableDefinition def){
        return new VariableDefinition(
                def.type() != null? def.type() : this.type(),
                def.role() != null? def.role() : this.role(),
                Sets.union(def.playedRoles(), this.playedRoles()),
                Sets.union(def.valuePredicates(), this.valuePredicates())
        );
    }

    public boolean isTrivial(){
        return type == null
                && role == null
                && playedRoles.isEmpty()
                && vps.isEmpty();
    }
}
