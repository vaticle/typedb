/*
 * Grakn - A Distributed Semantic Database
 * Copyright (C) 2016  Grakn Labs Limited
 *
 * Grakn is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Grakn is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Grakn. If not, see <http://www.gnu.org/licenses/gpl.txt>.
 */

package ai.grakn.graql.internal.reasoner.atom;

import ai.grakn.GraknGraph;
import ai.grakn.graql.admin.Atomic;
import ai.grakn.graql.admin.Conjunction;
import ai.grakn.graql.admin.PatternAdmin;
import ai.grakn.graql.internal.reasoner.query.Query;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

/**
 *
 * <p>
 * Factory class for creating atoms out of graql variables and patterns.
 * </p>
 *
 * @author Kasper Piskorski
 *
 */
public class AtomicFactory {
    
    /**
     * @param atom to be copied
     * @param parent query the copied atom should belong to
     * @return atom copy
     */
    public static Atomic create(Atomic atom, Query parent) {
        Atomic copy = atom.clone();
        ((AtomBase)copy).setParentQuery(parent);
        return copy;
    }

    /**
     * @param pattern conjunction of patterns to be converted to atoms
     * @param parent query the created atoms should belong to
     * @param graph graph of interest
     * @return set of atoms
     */
    public static Set<Atomic> createAtomSet(Conjunction<PatternAdmin> pattern, Query parent, GraknGraph graph) {
        Set<Atomic> atoms = new HashSet<>();
        pattern.getVars().stream()
                .flatMap(var -> var.getProperties()
                        .map(prop -> PropertyMapper.map(prop, var, pattern.getVars()))
                        .filter(Objects::nonNull))
                .forEach(atoms::add);
        atoms.forEach(at -> ((AtomBase) at).setParentQuery(parent));
        return atoms;
    }
}
