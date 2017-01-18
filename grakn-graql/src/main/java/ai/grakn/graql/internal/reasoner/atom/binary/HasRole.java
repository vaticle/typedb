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

package ai.grakn.graql.internal.reasoner.atom.binary;

import ai.grakn.graql.admin.ReasonerQuery;
import ai.grakn.graql.admin.VarAdmin;
import ai.grakn.graql.admin.Atomic;
import ai.grakn.graql.internal.reasoner.atom.predicate.IdPredicate;

/**
 *
 * <p>
 * Atom implementation defining a has-role atom.
 * </p>
 *
 * @author Kasper Piskorski
 *
 */
public class HasRole extends SelectableTypeAtom {

    public HasRole(VarAdmin pattern, IdPredicate predicate, ReasonerQuery par) {
        super(pattern, predicate, par);
    }

    private HasRole(HasRole a){
        super(a);
    }

    @Override
    public Atomic clone(){ return new HasRole(this);}
}
