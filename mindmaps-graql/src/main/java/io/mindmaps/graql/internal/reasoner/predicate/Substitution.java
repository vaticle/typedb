/*
 * MindmapsDB - A Distributed Semantic Database
 * Copyright (C) 2016  Mindmaps Research Ltd
 *
 * MindmapsDB is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * MindmapsDB is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with MindmapsDB. If not, see <http://www.gnu.org/licenses/gpl.txt>.
 */

package io.mindmaps.graql.internal.reasoner.predicate;

import io.mindmaps.concept.Concept;
import io.mindmaps.graql.Graql;
import io.mindmaps.graql.admin.VarAdmin;
import io.mindmaps.graql.internal.reasoner.query.Query;

public class Substitution extends AtomBase{

    private final String val;

    public Substitution(VarAdmin pattern) {
        super(pattern);
        this.val = extractValue(pattern);
    }

    public Substitution(VarAdmin pattern, Query par) {
        super(pattern, par);
        this.val = extractValue(pattern);
    }

    public Substitution(Substitution a) {
        super(a);
        this.val = extractValue(a.getPattern().asVar());
    }

    public Substitution(String varName, Concept con) {
        super(createSubstitution(varName, con));
        this.val = con.getId();
    }

    public Substitution(String varName, Concept con, Query parent) {
        this(varName, con);
        setParentQuery(parent);
    }

    public static VarAdmin createSubstitution(String varName, Concept con){
        return Graql.var(varName).id(con.getId()).admin();
    }

    @Override
    public Atomic clone(){
        return new Substitution(this);
    }

    @Override
    public boolean isSubstitution(){ return true;}
    @Override
    public boolean isRuleResolvable(){ return false;}

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof Substitution)) return false;
        Substitution a2 = (Substitution) obj;
        return this.getVarName().equals(a2.getVarName())
                && this.getVal().equals(a2.getVal());
    }

    @Override
    public int hashCode() {
        int hashCode = 1;
        hashCode = hashCode * 37 + this.val.hashCode();
        hashCode = hashCode * 37 + this.varName.hashCode();
        return hashCode;
    }

    @Override
    public boolean isEquivalent(Object obj){
        if (!(obj instanceof Substitution)) return false;
        Substitution a2 = (Substitution) obj;
        return this.getVal().equals(a2.getVal());
    }

    @Override
    public int equivalenceHashCode() {
        int hashCode = 1;
        hashCode = hashCode * 37 + this.val.hashCode();
        return hashCode;
    }

    @Override
    public String getVal(){ return val;}

    private String extractValue(VarAdmin var){ return var.admin().getId().orElse("");}
}
