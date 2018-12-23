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

package grakn.core.graql.internal.reasoner.atom.predicate;

import com.google.auto.value.AutoValue;
import grakn.core.graql.admin.Atomic;
import grakn.core.graql.admin.ReasonerQuery;
import grakn.core.graql.admin.Unifier;
import grakn.core.graql.exception.GraqlQueryException;
import grakn.core.graql.query.pattern.Statement;
import grakn.core.graql.query.pattern.StatementImpl;
import grakn.core.graql.query.pattern.Variable;
import grakn.core.graql.query.pattern.property.ValueProperty;
import org.apache.tinkerpop.gremlin.process.traversal.P;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Collectors;

/**
 *
 * <p>
 * Predicate implementation specialising it to be an value predicate. Corresponds to {@link ValueProperty}.
 * </p>
 *
 *
 */
@AutoValue
public abstract class ValuePredicate extends Predicate<grakn.core.graql.query.predicate.ValuePredicate> {

    @Override public abstract Statement getPattern();
    @Override public abstract ReasonerQuery getParentQuery();

    //need to have it explicitly here cause autovalue gets confused with the generic
    public abstract grakn.core.graql.query.predicate.ValuePredicate getPredicate();

    public static ValuePredicate create(Statement pattern, ReasonerQuery parent) {
        return new AutoValue_ValuePredicate(pattern.var(), pattern, parent, extractPredicate(pattern));
    }
    public static ValuePredicate create(Variable varName, grakn.core.graql.query.predicate.ValuePredicate pred, ReasonerQuery parent) {
        return create(createValueVar(varName, pred), parent);
    }
    private static ValuePredicate create(ValuePredicate pred, ReasonerQuery parent) {
        return create(pred.getPattern(), parent);
    }

    public static Statement createValueVar(Variable name, grakn.core.graql.query.predicate.ValuePredicate pred) {
        return new StatementImpl(name).val(pred);
    }

    private static grakn.core.graql.query.predicate.ValuePredicate extractPredicate(Statement pattern) {
        Iterator<ValueProperty> properties = pattern.getProperties(ValueProperty.class).iterator();
        ValueProperty property = properties.next();
        if (properties.hasNext()) {
            throw GraqlQueryException.valuePredicateAtomWithMultiplePredicates();
        }
        return property.predicate();
    }

    @Override
    public Atomic copy(ReasonerQuery parent) {
        return create(this, parent);
    }

    @Override
    public String toString(){ return "[" + getVarName() + " val " + getPredicate() + "]"; }

    public Set<ValuePredicate> unify(Unifier u){
        Collection<Variable> vars = u.get(getVarName());
        return vars.isEmpty()?
                Collections.singleton(this) :
                vars.stream().map(v -> create(v, getPredicate(), this.getParentQuery())).collect(Collectors.toSet());
    }

    @Override
    public boolean isAlphaEquivalent(Object obj){
        if (obj == null || this.getClass() != obj.getClass()) return false;
        if (obj == this) return true;
        ValuePredicate p2 = (ValuePredicate) obj;
        return this.getPredicate().getClass().equals(p2.getPredicate().getClass()) &&
                this.getPredicateValue().equals(p2.getPredicateValue());
    }

    @Override
    public int alphaEquivalenceHashCode() {
        int hashCode = super.alphaEquivalenceHashCode();
        hashCode = hashCode * 37 + this.getPredicate().getClass().getName().hashCode();
        return hashCode;
    }

    @Override
    public boolean isCompatibleWith(Object obj) {
        if (this.isAlphaEquivalent(obj)) return true;
        if (obj == null || this.getClass() != obj.getClass()) return false;
        if (obj == this) return true;
        ValuePredicate that = (ValuePredicate) obj;
        return this.getPredicate().isCompatibleWith(that.getPredicate());
    }

    @Override
    public boolean subsumes(Atomic atomic){
        if (this.isAlphaEquivalent(atomic)) return true;
        if (atomic == null || this.getClass() != atomic.getClass()) return false;
        if (atomic == this) return true;
        ValuePredicate that = (ValuePredicate) atomic;
        return this.getPredicate().subsumes(that.getPredicate());
    }

    @Override
    public String getPredicateValue() {
        return getPredicate().getPredicate().map(P::getValue).map(Object::toString).orElse("");
    }

    @Override
    public Set<Variable> getVarNames(){
        Set<Variable> vars = super.getVarNames();
        Statement innerVar = getPredicate().getInnerVar().orElse(null);
        if(innerVar != null && innerVar.var().isUserDefinedName()) vars.add(innerVar.var());
        return vars;
    }
}
