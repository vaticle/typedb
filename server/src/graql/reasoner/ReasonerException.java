/*
 * GRAKN.AI - THE KNOWLEDGE GRAPH
 * Copyright (C) 2019 Grakn Labs Ltd
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

package grakn.core.graql.reasoner;

import grakn.core.common.exception.ErrorMessage;
import grakn.core.common.exception.GraknException;
import grakn.core.concept.answer.ConceptMap;
import server.src.graql.reasoner.atom.Atomic;
import server.src.graql.reasoner.query.ReasonerQuery;
import graql.lang.statement.Statement;
import graql.lang.statement.Variable;

import java.util.Set;

public class ReasonerException extends GraknException {

    private ReasonerException(String error) { super(error); }

    @Override
    public String getName() { return getClass().getName(); }

    public static ReasonerException maxIterationsReached(Class<?> clazz) {
        return new ReasonerException(ErrorMessage.MAX_ITERATION_REACHED.getMessage(clazz.toString()));
    }

    public static ReasonerException ambiguousType(Variable var, Set<grakn.core.concept.api.Type> types) {
        return new ReasonerException(ErrorMessage.AMBIGUOUS_TYPE.getMessage(var, types));
    }

    public static ReasonerException incompleteResolutionPlan(ReasonerQuery reasonerQuery) {
        return new ReasonerException(ErrorMessage.INCOMPLETE_RESOLUTION_PLAN.getMessage(reasonerQuery));
    }

    public static ReasonerException rolePatternAbsent(Atomic relation) {
        return new ReasonerException(ErrorMessage.ROLE_PATTERN_ABSENT.getMessage(relation));
    }

    public static ReasonerException nonExistentUnifier() {
        return new ReasonerException(ErrorMessage.NON_EXISTENT_UNIFIER.getMessage());
    }

    public static ReasonerException illegalAtomConversion(Atomic atom, Class<?> targetType) {
        return new ReasonerException(ErrorMessage.ILLEGAL_ATOM_CONVERSION.getMessage(atom, targetType));
    }

    public static ReasonerException valuePredicateAtomWithMultiplePredicates() {
        return new ReasonerException("Attempting creation of ValuePredicate atom with more than single predicate");
    }

    public static ReasonerException getUnifierOfNonAtomicQuery() {
        return new ReasonerException("Attempted to obtain unifiers on non-atomic queries.");
    }

    public static ReasonerException invalidQueryCacheEntry(ReasonerQuery query, ConceptMap answer) {
        return new ReasonerException(ErrorMessage.INVALID_CACHE_ENTRY.getMessage(query.toString(), answer.toString()));
    }

    public static ReasonerException nonRoleIdAssignedToRoleVariable(Statement var) {
        return new ReasonerException(ErrorMessage.ROLE_ID_IS_NOT_ROLE.getMessage(var.toString()));
    }

    public static ReasonerException invalidVariablePredicateState(Atomic vp, ConceptMap ans){
        return new ReasonerException(ErrorMessage.INVALID_VARIABLE_PREDICATE_STATE.getMessage(vp.toString(), ans.toString()));
    }
}
