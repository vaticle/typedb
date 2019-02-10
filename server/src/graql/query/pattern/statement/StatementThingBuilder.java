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

package grakn.core.graql.query.pattern.statement;

import grakn.core.graql.query.pattern.property.IdProperty;
import grakn.core.graql.query.pattern.property.NeqProperty;
import grakn.core.graql.query.pattern.property.VarProperty;

import javax.annotation.CheckReturnValue;

interface StatementThingBuilder {

    /**
     * @param id a ConceptId that this variable's ID must match
     * @return this
     */
    @CheckReturnValue
    default StatementInstance.StatementThing id(String id) {
        return statementThing(new IdProperty(id));
    }

    /**
     * Specify that the variable is different to another variable
     *
     * @param var the variable that this variable should not be equal to
     * @return this
     */
    @CheckReturnValue
    default StatementInstance.StatementThing not(String var) {
        return not(new Variable(var));
    }

    /**
     * Specify that the variable is different to another variable
     *
     * @param var the variable pattern that this variable should not be equal to
     * @return this
     */
    @CheckReturnValue
    default StatementInstance.StatementThing not(Variable var) {
        return not(new NeqProperty(new Statement(var)));
    }

    /**
     * Specify that the variable is different to another variable
     *
     * @param property the NEQ property containing variable pattern that this variable should not be equal to
     * @return this
     */
    @CheckReturnValue
    default StatementInstance.StatementThing not(NeqProperty property) {
        return statementThing(property);
    }

    @Deprecated         // This method should not be used publicly
    @CheckReturnValue   // TODO: will be made "private" once we upgrade to Java 9
    StatementInstance.StatementThing statementThing(VarProperty property);
}
