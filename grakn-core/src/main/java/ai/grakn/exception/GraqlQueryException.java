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

package ai.grakn.exception;

import ai.grakn.concept.AttributeType;
import ai.grakn.concept.Concept;
import ai.grakn.concept.ConceptId;
import ai.grakn.concept.Label;
import ai.grakn.concept.SchemaConcept;
import ai.grakn.concept.Type;
import ai.grakn.graql.Var;
import ai.grakn.graql.VarPattern;
import ai.grakn.graql.admin.Atomic;
import ai.grakn.graql.admin.ReasonerQuery;
import ai.grakn.graql.admin.UniqueVarProperty;
import ai.grakn.graql.admin.VarPatternAdmin;
import ai.grakn.graql.macro.Macro;
import ai.grakn.util.ErrorMessage;

import java.time.format.DateTimeParseException;
import java.util.Collection;
import java.util.List;

import static ai.grakn.util.ErrorMessage.INSERT_ABSTRACT_NOT_TYPE;
import static ai.grakn.util.ErrorMessage.INSERT_RECURSIVE;
import static ai.grakn.util.ErrorMessage.INSERT_UNDEFINED_VARIABLE;
import static ai.grakn.util.ErrorMessage.INVALID_COMPUTE_ARGUMENT;
import static ai.grakn.util.ErrorMessage.INVALID_COMPUTE_CONDITION;
import static ai.grakn.util.ErrorMessage.INVALID_COMPUTE_METHOD;
import static ai.grakn.util.ErrorMessage.INVALID_COMPUTE_METHOD_ALGORITHM;
import static ai.grakn.util.ErrorMessage.INVALID_VALUE;
import static ai.grakn.util.ErrorMessage.MISSING_COMPUTE_CONDITION;
import static ai.grakn.util.ErrorMessage.NEGATIVE_OFFSET;
import static ai.grakn.util.ErrorMessage.NON_POSITIVE_LIMIT;
import static ai.grakn.util.ErrorMessage.UNEXPECTED_RESULT;
import static ai.grakn.util.ErrorMessage.VARIABLE_NOT_IN_QUERY;
import static ai.grakn.util.GraqlSyntax.Compute;
import static ai.grakn.util.GraqlSyntax.Compute.ALGORITHMS_ACCEPTED;
import static ai.grakn.util.GraqlSyntax.Compute.ARGUMENTS_ACCEPTED;
import static ai.grakn.util.GraqlSyntax.Compute.CONDITIONS_ACCEPTED;
import static ai.grakn.util.GraqlSyntax.Compute.CONDITIONS_REQUIRED;
import static ai.grakn.util.GraqlSyntax.Compute.METHODS_ACCEPTED;

/**
 * <p>
 * Graql Query Exception
 * </p>
 * <p>
 * Occurs when the query is syntactically correct but semantically incorrect.
 * For example limiting the results of a query -1
 * </p>
 *
 * @author fppt
 */
public class GraqlQueryException extends GraknException {

    private final String NAME = "GraqlQueryException";

    private GraqlQueryException(String error) {
        super(error);
    }

    private GraqlQueryException(String error, Exception cause) {
        super(error, cause);
    }

    @Override
    public String getName() {
        return NAME;
    }

    public static GraqlQueryException create(String formatString, Object... args) {
        return new GraqlQueryException(String.format(formatString, args));
    }

    public static GraqlQueryException noPatterns() {
        return new GraqlQueryException(ErrorMessage.NO_PATTERNS.getMessage());
    }

    public static GraqlQueryException incorrectAggregateArgumentNumber(
            String name, int minArgs, int maxArgs, List<Object> args) {
        String expectedArgs = (minArgs == maxArgs) ? Integer.toString(minArgs) : minArgs + "-" + maxArgs;
        String message = ErrorMessage.AGGREGATE_ARGUMENT_NUM.getMessage(name, expectedArgs, args.size());
        return new GraqlQueryException(message);
    }

    public static GraqlQueryException conflictingProperties(
            VarPatternAdmin varPattern, UniqueVarProperty property, UniqueVarProperty other) {
        String message = ErrorMessage.CONFLICTING_PROPERTIES.getMessage(
                varPattern.getPrintableName(), property.graqlString(), other.graqlString()
        );
        return new GraqlQueryException(message);
    }

    public static GraqlQueryException idNotFound(ConceptId id) {
        return new GraqlQueryException(ErrorMessage.ID_NOT_FOUND.getMessage(id));
    }

    public static GraqlQueryException labelNotFound(Label label) {
        return new GraqlQueryException(ErrorMessage.LABEL_NOT_FOUND.getMessage(label));
    }

    public static GraqlQueryException kCoreOnRelationshipType(Label label) {
        return create("cannot compute coreness of relationship type %s.", label.getValue());
    }

    public static GraqlQueryException deleteSchemaConcept(SchemaConcept schemaConcept) {
        return create("cannot delete schema concept %s. Use `undefine` instead.", schemaConcept);
    }

    public static GraqlQueryException insertUnsupportedProperty(String propertyName) {
        return GraqlQueryException.create("inserting property '%s' is not supported, try `define`", propertyName);
    }

    public static GraqlQueryException defineUnsupportedProperty(String propertyName) {
        return GraqlQueryException.create("defining property '%s' is not supported, try `insert`", propertyName);
    }

    public static GraqlQueryException mustBeAttributeType(Label attributeType) {
        return new GraqlQueryException(ErrorMessage.MUST_BE_ATTRIBUTE_TYPE.getMessage(attributeType));
    }

    public static GraqlQueryException cannotGetInstancesOfNonType(Label label) {
        return GraqlQueryException.create("%s is not a type and so does not have instances", label);
    }

    public static GraqlQueryException notARelationType(Label label) {
        return new GraqlQueryException(ErrorMessage.NOT_A_RELATION_TYPE.getMessage(label));
    }

    public static GraqlQueryException notARoleType(Label roleId) {
        return new GraqlQueryException(ErrorMessage.NOT_A_ROLE_TYPE.getMessage(roleId, roleId));
    }

    public static GraqlQueryException insertPredicate() {
        return new GraqlQueryException(ErrorMessage.INSERT_PREDICATE.getMessage());
    }

    public static GraqlQueryException insertRecursive(VarPatternAdmin var) {
        return new GraqlQueryException(INSERT_RECURSIVE.getMessage(var.getPrintableName()));
    }

    public static GraqlQueryException insertUndefinedVariable(VarPatternAdmin var) {
        return new GraqlQueryException(INSERT_UNDEFINED_VARIABLE.getMessage(var.getPrintableName()));
    }

    public static GraqlQueryException createInstanceOfMetaConcept(Var var, Type type) {
        return new GraqlQueryException(var + " cannot be an instance of meta-type " + type.label());
    }

    public static GraqlQueryException insertMetaType(Label label, SchemaConcept schemaConcept) {
        return new GraqlQueryException(ErrorMessage.INSERT_METATYPE.getMessage(label, schemaConcept.label()));
    }

    /**
     * Thrown when a concept is inserted with multiple properties when it can only have one.
     * <p>
     * For example: {@code insert $x isa movie; $x isa person;}
     * </p>
     */
    public static GraqlQueryException insertMultipleProperties(
            VarPattern varPattern, String property, Object value1, Object value2
    ) {
        String message = "a concept `%s` cannot have multiple properties `%s` and `%s` for `%s`";
        return create(message, varPattern, value1, value2, property);
    }

    /**
     * Thrown when a property is inserted on a concept that already exists and that property can't be overridden.
     * <p>
     * For example: {@code match $x isa name; insert $x val "Bob";}
     * </p>
     */
    public static GraqlQueryException insertPropertyOnExistingConcept(String property, Object value, Concept concept) {
        return create("cannot insert property `%s %s` on existing concept `%s`", property, value, concept);
    }

    /**
     * Thrown when a property is inserted on a concept that doesn't support that property.
     * <p>
     * For example, an entity with a value: {@code insert $x isa movie, val "The Godfather";}
     * </p>
     */
    public static GraqlQueryException insertUnexpectedProperty(String property, Object value, Concept concept) {
        return create("unexpected property `%s %s` for concept `%s`", property, value, concept);
    }

    /**
     * Thrown when a concept does not have all expected properties required to insert it.
     * <p>
     * For example, an attribute without a value: {@code insert $x isa name;}
     * </p>
     */
    public static GraqlQueryException insertNoExpectedProperty(String property, VarPatternAdmin var) {
        return create("missing expected property `%s` in `%s`", property, var);
    }

    /**
     * Thrown when attempting to insert a concept that already exists.
     * <p>
     * For example: {@code match $x isa movie; insert $x isa name, val "Bob";}
     * </p>
     */
    public static GraqlQueryException insertExistingConcept(VarPatternAdmin pattern, Concept concept) {
        return create("cannot overwrite properties `%s` on  concept `%s`", pattern, concept);
    }

    public static GraqlQueryException varNotInQuery(Var var) {
        return new GraqlQueryException(VARIABLE_NOT_IN_QUERY.getMessage(var));
    }

    public static GraqlQueryException noTx() {
        return new GraqlQueryException(ErrorMessage.NO_TX.getMessage());
    }

    public static GraqlQueryException multipleTxs() {
        return new GraqlQueryException(ErrorMessage.MULTIPLE_TX.getMessage());
    }

    public static GraqlQueryException nonPositiveLimit(long limit) {
        return new GraqlQueryException(NON_POSITIVE_LIMIT.getMessage(limit));
    }

    public static GraqlQueryException negativeOffset(long offset) {
        return new GraqlQueryException(NEGATIVE_OFFSET.getMessage(offset));
    }

    public static GraqlQueryException invalidValueClass(Object value) {
        return new GraqlQueryException(INVALID_VALUE.getMessage(value.getClass()));
    }

    public static GraqlQueryException wrongNumberOfMacroArguments(Macro macro, List<Object> values) {
        return new GraqlQueryException("Wrong number of arguments [" + values.size() + "] to macro " + macro.name());
    }

    public static GraqlQueryException wrongMacroArgumentType(Macro macro, String value) {
        return new GraqlQueryException("Value [" + value + "] is not a " + macro.name() + " needed for this macro");
    }

    public static GraqlQueryException unknownAggregate(String name) {
        return new GraqlQueryException(ErrorMessage.UNKNOWN_AGGREGATE.getMessage(name));
    }

    public static GraqlQueryException maxIterationsReached(Class<?> clazz) {
        return new GraqlQueryException(ErrorMessage.MAX_ITERATION_REACHED
                .getMessage(clazz.toString()));
    }

    public static GraqlQueryException statisticsAttributeTypesNotSpecified() {
        return new GraqlQueryException(ErrorMessage.ATTRIBUTE_TYPE_NOT_SPECIFIED.getMessage());
    }

    public static GraqlQueryException instanceDoesNotExist() {
        return new GraqlQueryException(ErrorMessage.INSTANCE_DOES_NOT_EXIST.getMessage());
    }

    public static GraqlQueryException kValueSmallerThanTwo() {
        return new GraqlQueryException(ErrorMessage.K_SMALLER_THAN_TWO.getMessage());
    }

    public static GraqlQueryException attributeMustBeANumber(AttributeType.DataType dataType, Label attributeType) {
        return new GraqlQueryException(attributeType + " must have data type of `long` or `double`, but was " + dataType.getName());
    }

    public static GraqlQueryException attributesWithDifferentDataTypes(Collection<? extends Label> attributeTypes) {
        return new GraqlQueryException("resource types " + attributeTypes + " have different data types");
    }

    public static GraqlQueryException unificationAtomIncompatibility() {
        return new GraqlQueryException(ErrorMessage.UNIFICATION_ATOM_INCOMPATIBILITY.getMessage());
    }

    public static GraqlQueryException nonAtomicQuery(ReasonerQuery query) {
        return new GraqlQueryException(ErrorMessage.NON_ATOMIC_QUERY.getMessage(query));
    }

    public static GraqlQueryException nonGroundNeqPredicate(ReasonerQuery query) {
        return new GraqlQueryException(ErrorMessage.NON_GROUND_NEQ_PREDICATE.getMessage(query));
    }

    public static GraqlQueryException incompleteResolutionPlan(ReasonerQuery reasonerQuery) {
        return new GraqlQueryException(ErrorMessage.INCOMPLETE_RESOLUTION_PLAN.getMessage(reasonerQuery));
    }

    public static GraqlQueryException rolePatternAbsent(Atomic relation) {
        return new GraqlQueryException(ErrorMessage.ROLE_PATTERN_ABSENT.getMessage(relation));
    }

    public static GraqlQueryException nonExistentUnifier() {
        return new GraqlQueryException(ErrorMessage.NON_EXISTENT_UNIFIER.getMessage());
    }

    public static GraqlQueryException illegalAtomConversion(Atomic atom) {
        return new GraqlQueryException(ErrorMessage.ILLEGAL_ATOM_CONVERSION.getMessage(atom));
    }

    public static GraqlQueryException valuePredicateAtomWithMultiplePredicates() {
        return new GraqlQueryException("Attempting creation of ValuePredicate atom with more than single predicate");
    }

    public static GraqlQueryException getUnifierOfNonAtomicQuery() {
        return new GraqlQueryException("Attempted to obtain unifiers on non-atomic queries.");
    }

    public static GraqlQueryException invalidQueryCacheEntry(ReasonerQuery query) {
        return new GraqlQueryException(ErrorMessage.INVALID_CACHE_ENTRY.getMessage(query.toString()));
    }

    public static GraqlQueryException noAtomsSelected(ReasonerQuery query) {
        return new GraqlQueryException(ErrorMessage.NO_ATOMS_SELECTED.getMessage(query.toString()));
    }

    public static GraqlQueryException conceptNotAThing(Object value) {
        return new GraqlQueryException(ErrorMessage.CONCEPT_NOT_THING.getMessage(value));
    }

    public static GraqlQueryException nonRoleIdAssignedToRoleVariable(VarPatternAdmin var) {
        return new GraqlQueryException(ErrorMessage.ROLE_ID_IS_NOT_ROLE.getMessage(var.toString()));
    }

    public static GraqlQueryException cannotParseDateFormat(String originalFormat) {
        return new GraqlQueryException("Cannot parse date format " + originalFormat + ". See DateTimeFormatter#ofPattern");
    }

    public static GraqlQueryException cannotParseDateString(String originalDate, String originalFormat, DateTimeParseException cause) {
        throw new GraqlQueryException("Cannot parse date value " + originalDate + " with format " + originalFormat, cause);
    }

    public static GraqlQueryException noLabelSpecifiedForHas(VarPattern varPattern) {
        return create("'has' argument '%s' requires a label", varPattern);
    }

    public static GraqlQueryException insertRolePlayerWithoutRoleType() {
        return new GraqlQueryException(ErrorMessage.INSERT_RELATION_WITHOUT_ROLE_TYPE.getMessage());
    }

    public static GraqlQueryException insertAbstractOnNonType(SchemaConcept concept) {
        return new GraqlQueryException(INSERT_ABSTRACT_NOT_TYPE.getMessage(concept.label()));
    }

    public static GraqlQueryException unexpectedResult(Var var) {
        return new GraqlQueryException(UNEXPECTED_RESULT.getMessage(var.getValue()));
    }

    public static GraqlQueryException invalidComputeQuery_invalidMethod() {
        return new GraqlQueryException(INVALID_COMPUTE_METHOD.getMessage(METHODS_ACCEPTED));
    }

    public static GraqlQueryException invalidComputeQuery_invalidCondition(Compute.Method method) {
        return new GraqlQueryException(INVALID_COMPUTE_CONDITION.getMessage(method, CONDITIONS_ACCEPTED.get(method)));
    }

    public static GraqlQueryException invalidComputeQuery_missingCondition(Compute.Method method) {
        return new GraqlQueryException(MISSING_COMPUTE_CONDITION.getMessage(method, CONDITIONS_REQUIRED.get(method)));
    }

    public static GraqlQueryException invalidComputeQuery_invalidMethodAlgorithm(Compute.Method method) {
        return new GraqlQueryException(INVALID_COMPUTE_METHOD_ALGORITHM.getMessage(method, ALGORITHMS_ACCEPTED.get(method)));
    }

    public static GraqlQueryException invalidComputeQuery_invalidArgument(Compute.Method method, Compute.Algorithm algorithm) {
        return new GraqlQueryException(INVALID_COMPUTE_ARGUMENT.getMessage(method, algorithm, ARGUMENTS_ACCEPTED.get(method).get(algorithm)));
    }
}
