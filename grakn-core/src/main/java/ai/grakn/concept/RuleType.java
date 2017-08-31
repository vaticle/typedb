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

package ai.grakn.concept;

import ai.grakn.graql.Pattern;

import javax.annotation.CheckReturnValue;
import javax.annotation.Nonnull;
import java.util.stream.Stream;

/**
 * <p>
 *     An ontological element used to model and categorise different types of {@link Rule}.
 * </p>
 *
 * <p>
 *     An ontological element used to define different types of {@link Rule}.
 * </p>
 *
 * @author fppt
 */
public interface RuleType extends Type {
    //------------------------------------- Accessors ----------------------------------
    /**
     * Retrieves the Left Hand Side of the rule.
     * When this query is satisfied the "then" part of the rule is executed.
     *
     * @return A string representing the left hand side Graql query.
     */
    @CheckReturnValue
    Pattern getWhen();

    /**
     * Retrieves the Right Hand Side of the rule.
     * This query is executed when the "when" part of the rule is satisfied
     *
     * @return A string representing the right hand side Graql query.
     */
    @CheckReturnValue
    Pattern getThen();

    /**
     * Retrieve a set of Types that constitute a part of the hypothesis of this Rule.
     *
     * @return A collection of Concept Types that constitute a part of the hypothesis of the Rule
     */
    @CheckReturnValue
    Stream<Type> getHypothesisTypes();

    /**
     * Retrieve a set of Types that constitue a part of the conclusion of the Rule.
     *
     * @return A collection of Concept Types that constitute a part of the conclusion of the Rule
     */
    @CheckReturnValue
    Stream<Type> getConclusionTypes();

    //------------------------------------- Modifiers ----------------------------------
    /**
     * Changes the {@link Label} of this {@link Concept} to a new one.
     * @param label The new {@link Label}.
     * @return The {@link Concept} itself
     */
    RuleType setLabel(Label label);

    /**
     * Creates a {@link RelationshipType} which allows this type and a resource type to be linked in a strictly one-to-one mapping.
     *
     * @param attributeType The resource type which instances of this type should be allowed to play.
     * @return The Type itself.
     */
    @Override
    RuleType key(AttributeType attributeType);

    /**
     * Creates a {@link RelationshipType} which allows this type and a resource type to be linked.
     *
     * @param attributeType The resource type which instances of this type should be allowed to play.
     * @return The Type itself.
     */
    @Override
    RuleType attribute(AttributeType attributeType);

    //---- Inherited Methods
    /**
     *
     * @param isAbstract  Specifies if the concept is abstract (true) or not (false).
     *                    If the concept type is abstract it is not allowed to have any instances.
     * @return The Rule Type itself
     */
    @Override
    RuleType setAbstract(Boolean isAbstract);

    /**
     *
     * @return The super type of this Rule Type
     */
    @Override
    @Nonnull
    RuleType sup();

    /**
     *
     * @param type The super type of this Rule Type
     * @return The Rule Type itself
     */
    RuleType sup(RuleType type);

    /**
     * Adds another subtype to this type
     *
     * @param type The sub type of this rule type
     * @return The RuleType itself
     */
    RuleType sub(RuleType type);

    /**
     *
     * @return All the sub types of this rule type
     */
    @Override
    Stream<RuleType> subs();

    /**
     *
     * @param role The Role Type which the instances of this Type are allowed to play.
     * @return The Rule Type itself
     */
    @Override
    RuleType plays(Role role);

    /**
     * Removes the ability of this {@link RuleType} to play a specific {@link Role}
     *
     * @param role The {@link Role} which the {@link Thing}s of this {@link RuleType} should no longer be allowed to play.
     * @return The {@link RuleType} itself.
     */
    @Override
    RuleType deletePlays(Role role);

    /**
     * Removes the ability for {@link Thing}s of this {@link RuleType} to have {@link Attribute}s of type {@link AttributeType}
     *
     * @param attributeType the {@link AttributeType} which this {@link RuleType} can no longer have
     * @return The {@link RuleType} itself.
     */
    @Override
    RuleType deleteAttribute(AttributeType attributeType);

    /**
     * Removes {@link AttributeType} as a key to this {@link RuleType}
     *
     * @param attributeType the {@link AttributeType} which this {@link RuleType} can no longer have as a key
     * @return The {@link RuleType} itself.
     */
    @Override
    RuleType deleteKey(AttributeType attributeType);

    /**
     *
     * @return All the rule instances of this Rule Type.
     */
    @Override
    Stream<Rule> instances();

    //------------------------------------- Other ---------------------------------
    @Deprecated
    @CheckReturnValue
    @Override
    default RuleType asRuleType(){
        return this;
    }

    @Deprecated
    @CheckReturnValue
    @Override
    default boolean isRuleType(){
        return true;
    }
}
