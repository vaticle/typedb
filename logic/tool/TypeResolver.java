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

package grakn.core.logic.tool;

import grakn.common.collection.Bytes;
import grakn.core.common.exception.GraknException;
import grakn.core.common.parameters.Label;
import grakn.core.concept.ConceptManager;
import grakn.core.graph.util.Encoding;
import grakn.core.graph.vertex.TypeVertex;
import grakn.core.logic.LogicCache;
import grakn.core.pattern.Conjunction;
import grakn.core.pattern.constraint.thing.HasConstraint;
import grakn.core.pattern.constraint.thing.IIDConstraint;
import grakn.core.pattern.constraint.thing.IsConstraint;
import grakn.core.pattern.constraint.thing.IsaConstraint;
import grakn.core.pattern.constraint.thing.RelationConstraint;
import grakn.core.pattern.constraint.thing.ValueConstraint;
import grakn.core.pattern.variable.SystemReference;
import grakn.core.pattern.variable.ThingVariable;
import grakn.core.pattern.variable.TypeVariable;
import grakn.core.pattern.variable.Variable;
import grakn.core.traversal.Traversal;
import grakn.core.traversal.TraversalEngine;
import grakn.core.traversal.common.Identifier;
import graql.lang.common.GraqlArg.ValueType;
import graql.lang.pattern.variable.Reference;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static grakn.common.collection.Collections.set;
import static grakn.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static grakn.core.common.exception.ErrorMessage.Pattern.SCHEMATICALLY_UNSATISFIABLE_CONJUNCTION;
import static grakn.core.common.exception.ErrorMessage.ThingRead.THING_NOT_FOUND;
import static grakn.core.common.exception.ErrorMessage.TypeRead.ROLE_TYPE_NOT_FOUND;
import static grakn.core.common.exception.ErrorMessage.TypeRead.TYPE_NOT_FOUND;
import static grakn.core.common.iterator.Iterators.iterate;
import static graql.lang.common.GraqlToken.Type.ATTRIBUTE;

public class TypeResolver {

    private final ConceptManager conceptMgr;
    private final TraversalEngine traversalEng;
    private final LogicCache logicCache;

    public TypeResolver(ConceptManager conceptMgr, TraversalEngine traversalEng, LogicCache logicCache) {
        this.conceptMgr = conceptMgr;
        this.traversalEng = traversalEng;
        this.logicCache = logicCache;
    }

    public Conjunction resolveLabels(Conjunction conjunction) {
        iterate(conjunction.variables()).filter(v -> v.isType() && v.asType().label().isPresent())
                .forEachRemaining(typeVar -> {
                    Label label = typeVar.asType().label().get().properLabel();
                    if (label.scope().isPresent()) {
                        String scope = label.scope().get();
                        Set<Label> labels = traversalEng.graph().schema().resolveRoleTypeLabels(label);
                        if (labels.isEmpty()) throw GraknException.of(ROLE_TYPE_NOT_FOUND, label.name(), scope);
                        typeVar.addResolvedTypes(labels);
                    } else {
                        TypeVertex type = traversalEng.graph().schema().getType(label);
                        if (type == null) throw GraknException.of(TYPE_NOT_FOUND, label);
                        typeVar.addSingleResolvedType(label);
                    }
                });
        return conjunction;
    }

    public Conjunction resolve(Conjunction conjunction) {
        resolveLabels(conjunction);
        TraversalConstructor traversalConstructor = new TraversalConstructor(conjunction, conceptMgr);

        Map<Reference, Set<Label>> resolvedLabels = executeResolverTraversals(traversalConstructor);
        if (resolvedLabels.isEmpty()) throw GraknException.of(SCHEMATICALLY_UNSATISFIABLE_CONJUNCTION, conjunction);
        resolvedLabels.forEach((ref, labels) -> traversalConstructor.getVariable(ref).setResolvedTypes(labels));
        clearResolvedTypesWhichProvideNoInfo(conjunction);

        return conjunction;
    }

    private void clearResolvedTypesWhichProvideNoInfo(Conjunction conjunction) {
        long numOfTypes = traversalEng.graph().schema().stats().thingTypeCount();
        long numOfConcreteTypes = traversalEng.graph().schema().stats().concreteThingTypeCount();
        iterate(conjunction.variables()).filter(variable -> (
                variable.isType() && variable.resolvedTypes().size() == numOfTypes ||
                        variable.isThing() && variable.resolvedTypes().size() == numOfConcreteTypes
        )).forEachRemaining(Variable::clearResolvedTypes);
    }

    private Map<Reference, Set<Label>> executeResolverTraversals(TraversalConstructor traversalConstructor) {
        return logicCache.resolver().get(traversalConstructor.resolverTraversal(), traversal -> {
            Map<Reference, Set<Label>> mapping = new HashMap<>();
            traversalEng.iterator(traversal).forEachRemaining(
                    result -> result.forEach((ref, vertex) -> {
                        mapping.putIfAbsent(ref, new HashSet<>());
                        assert vertex.isType();
                        if (!(vertex.asType().isAbstract() && traversalConstructor.getVariable(ref).isThing()))
                            mapping.get(ref).add(vertex.asType().properLabel());
                    })
            );
            return mapping;
        });
    }

    private static class TraversalConstructor {

        private final Conjunction conjunction;
        private final Map<Reference, Variable> variableRegister;
        private final Map<Identifier, TypeVariable> resolverRegister;
        private final Traversal resolverTraversal;
        private int sysVarCounter;
        private final ConceptManager conceptMgr;
        private final Map<Identifier, Set<ValueType>> valueTypeRegister;

        TraversalConstructor(Conjunction conjunction, ConceptManager conceptMgr) {
            this.conjunction = conjunction;
            this.conceptMgr = conceptMgr;
            this.resolverTraversal = new Traversal();
            this.variableRegister = new HashMap<>();
            this.resolverRegister = new HashMap<>();
            this.sysVarCounter = 0;
            this.valueTypeRegister = new HashMap<>();
            conjunction.variables().forEach(this::convert);
        }

        Traversal resolverTraversal() {
            return resolverTraversal;
        }

        Variable getVariable(Reference reference) {
            return variableRegister.get(reference);
        }

        private void convert(Variable variable) {
            if (variable.isType()) convert(variable.asType());
            else if (variable.isThing()) convert(variable.asThing());
            else throw GraknException.of(ILLEGAL_STATE);
        }

        private TypeVariable convert(TypeVariable variable) {
            if (resolverRegister.containsKey(variable.id())) return resolverRegister.get(variable.id());
            TypeVariable resolver;
            if (variable.label().isPresent() && variable.label().get().scope().isPresent()) {
                resolver = new TypeVariable(newSystemId());
                resolverTraversal.labels(resolver.id(), variable.resolvedTypes());
            } else {
                resolver = variable;
            }
            resolverRegister.put(variable.id(), resolver);
            variableRegister.putIfAbsent(resolver.reference(), variable);
            resolver.addTo(resolverTraversal);
            return resolver;
        }

        private TypeVariable convert(ThingVariable variable) {
            if (resolverRegister.containsKey(variable.id())) return resolverRegister.get(variable.id());

            TypeVariable resolver = new TypeVariable(variable.reference().isAnonymous() ?
                                                             newSystemId() : variable.id());
            resolverRegister.put(variable.id(), resolver);
            variableRegister.putIfAbsent(resolver.reference(), variable);
            valueTypeRegister.putIfAbsent(resolver.id(), set());

            // Note: order is important! convertValue assumes that any other Variable encountered from that edge will
            //have resolved its valueType, so we execute convertValue first.
            variable.value().forEach(constraint -> convertValue(resolver, constraint));
            variable.isa().ifPresent(constraint -> convertIsa(resolver, constraint));
            variable.is().forEach(constraint -> convertIs(resolver, constraint));
            variable.has().forEach(constraint -> convertHas(resolver, constraint));
            variable.relation().forEach(constraint -> convertRelation(resolver, constraint));
            variable.iid().ifPresent(constraint -> convertIID(resolver, constraint));
            return resolver;
        }

        private void convertIID(TypeVariable owner, IIDConstraint iidConstraint) {
            if (conceptMgr.getThing(iidConstraint.iid()) == null)
                throw GraknException.of(THING_NOT_FOUND, Bytes.bytesToHexString(iidConstraint.iid()));
            resolverTraversal.labels(owner.id(), conceptMgr.getThing(iidConstraint.iid()).getType().getLabel());
        }

        private void convertIsa(TypeVariable owner, IsaConstraint isaConstraint) {
            if (!isaConstraint.isExplicit())
                resolverTraversal.sub(owner.id(), convert(isaConstraint.type()).id(), true);
            else if (isaConstraint.type().reference().isName())
                resolverTraversal.equalTypes(owner.id(), convert(isaConstraint.type()).id());
            else if (isaConstraint.type().label().isPresent())
                resolverTraversal.labels(owner.id(), isaConstraint.type().label().get().properLabel());
            else throw GraknException.of(ILLEGAL_STATE);
        }

        private void convertIs(TypeVariable owner, IsConstraint isConstraint) {
            resolverTraversal.equalTypes(owner.id(), convert(isConstraint.variable()).id());
        }

        private void convertHas(TypeVariable owner, HasConstraint hasConstraint) {
            resolverTraversal.owns(owner.id(), convert(hasConstraint.attribute()).id(), false);
        }

        private void convertRelation(TypeVariable owner, RelationConstraint constraint) {
            for (RelationConstraint.RolePlayer rolePlayer : constraint.players()) {
                TypeVariable playerResolver = convert(rolePlayer.player());
                TypeVariable actingRoleResolver = convert(new TypeVariable(newSystemId()));
                if (rolePlayer.roleType().isPresent()) {
                    TypeVariable roleTypeResolver = convert(rolePlayer.roleType().get());
                    resolverTraversal.sub(actingRoleResolver.id(), roleTypeResolver.id(), true);
                }
                resolverTraversal.relates(owner.id(), actingRoleResolver.id());
                resolverTraversal.plays(playerResolver.id(), actingRoleResolver.id());
            }
        }

        private void convertValue(TypeVariable owner, ValueConstraint<?> constraint) {
            Set<ValueType> valueTypes = findComparableValueTypes(constraint);
            if (valueTypeRegister.get(owner.id()).isEmpty()) {
                valueTypes.forEach(valueType -> resolverTraversal.valueType(owner.id(), valueType));
                valueTypeRegister.put(owner.id(), valueTypes);
            } else if (!valueTypeRegister.get(owner.id()).containsAll(valueTypes)) {
                throw GraknException.of(SCHEMATICALLY_UNSATISFIABLE_CONJUNCTION, conjunction);
            }
            subAttribute(owner.id());
        }

        private Set<ValueType> findComparableValueTypes(ValueConstraint<?> constraint) {
            if (constraint.isVariable()) {
                TypeVariable comparableVar = convert(constraint.asVariable().value());
                assert valueTypeRegister.containsKey(comparableVar.id()); //This will fail without careful ordering.
                subAttribute(comparableVar.id());
                return valueTypeRegister.get(comparableVar.id());
            }
            return iterate(Encoding.ValueType.of(constraint.value().getClass()).comparables())
                    .map(Encoding.ValueType::graqlValueType).toSet();
        }

        private void subAttribute(Identifier.Variable variable) {
            Identifier.Variable attributeID = Identifier.Variable.of(Reference.label(ATTRIBUTE.toString()));
            resolverTraversal.labels(attributeID, Label.of(ATTRIBUTE.toString()));
            resolverTraversal.sub(variable, attributeID, true);
        }

        private Identifier.Variable newSystemId() {
            return Identifier.Variable.of(SystemReference.of(sysVarCounter++));
        }

    }
}
