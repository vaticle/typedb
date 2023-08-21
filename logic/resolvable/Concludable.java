/*
 * Copyright (C) 2022 Vaticle
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

package com.vaticle.typedb.core.logic.resolvable;

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.common.iterator.Iterators;
import com.vaticle.typedb.core.common.parameters.Label;
import com.vaticle.typedb.core.concept.ConceptManager;
import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.concept.thing.Thing;
import com.vaticle.typedb.core.logic.LogicManager;
import com.vaticle.typedb.core.logic.Rule;
import com.vaticle.typedb.core.pattern.Conjunction;
import com.vaticle.typedb.core.pattern.constraint.Constraint;
import com.vaticle.typedb.core.pattern.constraint.common.Predicate;
import com.vaticle.typedb.core.pattern.constraint.thing.HasConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.IsaConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.PredicateConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.RelationConstraint;
import com.vaticle.typedb.core.pattern.constraint.thing.RelationConstraint.RolePlayer;
import com.vaticle.typedb.core.pattern.constraint.thing.ThingConstraint;
import com.vaticle.typedb.core.pattern.constraint.type.LabelConstraint;
import com.vaticle.typedb.core.pattern.equivalence.AlphaEquivalence;
import com.vaticle.typedb.core.pattern.equivalence.AlphaEquivalent;
import com.vaticle.typedb.core.pattern.variable.ThingVariable;
import com.vaticle.typedb.core.pattern.variable.TypeVariable;
import com.vaticle.typedb.core.pattern.variable.Variable;
import com.vaticle.typedb.core.traversal.common.Identifier;
import com.vaticle.typedb.core.traversal.common.Identifier.Variable.Retrievable;
import com.vaticle.typeql.lang.common.TypeQLToken;
import com.vaticle.typeql.lang.pattern.variable.Reference;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.vaticle.typedb.common.collection.Collections.concatToSet;
import static com.vaticle.typedb.common.collection.Collections.list;
import static com.vaticle.typedb.common.collection.Collections.set;
import static com.vaticle.typedb.common.util.Objects.className;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Pattern.INVALID_CASTING;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;
import static com.vaticle.typedb.core.common.iterator.Iterators.single;
import static java.util.stream.Collectors.toSet;

public abstract class Concludable extends Resolvable<Conjunction> implements AlphaEquivalent<Concludable> {

    private final Set<Retrievable> retrievableIds;

    private Concludable(Conjunction conjunction) {
        super(conjunction);
        this.retrievableIds = pattern().retrieves();
    }

    public static Set<Concludable> create(com.vaticle.typedb.core.pattern.Conjunction conjunction) {
        return new Extractor(conjunction).concludables();
    }

    @Override
    public Set<Retrievable> retrieves() {
        return retrievableIds;
    }

    @Override
    public Set<Variable> variables() {
        return pattern().variables();
    }

    public abstract ThingVariable generatingVariable();

    public boolean isConcludable() {
        return true;
    }

    public Concludable asConcludable() {
        return this;
    }

    public abstract Set<Constraint> concludableConstraints();

    public abstract Map<Rule, Set<Unifier>> computeApplicableRules(ConceptManager conceptMgr, LogicManager logicMgr);

    public abstract FunctionalIterator<Unifier> unify(Rule.Conclusion conclusion, ConceptManager conceptMgr);

    public abstract boolean isInferredAnswer(ConceptMap conceptMap);

    public boolean isRelation() {
        return false;
    }

    public boolean isHas() {
        return false;
    }

    public boolean isIsa() {
        return false;
    }

    public boolean isAttribute() {
        return false;
    }

    public Relation asRelation() {
        throw TypeDBException.of(INVALID_CASTING, className(this.getClass()), className(Relation.class));
    }

    public Has asHas() {
        throw TypeDBException.of(INVALID_CASTING, className(this.getClass()), className(Has.class));
    }

    public Isa asIsa() {
        throw TypeDBException.of(INVALID_CASTING, className(this.getClass()), className(Isa.class));
    }

    public Attribute asAttribute() {
        throw TypeDBException.of(INVALID_CASTING, className(this.getClass()), className(Attribute.class));
    }

    static <T, V> Map<T, Set<V>> cloneMapping(Map<T, Set<V>> mapping) {
        Map<T, Set<V>> clone = new HashMap<>();
        mapping.forEach((key, set) -> clone.put(key, new HashSet<>(set)));
        return clone;
    }

    private static FunctionalIterator<AlphaEquivalence> alphaEqualPredicateConstraints(Set<PredicateConstraint> set1,
                                                                                       Set<PredicateConstraint> set2) {
        if (set1.size() != set2.size()) return Iterators.empty();
        else {
            Set<PredicateConstraint> remaining = new HashSet<>(set2);
            for (PredicateConstraint s1 : set1) {
                boolean found = false;
                for (PredicateConstraint r : remaining) {
                    if (s1.alphaEquals(r).first().isPresent()) {
                        remaining.remove(r);
                        found = true;
                        break;
                    }
                }
                if (!found) return Iterators.empty();
            }
            return Iterators.single(AlphaEquivalence.empty());
        }
    }

    Map<Rule, Set<Unifier>> applicableRules(Set<Label> types, ConceptManager conceptMgr, LogicManager logicMgr) {
        assert !types.isEmpty();
        Map<Rule, Set<Unifier>> applicableRules = new HashMap<>();
        types.forEach(type -> logicMgr.rulesConcluding(type)
                .forEachRemaining(rule -> unify(rule.conclusion(), conceptMgr)
                        .forEachRemaining(unifier -> {
                            applicableRules.putIfAbsent(rule, new HashSet<>());
                            applicableRules.get(rule).add(unifier);
                        })));

        return applicableRules;
    }

    /**
     * Relation handles these concludable patterns, where `$role` and `$relation` could be labelled, and there could
     * be any number of rolePlayers:
     * { $r($role: $x) isa $relation; }
     * { $r($role: $x); }
     * { $r($x) isa $relation; }
     * { $r($x); }
     * { ($role: $x) isa $relation; }
     * { ($x) isa $relation; }
     * { ($x); }
     */
    public static class Relation extends Concludable {

        private final RelationConstraint relation;
        private final IsaConstraint isa;
        private final Set<LabelConstraint> labels;
        private final Set<Variable> generating;

        private Relation(Conjunction conjunction, RelationConstraint relation, @Nullable IsaConstraint isa, Set<LabelConstraint> labels) {
            super(conjunction);
            this.relation = relation;
            this.isa = isa;
            this.labels = labels;
            this.generating = set(generatingVariable());
        }

        public static Relation of(RelationConstraint relation, @Nullable IsaConstraint isa, Set<LabelConstraint> labels) {
            Conjunction.ConstraintCloner cloner;
            IsaConstraint clonedIsa;
            if (isa == null) {
                cloner = Conjunction.ConstraintCloner.cloneExactly(labels, relation);
                clonedIsa = null;
            } else {
                cloner = Conjunction.ConstraintCloner.cloneExactly(labels, isa, relation);
                clonedIsa = cloner.getClone(isa).asThing().asIsa();
            }
            return new Relation(cloner.conjunction(), cloner.getClone(relation).asThing().asRelation(), clonedIsa,
                    iterate(labels).map(l -> cloner.getClone(l).asType().asLabel()).toSet());
        }

        public RelationConstraint relation() {
            return relation;
        }

        public Optional<IsaConstraint> isa() {
            return Optional.ofNullable(isa);
        }

        @Override
        public Set<Constraint> concludableConstraints() {
            Set<Constraint> c = new HashSet<>(labels);
            c.add(relation);
            if (isa != null) c.add(isa);
            return set(c);
        }

        @Override
        public FunctionalIterator<Unifier> unify(Rule.Conclusion conclusion, ConceptManager conceptMgr) {
            if (conclusion.isRelation()) return unify(conclusion.asRelation(), conceptMgr);
            return Iterators.empty();
        }

        @Override
        public boolean isInferredAnswer(ConceptMap conceptMap) {
            return conceptMap.get(relation.owner().id()).asThing().isInferred();
        }

        @Override
        public ThingVariable generatingVariable() {
            return relation.owner();
        }

        @Override
        public Set<Variable> generating() {
            return generating;
        }

        public FunctionalIterator<Unifier> unify(Rule.Conclusion.Relation relationConclusion, ConceptManager conceptMgr) {
            if (relation().players().size() > relationConclusion.relation().players().size()) return Iterators.empty();

            Unifier.Builder unifierBuilder = Unifier.builder();
            ThingVariable relVar = relation().owner();
            ThingVariable unifiedRelVar = relationConclusion.relation().owner();
            if (Unifier.Builder.unificationSatisfiable(relVar, unifiedRelVar)) {
                unifierBuilder.addThing(relVar, unifiedRelVar.id());
            } else return Iterators.empty();

            if (relVar.isa().isPresent()) {
                if (relVar.isa().get().type().id().isLabel()) {
                    // require the unification target type variable satisfies a set of labels
                    Set<Label> allowedTypes = iterate(relVar.isa().get().type().inferredTypes()).flatMap(label -> Unifier.Builder.subtypeLabels(label, conceptMgr)).toSet();
                    assert allowedTypes.containsAll(relVar.inferredTypes())
                            && Unifier.Builder.unificationSatisfiable(relVar.isa().get().type(), unifiedRelVar.isa().get().type(), conceptMgr);
                    unifierBuilder.addLabelType(relVar.isa().get().type().id().asLabel(), allowedTypes, unifiedRelVar.isa().get().type().id());
                } else {
                    unifierBuilder.addVariableType(relVar.isa().get().type(), unifiedRelVar.isa().get().type().id());
                }
            }

            Set<RolePlayer> conjRolePlayers = relation().players();
            Set<RolePlayer> thenRolePlayers = relationConclusion.relation().players();

            return matchRolePlayers(conjRolePlayers, thenRolePlayers, conceptMgr)
                    .map(mapping -> convertRPMappingToUnifier(mapping, unifierBuilder.clone(), conceptMgr)).distinct();
        }

        private FunctionalIterator<Map<RolePlayer, RolePlayer>> matchRolePlayers(Set<RolePlayer> conjRolePlayerSet, Set<RolePlayer> thenRolePlayers, ConceptManager conceptMgr) {
            // If this is ever slow again, consider Divide & Conquer: Partition conjRolePlayers such that the result sets of all partitions are disjoint
            // Sort, So that the once with identical role-labels are together; They hopefully fail together
            List<RolePlayer> conjRolePlayers = new ArrayList<>(conjRolePlayerSet);
            conjRolePlayers.sort(Comparator.comparing(rolePlayer -> rolePlayer.roleType().map(typeVariable -> typeVariable.label().map(LabelConstraint::label).orElse("")).orElse("")));
            Map<RolePlayer, Set<RolePlayer>> unifiesWith = new HashMap<>();
            iterate(conjRolePlayers).forEachRemaining(conjRP -> {
                unifiesWith.put(conjRP, iterate(thenRolePlayers).filter(thenRP -> Unifier.Builder.unificationSatisfiable(conjRP, thenRP, conceptMgr)).toSet());
            });
            FunctionalIterator<Map<RolePlayer, RolePlayer>> it = Iterators.single(new HashMap<>());
            for (int i = 0; i < conjRolePlayers.size(); i++) {
                RolePlayer conjRP = conjRolePlayers.get(i);
                it = it.flatMap(currentMapping -> iterate(unifiesWith.get(conjRP))
                        .filter(thenRP -> !currentMapping.values().contains(thenRP))
                        .map(thenRP -> {
                            Map<RolePlayer, RolePlayer> clonedMapping = new HashMap<>(currentMapping);
                            clonedMapping.put(conjRP, thenRP);
                            return clonedMapping;
                        }));
            }
            return it;
        }

        private Unifier convertRPMappingToUnifier(Map<RolePlayer, RolePlayer> mapping,
                                                  Unifier.Builder unifierBuilder, ConceptManager conceptMgr) {
            mapping.forEach((conjRP, thenRP) -> {
                unifierBuilder.addThing(conjRP.player(), thenRP.player().id());
                if (conjRP.roleType().isPresent()) {
                    assert thenRP.roleType().isPresent();
                    TypeVariable conjRoleType = conjRP.roleType().get();
                    TypeVariable thenRoleType = thenRP.roleType().get();
                    if (conjRoleType.id().isLabel()) {
                        Set<Label> allowedTypes = iterate(conjRoleType.inferredTypes())
                                .flatMap(roleLabel -> Unifier.Builder.subtypeLabels(roleLabel, conceptMgr))
                                .toSet();
                        unifierBuilder.addLabelType(conjRoleType.id().asLabel(), allowedTypes, thenRoleType.id());
                    } else {
                        unifierBuilder.addVariableType(conjRoleType, thenRoleType.id());
                    }
                }
            });

            return unifierBuilder.build();
        }

        @Override
        public Map<Rule, Set<Unifier>> computeApplicableRules(ConceptManager conceptMgr, LogicManager logicMgr) {
            return applicableRules(generatingVariable().inferredTypes(), conceptMgr, logicMgr);
        }

        @Override
        public boolean isRelation() {
            return true;
        }

        @Override
        public Relation asRelation() {
            return this;
        }

        @Override
        public FunctionalIterator<AlphaEquivalence> alphaEquals(Concludable that) {
            return AlphaEquivalence.empty()
                    .alphaEqualIf(that.isRelation())
                    .flatMap(a -> AlphaEquivalence.alphaEquals(isa().orElse(null), that.asRelation().isa().orElse(null))
                            .flatMap(a::extendIfCompatible))
                    .flatMap(a -> relation().alphaEquals(that.asRelation().relation()).flatMap(a::extendIfCompatible));
        }
    }

    /**
     * `Has` handles these concludable patterns:
     * `{ $x has $a; }`,
     * `{ $x has age $a; }`,
     * `{ $x has age 30; }`,
     * `{ $x has $a; $a isa age; }`,
     * `{ $x has $a; $a 30 isa age; }`,
     * `{ $x has $a; $a = 30; }`
     * `{ $x has $a; $a < 30; $a >= 10; }`
     * Value constraints are included here to improve performance, with the exception of `=`, which cannot be included
     * elsewhere due to the anonymous attribute variable in examples such as `{ $x has age 30; }`. Only `=` is added as
     * a requirement on the unifier.
     */
    public static class Has extends Concludable {

        private final HasConstraint has;
        private final IsaConstraint isa;
        private final Set<PredicateConstraint> predicates;
        private final Set<Variable> generating;

        private Has(Conjunction conjunction, HasConstraint has, @Nullable IsaConstraint isa, Set<PredicateConstraint> predicates) {
            super(conjunction);
            this.has = has;
            this.isa = isa;
            this.predicates = predicates;
            this.generating = set(generatingVariable());
        }

        public static Has of(HasConstraint has, @Nullable IsaConstraint isa, Set<PredicateConstraint> predicates, Set<LabelConstraint> labels) {
            Conjunction.ConstraintCloner cloner;
            IsaConstraint clonedIsa;
            if (isa == null) {
                cloner = Conjunction.ConstraintCloner.cloneExactly(predicates, has);
                clonedIsa = null;
            } else {
                cloner = Conjunction.ConstraintCloner.cloneExactly(labels, predicates, isa, has);
                clonedIsa = cloner.getClone(isa).asThing().asIsa();
            }
            Set<PredicateConstraint> clonedPredicates = new HashSet<>();
            iterate(predicates).map(c -> cloner.getClone(c).asThing().asPredicate()).forEachRemaining(clonedPredicates::add);
            return new Has(cloner.conjunction(), cloner.getClone(has).asThing().asHas(), clonedIsa, clonedPredicates);
        }

        public ThingVariable owner() {
            return has.owner();
        }

        public ThingVariable attribute() {
            return has.attribute();
        }

        public HasConstraint has() {
            return has;
        }

        public Set<PredicateConstraint> predicates() {
            return predicates;
        }

        public Optional<IsaConstraint> isa() {
            return Optional.ofNullable(isa);
        }

        @Override
        public Set<Constraint> concludableConstraints() {
            Set<Constraint> constraints = new HashSet<>();
            constraints.add(has);
            if (isa != null) constraints.add(isa);
            constraints.addAll(Unifier.Builder.constantPredicateConstraints(predicates));
            return set(constraints);
        }

        @Override
        public FunctionalIterator<Unifier> unify(Rule.Conclusion conclusion, ConceptManager conceptMgr) {
            if (conclusion.isHas()) return unify(conclusion.asHas(), conceptMgr);
            return Iterators.empty();
        }

        @Override
        public boolean isInferredAnswer(ConceptMap conceptMap) {
            Thing owner = conceptMap.get(has.owner().id()).asThing();
            return owner.hasInferred(conceptMap.get(has.attribute().id()).asAttribute());
        }

        public FunctionalIterator<Unifier> unify(Rule.Conclusion.Has hasConclusion, ConceptManager conceptMgr) {
            Unifier.Builder unifierBuilder = Unifier.builder();
            ThingVariable owner = has().owner();
            ThingVariable unifiedOwner = hasConclusion.owner();
            if (Unifier.Builder.unificationSatisfiable(owner, unifiedOwner)) {
                unifierBuilder.addThing(owner, unifiedOwner.id());
            } else return Iterators.empty();

            ThingVariable attr = has().attribute();
            ThingVariable conclusionAttr = hasConclusion.attribute();
            if (Unifier.Builder.unificationSatisfiable(attr, conclusionAttr)) {
                unifierBuilder.addThing(attr, conclusionAttr.id());
                if (attr.isa().isPresent() && attr.isa().get().type().label().isPresent()) {
                    // $x has [type] $a/"John"
                    assert attr.isa().isPresent() && attr.isa().get().type().label().isPresent() &&
                            Unifier.Builder.subtypeLabels(attr.isa().get().type().label().get().properLabel(), conceptMgr).toSet()
                                    .containsAll(unifierBuilder.requirements().isaExplicit().get(attr.id()));
                }
                unifierBuilder.addConstantValueRequirements(predicates, attr.id(), conclusionAttr.id());
            } else return Iterators.empty();

            return single(unifierBuilder.build());
        }

        @Override
        public boolean isHas() {
            return true;
        }

        @Override
        public Has asHas() {
            return this;
        }

        @Override
        public ThingVariable generatingVariable() {
            return has.attribute();
        }

        @Override
        public Set<Variable> generating() {
            return generating;
        }

        @Override
        public Map<Rule, Set<Unifier>> computeApplicableRules(ConceptManager conceptMgr, LogicManager logicMgr) {
            Set<Label> attributeTypes = generatingVariable().inferredTypes();
            assert !generatingVariable().inferredTypes().isEmpty();
            Map<Rule, Set<Unifier>> applicableRules = new HashMap<>();
            attributeTypes.forEach(type -> logicMgr.rulesConcludingHas(type)
                    .forEachRemaining(rule -> unify(rule.conclusion(), conceptMgr)
                            .forEachRemaining(unifier -> {
                                applicableRules.putIfAbsent(rule, new HashSet<>());
                                applicableRules.get(rule).add(unifier);
                            })));

            return applicableRules;
        }

        @Override
        public FunctionalIterator<AlphaEquivalence> alphaEquals(Concludable that) {
            return AlphaEquivalence.empty().alphaEqualIf(that.isHas())
                    .flatMap(a -> has().alphaEquals(that.asHas().has()).flatMap(a::extendIfCompatible))
                    .flatMap(a -> AlphaEquivalence.alphaEquals(isa().orElse(null), that.asHas().isa().orElse(null))
                            .flatMap(a::extendIfCompatible))
                    .flatMap(a -> alphaEqualPredicateConstraints(predicates(), that.asHas().predicates())
                            .flatMap(a::extendIfCompatible));
        }

    }

    /**
     * Isa handles concludable these concludable patterns, where the owner of the IsaConstraint is not already the
     * subject of a Has or Relation Concludable:
     * `{ $x isa person; }`
     * `{ $a isa age; $a = 30; }`
     * `{ $a isa age; $a > 5; $a < 30; }`
     * Value constraints are included here to improve performance. Only `=` is added as a requirement on the unifier.
     */
    public static class Isa extends Concludable {

        private final IsaConstraint isa;
        private final Set<PredicateConstraint> predicates;
        private final Set<Variable> generating;

        private Isa(Conjunction conjunction, IsaConstraint isa, Set<PredicateConstraint> predicates) {
            super(conjunction);
            this.isa = isa;
            this.predicates = predicates;
            this.generating = set(generatingVariable());
        }

        public static Isa of(IsaConstraint isa, Set<PredicateConstraint> predicates, Set<LabelConstraint> labelConstraints) {
            Conjunction.ConstraintCloner cloner = Conjunction.ConstraintCloner.cloneExactly(labelConstraints, predicates, isa);
            Set<PredicateConstraint> clonedPredicates = new HashSet<>();
            iterate(predicates).map(c -> cloner.getClone(c).asThing().asPredicate()).forEachRemaining(clonedPredicates::add);
            return new Isa(cloner.conjunction(), cloner.getClone(isa).asThing().asIsa(), clonedPredicates);
        }

        public IsaConstraint isa() {
            return isa;
        }

        public Set<PredicateConstraint> predicates() {
            return predicates;
        }

        @Override
        public Set<Constraint> concludableConstraints() {
            Set<Constraint> constraints = new HashSet<>();
            constraints.add(isa);
            constraints.addAll(Unifier.Builder.constantPredicateConstraints(predicates));
            return set(constraints);
        }

        @Override
        public FunctionalIterator<Unifier> unify(Rule.Conclusion conclusion, ConceptManager conceptMgr) {
            if (conclusion.isIsa()) return unify(conclusion.asIsa(), conceptMgr);
            return Iterators.empty();
        }

        @Override
        public boolean isInferredAnswer(ConceptMap conceptMap) {
            return conceptMap.get(isa().owner().id()).asThing().isInferred();
        }

        FunctionalIterator<Unifier> unify(Rule.Conclusion.Isa isa, ConceptManager conceptMgr) {
            Unifier.Builder unifierBuilder = Unifier.builder();
            ThingVariable owner = isa().owner();
            ThingVariable unifiedOwner = isa.isa().owner();
            if (Unifier.Builder.unificationSatisfiable(owner, unifiedOwner)) {
                unifierBuilder.addThing(owner, unifiedOwner.id());
            } else return Iterators.empty();

            TypeVariable type = isa().type();
            TypeVariable unifiedType = isa.isa().type();
            if (Unifier.Builder.unificationSatisfiable(type, unifiedType, conceptMgr)) {
                if (type.id().isLabel()) {
                    // form: $r isa friendship -> require type subs(friendship) for anonymous type variable
                    Set<Label> allowedTypes = Unifier.Builder.subtypeLabels(type.inferredTypes(), conceptMgr).toSet();
                    assert allowedTypes.containsAll(unifierBuilder.requirements().isaExplicit().get(owner.id()));
                    unifierBuilder.addLabelType(type.id().asLabel(), allowedTypes, unifiedType.id());
                } else {
                    unifierBuilder.addVariableType(type, unifiedType.id());
                }
                unifierBuilder.addConstantValueRequirements(predicates, owner.id(), unifiedOwner.id());
            } else return Iterators.empty();

            return single(unifierBuilder.build());
        }

        @Override
        public boolean isIsa() {
            return true;
        }

        @Override
        public Isa asIsa() {
            return this;
        }

        @Override
        public ThingVariable generatingVariable() {
            return isa.owner();
        }

        @Override
        public Set<Variable> generating() {
            return generating;
        }

        @Override
        public Map<Rule, Set<Unifier>> computeApplicableRules(ConceptManager conceptMgr, LogicManager logicMgr) {
            return applicableRules(generatingVariable().inferredTypes(), conceptMgr, logicMgr);
        }

        @Override
        public FunctionalIterator<AlphaEquivalence> alphaEquals(Concludable that) {
            return AlphaEquivalence.empty().alphaEqualIf(that.isIsa())
                    .flatMap(a -> isa().alphaEquals(that.asIsa().isa()).flatMap(a::extendIfCompatible))
                    .flatMap(a -> alphaEqualPredicateConstraints(predicates(), that.asIsa().predicates()).flatMap(a::extendIfCompatible));
        }
    }

    /**
     * Attribute handles patterns where nothing is known about an attribute except its value:
     * `{ $a = 30; }`
     * `{ $a > 5; $a < 20; }`
     * It does not handle `{ $a < $b; }`, this scenario should be split into a Retrievable of `{ $a < $b; }`, a
     * `Concludable.Attribute` of `$a` and a `Concludable.Attribute` of `$b` (both having an empty set of
     * predicateConstraints). Only `=` is added as a requirement on the unifier.
     */
    public static class Attribute extends Concludable {

        private final Set<PredicateConstraint> values;
        private final ThingVariable attribute;
        private final Set<Variable> generating;

        private Attribute(ThingVariable attribute, Set<PredicateConstraint> values) {
            super(new Conjunction(set(attribute), list()));
            this.attribute = attribute;
            this.values = values;
            this.generating = set(generatingVariable());
        }

        private Attribute(IsaConstraint isa) {
            super(new Conjunction(isa.variables(), list()));
            attribute = isa.owner();
            values = set();
            this.generating = set(generatingVariable());
        }

        public static Attribute of(ThingVariable attribute) {
            TypeVariable typeVar = TypeVariable.of(Identifier.Variable.of(Reference.label(TypeQLToken.Type.ATTRIBUTE.toString())));
            typeVar.label(Label.of(TypeQLToken.Type.ATTRIBUTE.toString()));
            typeVar.setInferredTypes(attribute.inferredTypes());
            return new Attribute(attribute.clone().isa(typeVar, false));
        }

        public static Attribute of(ThingVariable attribute, Set<PredicateConstraint> values) {
            assert iterate(values).map(ThingConstraint::owner).toSet().equals(set(attribute));
            Conjunction.ConstraintCloner cloner = Conjunction.ConstraintCloner.cloneExactly(values);
            assert cloner.conjunction().variables().size() == 1;
            FunctionalIterator<PredicateConstraint> valueIt = iterate(values).map(v -> cloner.getClone(v).asThing().asPredicate());
            return new Attribute(cloner.conjunction().variables().iterator().next().asThing(), valueIt.toSet());
        }

        @Override
        public Set<Constraint> concludableConstraints() {
            if (values.isEmpty()) {
                assert attribute.isa().isPresent();
                return set(attribute.isa().get());
            } else {
                return new HashSet<>(Unifier.Builder.constantPredicateConstraints(values));
            }
        }

        public ThingVariable attribute() {
            return attribute;
        }

        public Set<PredicateConstraint> values() {
            return values;
        }

        @Override
        public FunctionalIterator<Unifier> unify(Rule.Conclusion conclusion, ConceptManager conceptMgr) {
            if (conclusion.isValue()) return unify(conclusion.asValue());
            return Iterators.empty();
        }

        @Override
        public boolean isInferredAnswer(ConceptMap conceptMap) {
            return conceptMap.get(generatingVariable().id()).asThing().isInferred();
        }

        FunctionalIterator<Unifier> unify(Rule.Conclusion.Value value) {
            assert iterate(values).filter(pred -> pred.predicate().isThingVar()).toSet().size() == 0;
            Unifier.Builder unifierBuilder = Unifier.builder();
            if (Unifier.Builder.unificationSatisfiable(attribute, value.value().owner())) {
                unifierBuilder.addThing(attribute, value.value().owner().id());
            } else return Iterators.empty();
            unifierBuilder.addConstantValueRequirements(values, attribute.id(), value.value().owner().id());
            return single(unifierBuilder.build());
        }

        @Override
        public boolean isAttribute() {
            return true;
        }

        @Override
        public Attribute asAttribute() {
            return this;
        }

        @Override
        public ThingVariable generatingVariable() {
            return attribute;
        }

        @Override
        public Set<Variable> generating() {
            return generating;
        }

        @Override
        public Map<Rule, Set<Unifier>> computeApplicableRules(ConceptManager conceptMgr, LogicManager logicMgr) {
            return applicableRules(generatingVariable().inferredTypes(), conceptMgr, logicMgr);
        }

        @Override
        public FunctionalIterator<AlphaEquivalence> alphaEquals(Concludable that) {
            return AlphaEquivalence.empty().alphaEqualIf(that.isAttribute())
                    .flatMap(a -> attribute().alphaEquals(that.asAttribute().attribute()).flatMap(a::extendIfCompatible))
                    .flatMap(a -> alphaEqualPredicateConstraints(values(), that.asAttribute().values()).flatMap(a::extendIfCompatible));
        }
    }

    private static class Extractor {

        private final Set<Variable> isaOwnersToSkip = new HashSet<>();
        private final Set<Variable> valueOwnersToSkip = new HashSet<>();
        private final Set<Concludable> concludables = new HashSet<>();

        Extractor(Conjunction conjunction) {
            Set<Constraint> constraints = conjunction.variables().stream().flatMap(variable -> variable.constraints().stream())
                    .collect(toSet());
            constraints.stream().filter(Constraint::isThing).map(Constraint::asThing).filter(ThingConstraint::isRelation)
                    .map(ThingConstraint::asRelation).forEach(this::fromConstraint);
            constraints.stream().filter(Constraint::isThing).map(Constraint::asThing).filter(ThingConstraint::isHas)
                    .map(ThingConstraint::asHas).forEach(this::fromConstraint);
            constraints.stream().filter(Constraint::isThing).map(Constraint::asThing).filter(ThingConstraint::isIsa)
                    .map(ThingConstraint::asIsa).forEach(this::fromConstraint);
            constraints.stream().filter(Constraint::isThing).map(Constraint::asThing).filter(ThingConstraint::isPredicate)
                    .map(ThingConstraint::asPredicate).forEach(this::fromConstraint);
        }

        public void fromConstraint(RelationConstraint relationConstraint) {
            Set<LabelConstraint> labelConstraints = concatToSet(labelConstraints(relationConstraint), relationConstraint.owner().isa().map(Extractor::labelConstraints).orElse(set()));
            concludables.add(Relation.of(relationConstraint, relationConstraint.owner().isa().orElse(null), labelConstraints));
            isaOwnersToSkip.add(relationConstraint.owner());
        }

        private void fromConstraint(HasConstraint hasConstraint) {
            Set<LabelConstraint> labelConstraints = concatToSet(labelConstraints(hasConstraint), hasConstraint.attribute().isa().map(Extractor::labelConstraints).orElse(set()));
            Set<PredicateConstraint> predicateConstraints = Iterators.iterate(hasConstraint.attribute().predicates()).filter(v -> !v.predicate().isThingVar()).toSet();
            concludables.add(Has.of(hasConstraint, hasConstraint.attribute().isa().orElse(null), predicateConstraints, labelConstraints));
            isaOwnersToSkip.add(hasConstraint.attribute());
            valueOwnersToSkip.add(hasConstraint.attribute());
        }

        private void fromConstraint(IsaConstraint isaConstraint) {
            if (isaOwnersToSkip.contains(isaConstraint.owner())) return;
            Set<PredicateConstraint> predicateConstraints = Iterators.iterate(isaConstraint.owner().predicates()).filter(v -> !v.predicate().isThingVar()).toSet();
            concludables.add(Concludable.Isa.of(isaConstraint, predicateConstraints, labelConstraints(isaConstraint)));
            isaOwnersToSkip.add(isaConstraint.owner());
            valueOwnersToSkip.add(isaConstraint.owner());
        }

        private void fromConstraint(PredicateConstraint predicateConstraint) {
            if (valueOwnersToSkip.contains(predicateConstraint.owner())) return;
            if (predicateConstraint.predicate().isThingVar()) {
                // form: `{ $x > $y; }`
                concludables.add(Attribute.of(predicateConstraint.owner()));
                Predicate.ThingVar val;
                if (!valueOwnersToSkip.contains((val = predicateConstraint.predicate().asThingVar()).value())) {
                    concludables.add(Attribute.of(val.value()));
                    valueOwnersToSkip.add(val.value());
                }
            } else {
                concludables.add(Attribute.of(predicateConstraint.owner(), set(predicateConstraint.owner().predicates())));
            }
            valueOwnersToSkip.add(predicateConstraint.owner());
        }

        public Set<Concludable> concludables() {
            return set(concludables);
        }

        private static Set<LabelConstraint> labelConstraints(Constraint constraint) {
            return iterate(constraint.variables()).filter(v -> v.reference().isLabel()).map(
                    v -> v.asType().label().get()).toSet();
        }
    }
}
