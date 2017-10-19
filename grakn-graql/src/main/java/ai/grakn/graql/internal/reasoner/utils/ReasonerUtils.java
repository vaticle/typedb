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

package ai.grakn.graql.internal.reasoner.utils;

import ai.grakn.concept.RelationshipType;
import ai.grakn.concept.Role;
import ai.grakn.concept.SchemaConcept;
import ai.grakn.concept.Type;
import ai.grakn.graql.Var;
import ai.grakn.graql.admin.ReasonerQuery;
import ai.grakn.graql.admin.VarPatternAdmin;
import ai.grakn.graql.internal.pattern.property.IdProperty;
import ai.grakn.graql.internal.pattern.property.LabelProperty;
import ai.grakn.graql.internal.pattern.property.ValueProperty;
import ai.grakn.graql.internal.reasoner.atom.predicate.IdPredicate;
import ai.grakn.graql.internal.reasoner.atom.predicate.ValuePredicate;
import ai.grakn.graql.internal.reasoner.utils.conversion.SchemaConceptConverter;
import ai.grakn.util.Schema;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;

import java.util.Collection;
import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Stream;

import static ai.grakn.graql.internal.reasoner.atom.predicate.ValuePredicate.createValueVar;
import static java.util.stream.Collectors.toSet;

/**
 *
 * <p>
 * Utiliy class providing useful functionalities.
 * </p>
 *
 * @author Kasper Piskorski
 *
 */
public class ReasonerUtils {

    /**
     * looks for an appropriate var property with a specified name among the vars and maps it to an IdPredicate,
     * covers the case when specified variable name is user defined
     * @param typeVariable variable name of interest
     * @param vars VarAdmins to look for properties
     * @param parent reasoner query the mapped predicate should belong to
     * @return mapped IdPredicate
     */
    public static IdPredicate getUserDefinedIdPredicate(Var typeVariable, Set<VarPatternAdmin> vars, ReasonerQuery parent){
        return  vars.stream()
                .filter(v -> v.var().equals(typeVariable))
                .flatMap(v -> v.hasProperty(LabelProperty.class)?
                        v.getProperties(LabelProperty.class).map(np -> new IdPredicate(typeVariable, np.label(), parent)) :
                        v.getProperties(IdProperty.class).map(np -> new IdPredicate(typeVariable, np.id(), parent)))
                .findFirst().orElse(null);
    }

    /**
     * looks for an appropriate var property with a specified name among the vars and maps it to an IdPredicate,
     * covers both the cases when variable is and isn't user defined
     * @param typeVariable variable name of interest
     * @param typeVar {@link VarPatternAdmin} to look for in case the variable name is not user defined
     * @param vars VarAdmins to look for properties
     * @param parent reasoner query the mapped predicate should belong to
     * @return mapped IdPredicate
     */
    @Nullable
    public static IdPredicate getIdPredicate(Var typeVariable, VarPatternAdmin typeVar, Set<VarPatternAdmin> vars, ReasonerQuery parent){
        IdPredicate predicate = null;
        //look for id predicate among vars
        if(typeVar.var().isUserDefinedName()) {
            predicate = getUserDefinedIdPredicate(typeVariable, vars, parent);
        } else {
            LabelProperty nameProp = typeVar.getProperty(LabelProperty.class).orElse(null);
            if (nameProp != null) predicate = new IdPredicate(typeVariable, nameProp.label(), parent);
        }
        return predicate;
    }

    /**
     * looks for appropriate var properties with a specified name among the vars and maps them to ValuePredicates,
     * covers both the case when variable is and isn't user defined
     * @param valueVariable variable name of interest
     * @param valueVar {@link VarPatternAdmin} to look for in case the variable name is not user defined
     * @param vars VarAdmins to look for properties
     * @param parent reasoner query the mapped predicate should belong to
     * @return set of mapped ValuePredicates
     */
    public static Set<ValuePredicate> getValuePredicates(Var valueVariable, VarPatternAdmin valueVar, Set<VarPatternAdmin> vars, ReasonerQuery parent){
        Set<ValuePredicate> predicates = new HashSet<>();
        if(valueVar.var().isUserDefinedName()){
            vars.stream()
                    .filter(v -> v.var().equals(valueVariable))
                    .flatMap(v -> v.getProperties(ValueProperty.class).map(vp -> new ValuePredicate(v.var(), vp.predicate(), parent)))
                    .forEach(predicates::add);
        }
        //add value atom
        else {
            valueVar.getProperties(ValueProperty.class)
                    .forEach(vp -> predicates
                            .add(new ValuePredicate(createValueVar(valueVariable, vp.predicate()), parent)));
        }
        return predicates;
    }

    /**
     * @param schemaConcept input type
     * @return set of all non-meta super types of the role
     */
    public static Set<SchemaConcept> supers(SchemaConcept schemaConcept){
        Set<SchemaConcept> superTypes = new HashSet<>();
        SchemaConcept superType = schemaConcept.sup();
        while(superType != null && !Schema.MetaSchema.isMetaLabel(superType.getLabel())) {
            superTypes.add(superType);
            superType = superType.sup();
        }
        return superTypes;
    }

    /**
     * @param concept which hierarchy should be considered
     * @return set of {@link SchemaConcept}s consisting of the provided {@link SchemaConcept} and all its supers including meta
     */
    public static Set<SchemaConcept> upstreamHierarchy(SchemaConcept concept){
        Set<SchemaConcept> concepts = new HashSet<>();
        SchemaConcept superType = concept;
        while(superType != null) {
            concepts.add(superType);
            superType = superType.sup();
        }
        return concepts;
    }

    /**
     *
     * @param type for which top type is to be found
     * @return non-meta top type of the type
     */
    public static Type topType(Type type){
        Type superType = type;
        while(superType != null && !Schema.MetaSchema.isMetaLabel(superType.getLabel())) {
            superType = superType.sup();
        }
        return superType;
    }

    /**
     * @param schemaConcepts entry set
     * @return top non-meta {@link SchemaConcept} from within the provided set of {@link Role}
     */
    public static <T extends SchemaConcept> Set<T> schemaConcepts(Set<T> schemaConcepts) {
        return schemaConcepts.stream()
                .filter(rt -> Sets.intersection(supers(rt), schemaConcepts).isEmpty())
                .collect(toSet());
    }

    /**
     * Gets {@link Role} a given {@link Type} can play in the provided {@link RelationshipType} by performing
     * type intersection between type's playedRoles and relation's relates.
     * @param type for which we want to obtain compatible {@link Role}s it plays
     * @param relRoles entry {@link Role}s
     * @return set of {@link Role}s the type can play from the provided {@link Role}s
     */
    public static Set<Role> compatibleRoles(Type type, Stream<Role> relRoles) {
        Set<Role> typeRoles = type.plays().collect(toSet());
        return relRoles.filter(typeRoles::contains).collect(toSet());
    }

    /**
     * calculates map intersection by doing an intersection on key sets and accumulating the keys
     * @param m1 first operand
     * @param m2 second operand
     * @param <K> map key type
     * @param <V> map value type
     * @return map intersection
     */
    public static <K, V> Multimap<K, V> multimapIntersection(Multimap<K, V> m1, Multimap<K, V> m2){
        Multimap<K, V> intersection = HashMultimap.create();
        Sets.SetView<K> keyIntersection = Sets.intersection(m1.keySet(), m2.keySet());
        Stream.concat(m1.entries().stream(), m2.entries().stream())
                .filter(e -> keyIntersection.contains(e.getKey()))
                .forEach(e -> intersection.put(e.getKey(), e.getValue()));
        return intersection;
    }

    /**
     * compute the map of compatible {@link RelationshipType}s for a given set of {@link Type}s
     * (intersection of allowed sets of relation types for each entry type) and compatible role types
     * @param types for which the set of compatible {@link RelationshipType}s is to be computed
     * @param schemaConceptConverter converter between {@link SchemaConcept} and relation type-role entries
     * @param <T> type generic
     * @return map of compatible {@link RelationshipType}s and their corresponding {@link Role}s
     */
    public static <T extends SchemaConcept> Multimap<RelationshipType, Role> compatibleRelationTypesWithRoles(Set<T> types, SchemaConceptConverter<T> schemaConceptConverter) {
        Multimap<RelationshipType, Role> compatibleTypes = HashMultimap.create();
        if (types.isEmpty()) return compatibleTypes;
        Iterator<T> it = types.iterator();
        compatibleTypes.putAll(schemaConceptConverter.toRelationshipMultimap(it.next()));
        while(it.hasNext() && !compatibleTypes.isEmpty()) {
            compatibleTypes = multimapIntersection(compatibleTypes, schemaConceptConverter.toRelationshipMultimap(it.next()));
        }
        return compatibleTypes;
    }

    /**
     * @param parentRole parent {@link Role}
     * @param parentType parent {@link SchemaConcept}
     * @param childRoles entry set of possible {@link Role}s
     * @return set of playable {@link Role}s defined by type-role parent
     */
    public static Set<Role> playableRoles(Role parentRole, SchemaConcept parentType, Set<Role> childRoles) {
        boolean isParentRoleMeta = Schema.MetaSchema.isMetaLabel(parentRole.getLabel());
        Set<Role> compatibleRoles = Sets.union(
                Sets.newHashSet(parentRole),
                isParentRoleMeta? childRoles : Sets.intersection(parentRole.subs().collect(toSet()), childRoles)
        );

        //if parent role player has a type, constrain the allowed roles
        if (parentType != null && parentType.isType()) {
            boolean isParentTypeMeta = Schema.MetaSchema.isMetaLabel(parentType.getLabel());
            Set<Role> parentTypeRoles = isParentTypeMeta ? childRoles : parentType.asType().plays().collect(toSet());

            compatibleRoles = compatibleRoles.stream()
                    .filter(rc -> Schema.MetaSchema.isMetaLabel(rc.getLabel()) || parentTypeRoles.contains(rc))
                    .collect(toSet());

            //parent role also possible
            compatibleRoles.add(parentRole);
        }
        return compatibleRoles;
    }

    /**
     * @param parent type
     * @param child type
     * @return true if child is a subtype of parent
     */
    public static boolean typesCompatible(SchemaConcept parent, SchemaConcept child) {
        if (parent == null) return true;
        if (child == null) return false;
        if (Schema.MetaSchema.isMetaLabel(parent.getLabel())) return true;
        SchemaConcept superType = child;
        while(superType != null && !Schema.MetaSchema.isMetaLabel(superType.getLabel())){
            if (superType.equals(parent)) return true;
            superType = superType.sup();
        }
        return false;
    }

    /** determines disjointness of parent-child types, parent defines the bound on the child
     * @param parent type
     * @param child type
     * @return true if types do not belong to the same type hierarchy, also true if parent is null and false if parent non-null and child null
     */
    public static boolean areDisjointTypes(SchemaConcept parent, SchemaConcept child) {
        return parent != null && child == null || !typesCompatible(parent, child) && !typesCompatible(child, parent);
    }

    /**
     * @param a subtraction left operand
     * @param b subtraction right operand
     * @param <T> collection type
     * @return new Collection containing a minus a - b.
     * The cardinality of each element e in the returned Collection will be the cardinality of e in a minus the cardinality of e in b, or zero, whichever is greater.
     */
    public static <T> Collection<T> subtract(Collection<T> a, Collection<T> b){
        ArrayList<T> list = new ArrayList<>(a);
        b.forEach(list::remove);
        return list;
    }
}
