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

package ai.grakn.graql.internal.reasoner;

import ai.grakn.GraknGraph;
import ai.grakn.concept.Concept;
import ai.grakn.concept.RelationType;
import ai.grakn.concept.RoleType;
import ai.grakn.concept.Rule;
import ai.grakn.concept.Type;
import ai.grakn.util.Schema;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import ai.grakn.graql.Graql;
import ai.grakn.graql.Pattern;
import ai.grakn.graql.Var;
import ai.grakn.graql.admin.VarAdmin;
import ai.grakn.graql.internal.pattern.Patterns;
import ai.grakn.util.ErrorMessage;
import javafx.util.Pair;

import java.util.*;


/**
 *
 * <p>
 * Utiliy class providing useful
 * </p>
 *
 * @author Kasper Piskorski
 *
 */
public class Utility {

    /**
     * Provides more readable answer output.
     * @param answers set of answers to be printed
     */
    public static void printAnswers(Set<Map<String, Concept>> answers) {
        answers.forEach(result -> {
            result.entrySet().forEach(entry -> {
                Concept concept = entry.getValue();
                System.out.print(entry.getKey() + ": " + concept.getId() + " : ");
                if (concept.isResource())
                    System.out.print(concept.asResource().getValue() + " ");
            });
            System.out.println();
        });
        System.out.println();
    }

    /**
     * Gets roletypes a given type can play in the provided relType relation type by performing
     * type intersection between type's playedRoles and relation's hasRoles.
     * @param type for which we want to obtain compatible roles it plays
     * @param relType relation type of interest
     * @return set of role types the type can play in relType
     */
    public static Set<RoleType> getCompatibleRoleTypes(Type type, Type relType) {
        Set<RoleType> cRoles = new HashSet<>();
        Collection<RoleType> typeRoles = type.playsRoles();
        Collection<RoleType> relRoles = ((RelationType) relType).hasRoles();
        relRoles.stream().filter(typeRoles::contains).forEach(cRoles::add);
        return cRoles;
    }

    public static Set<RelationType> getCompatibleRelationTypes(Set<RoleType> roles) {
        Set<RelationType> compatibleTypes = new HashSet<>();
        if (roles.isEmpty()) return compatibleTypes;
        Iterator<RoleType> it =  roles.iterator();
        compatibleTypes.addAll(it.next().relationTypes());
        while(it.hasNext() && compatibleTypes.size() > 1)
            compatibleTypes.retainAll(it.next().relationTypes());
        return compatibleTypes;
    }

    /**
     * compute all rolePlayer-roleType combinations complementing provided roleMap
     * @param vars set of rolePlayers
     * @param roles set of roleTypes
     * @param roleMap initial rolePlayer-roleType roleMap to be complemented
     * @param roleMaps output set containing possible role mappings complementing the roleMap configuration
     */
    public static void computeRoleCombinations(Set<String> vars, Set<RoleType> roles, Map<String, String> roleMap,
                                        Set<Map<String, String>> roleMaps){
        Set<String> tempVars = Sets.newHashSet(vars);
        Set<RoleType> tempRoles = Sets.newHashSet(roles);
        String var = vars.iterator().next();

        roles.forEach(role -> {
            tempVars.remove(var);
            tempRoles.remove(role);
            roleMap.put(var, role.getName());
            if (!tempVars.isEmpty() && !tempRoles.isEmpty())
                computeRoleCombinations(tempVars, tempRoles, roleMap, roleMaps);
            else {
                if (!roleMap.isEmpty())
                    roleMaps.add(Maps.newHashMap(roleMap));
                roleMap.remove(var);
            }
            tempVars.add(var);
            tempRoles.add(role);
        });
    }

    /**
     * generate a fresh variable avoiding global variables and variables from the same query
     * @param vars  vars to be avoided
     * @param var variable to be generated a fresh replacement
     * @return fresh variables
     */
    public static String createFreshVariable(Set<String> vars, String var) {
        String fresh = var;
        while (vars.contains(fresh)) {
            String valFree = fresh.replaceAll("[^0-9]", "");
            int value = valFree.equals("") ? 0 : Integer.parseInt(valFree);
            fresh = fresh.replaceAll("\\d+", "") + (++value);
        }
        return fresh;
    }

    /**
     * create transitive rule R(from: X, to: Y) :- R(from: X,to: Z), R(from: Z, to: Y)
     * @param relType transitive relation type
     * @param fromRoleName  from directional role type type name
     * @param toRoleName to directional role type type name
     * @param graph graph for the rule to be inserted
     * @return rule instance
     */
    public static Rule createTransitiveRule(RelationType relType, String fromRoleName, String toRoleName, GraknGraph graph){
        final int arity = relType.hasRoles().size();
        if (arity != 2)
            throw new IllegalArgumentException(ErrorMessage.RULE_CREATION_ARITY_ERROR.getMessage());

        VarAdmin startVar = Graql.var().isa(relType.getName()).rel(fromRoleName, "x").rel(toRoleName, "z").admin();
        VarAdmin endVar = Graql.var().isa(relType.getName()).rel(fromRoleName, "z").rel(toRoleName, "y").admin();
        VarAdmin headVar = Graql.var().isa(relType.getName()).rel(fromRoleName, "x").rel(toRoleName, "y").admin();
        Pattern body = Patterns.conjunction(Sets.newHashSet(startVar, endVar));
        return graph.admin().getMetaRuleInference().addRule(body, headVar);
    }

    /**
     * create reflexive rule R(from: X, to: X) :- R(from: X,to: Y)
     * @param relType reflexive relation type
     * @param graph graph for the rule to be inserted
     * @return rule instance
     */
    public static Rule createReflexiveRule(RelationType relType, GraknGraph graph){
        final int arity = relType.hasRoles().size();
        if (arity != 2)
            throw new IllegalArgumentException(ErrorMessage.RULE_CREATION_ARITY_ERROR.getMessage());

        Var body = Graql.var().isa(relType.getName()).rel("x").rel("y");
        Var head = Graql.var().isa(relType.getName()).rel("x").rel("x");
        return graph.admin().getMetaRuleInference().addRule(body, head);
    }

    /**
     * creates rule parent :- child
     * @param parent relation type of parent
     * @param child relation type of child
     * @param roleMappings map of corresponding role type type names
     * @param graph graph for the rule to be inserted
     * @return rule instance
     */
    public static Rule createSubPropertyRule(RelationType parent, RelationType child, Map<String, String> roleMappings,
                                             GraknGraph graph){
        final int parentArity = parent.hasRoles().size();
        final int childArity = child.hasRoles().size();
        if (parentArity != childArity || parentArity != roleMappings.size())
            throw new IllegalArgumentException(ErrorMessage.RULE_CREATION_ARITY_ERROR.getMessage());
        Var parentVar = Graql.var().isa(parent.getName());
        Var childVar = Graql.var().isa(child.getName());
        Set<String> vars = new HashSet<>();

        roleMappings.forEach( (parentRoleName, childRoleName) -> {
            String varName = createFreshVariable(vars, "x");
            parentVar.rel(parentRoleName, varName);
            childVar.rel(childRoleName, varName);
            vars.add(varName);
        });
        return graph.admin().getMetaRuleInference().addRule(childVar, parentVar);
    }

    /**
     * creates rule R(fromRole: x, toRole: xm) :- R1(fromRole: x, ...), , R2, ... , Rn(..., toRole: xm)
     * @param relation head relation
     * @param fromRoleName specifies the role directionality of the head relation
     * @param toRoleName specifies the role directionality of the head relation
     * @param chain map containing ordered relation with their corresponding role mappings
     * @param graph graph for the rule to be inserted
     * @return rule instance
     */
    public static Rule createPropertyChainRule(RelationType relation, String fromRoleName, String toRoleName,
                                             LinkedHashMap<RelationType, Pair<String, String>> chain, GraknGraph graph){
        Stack<String> varNames = new Stack<>();
        varNames.push("x");
        Set<VarAdmin> bodyVars = new HashSet<>();
        chain.forEach( (relType, rolePair) ->{
            String varName = createFreshVariable(Sets.newHashSet(varNames), "x");
            VarAdmin var = Graql.var().isa(relType.getName())
                    .rel(rolePair.getKey(), varNames.peek())
                    .rel(rolePair.getValue(), varName).admin();
            varNames.push(varName);
            bodyVars.add(var);
        });

        Var headVar = Graql.var().isa(relation.getName()).rel(fromRoleName, "x").rel(toRoleName, varNames.peek());
        return graph.admin().getMetaRuleInference().addRule(Patterns.conjunction(bodyVars), headVar);
    }

    /**
     * For a given role returns all its non-meta super roles.
     * @param role in question
     * @return set of role's non-meta super types
     */
    public static Set<RoleType> getNonMetaSuperRoleTypes(RoleType role){
        Set<RoleType> roles = new HashSet<>();
        RoleType baseRole = role.superType();
        while(!Schema.MetaSchema.isMetaName(baseRole.getName())){
            roles.add(baseRole);
            baseRole = baseRole.superType();
        }
        return roles;
    }

    /**
     * @param role in question
     * @return top non-meta super role of the role
     */
    public static RoleType getNonMetaTopRole(RoleType role){
        RoleType topRole = role;
        RoleType superRole = topRole.superType();
        while(!Schema.MetaSchema.isMetaName(superRole.getName())) {
            topRole = superRole;
            superRole = superRole.superType();
        }
        return topRole;
    }

    /**
     * @param parent type
     * @param child type
     * @return true if child is subtype of parent
     */
    public static boolean checkTypesCompatible(Type parent, Type child) {
        return parent.equals(child) || parent.subTypes().contains(child);
    }

    /**
     * @param A set
     * @param B set
     * @param <T> set element type
     * @return results of set subtraction starting with larger set
     */
    public static <T> Set<T> subtractSets(Set<T> A, Set<T> B){
        Set<T> sub =  A.size() > B.size()? Sets.newHashSet(A) : Sets.newHashSet(B);
        if (A.size() > B.size())
            sub.removeAll(B);
        else
            sub.removeAll(A);
        return sub;
    }
}
