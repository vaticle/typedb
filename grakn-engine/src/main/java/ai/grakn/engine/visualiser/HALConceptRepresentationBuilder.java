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

package ai.grakn.engine.visualiser;

import ai.grakn.concept.Concept;
import ai.grakn.engine.controller.VisualiserController;
import ai.grakn.graql.MatchQuery;
import ai.grakn.graql.internal.pattern.property.RelationProperty;
import ai.grakn.util.REST;
import com.theoryinpractise.halbuilder.api.Representation;
import com.theoryinpractise.halbuilder.api.RepresentationFactory;
import org.json.JSONArray;
import org.json.JSONObject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.stream.Collectors;

public class HALConceptRepresentationBuilder {

    private final static Logger LOG = LoggerFactory.getLogger(VisualiserController.class);
    private final static int MATCH_QUERY_FIXED_DEGREE = 0;
    private final static String ASSERTION_URL = REST.WebPath.GRAPH_MATCH_QUERY_URI + "?query=match $x id '%s'; $y id '%s'; $r ($x, $y); select $r;";
    private final static String HAS_ROLE_EDGE = "has-role";

    public static JSONArray renderHALArrayData(MatchQuery matchQuery, Collection<Map<String, Concept>> graqlResultsList) {
        //Compute connections between variables in Graql result
        Map<String, Collection<String>> linkedNodes = computeLinkedNodesFromQuery(matchQuery);
        //Collect all the types explicitly asked in the match query
        Set<String> typesAskedInQuery = matchQuery.admin().getTypes().stream().map(Concept::getId).collect(Collectors.toSet());
        //Check if among the types asked in the query there is a relation-type (we only support one relation-type per query)
        String relationType = matchQuery.admin().getTypes().stream()
                .filter(Concept::isRelationType)
                .findFirst().map(Concept::getId)
                .orElse("");

        return buildHALRepresentations(graqlResultsList, linkedNodes, typesAskedInQuery,relationType);
    }

    public static String renderHALConceptData(Concept concept, int separationDegree) {
        return new HALConceptData(concept, separationDegree, false, new HashSet<>()).render();
    }

    public static String renderHALConceptOntology(Concept concept) {
        return new HALConceptOntology(concept).render();
    }

    private static JSONArray buildHALRepresentations(Collection<Map<String, Concept>> graqlResultsList, Map<String, Collection<String>> linkedNodes, Set<String> typesAskedInQuery, String relationType) {
        final JSONArray lines = new JSONArray();
        graqlResultsList.parallelStream()
                .forEach(resultLine -> resultLine.entrySet().forEach(current -> {
                    LOG.trace("Building HAL resource for concept with id {}", current.getValue().getId());
                    Representation currentHal = new HALConceptData(current.getValue(), MATCH_QUERY_FIXED_DEGREE, true,
                            typesAskedInQuery).getRepresentation();
                    attachGeneratedRelation(currentHal, current, linkedNodes, resultLine, relationType);
                    lines.put(new JSONObject(currentHal.toString(RepresentationFactory.HAL_JSON)));
                }));
        return lines;
    }

    private static void attachGeneratedRelation(Representation currentHal,Map.Entry<String,Concept> current, Map<String, Collection<String>> linkedNodes, Map<String, Concept> resultLine, String relationType){
        if (linkedNodes.containsKey(current.getKey())) {
            linkedNodes.get(current.getKey())
                    .forEach(varName -> {
                        Concept rolePlayer = resultLine.get(varName);
                        String currentID = current.getValue().getId();
                        String firstID = (currentID.compareTo(rolePlayer.getId()) > 0) ? currentID : rolePlayer.getId();
                        String secondID = (currentID.compareTo(rolePlayer.getId()) > 0) ? rolePlayer.getId() : currentID;
                        String assertionID = String.format(ASSERTION_URL, firstID, secondID);
                        currentHal.withRepresentation(HAS_ROLE_EDGE, new HALGeneratedRelation().getNewGeneratedRelation(assertionID, relationType));
                    });
        }
    }

    private static Map<String, Collection<String>> computeLinkedNodesFromQuery(MatchQuery matchQuery) {
        final Map<String, Collection<String>> linkedNodes = new HashMap<>();
        matchQuery.admin().getPattern().getVars().forEach(var -> {
            //if in the current var is expressed some kind of relation (e.g. ($x,$y))
            if (var.getProperty(RelationProperty.class).isPresent()) {
                //collect all the role players in the current var's relations (e.g. 'x' and 'y')
                final List<String> rolePlayersInVar = var.getProperty(RelationProperty.class).get()
                        .getRelationPlayers().map(x -> x.getRolePlayer().getName()).collect(Collectors.toList());
                //if it is a binary or ternary relation
                if (rolePlayersInVar.size() > 1) {
                    rolePlayersInVar.forEach(rolePlayer -> {
                        linkedNodes.putIfAbsent(rolePlayer, new HashSet<>());
                        rolePlayersInVar.forEach(y -> {
                            if (!y.equals(rolePlayer))
                                linkedNodes.get(rolePlayer).add(y);
                        });
                    });
                }
            }
        });
        return linkedNodes;
    }
}
