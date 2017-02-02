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
 *
 */

package ai.grakn.generator;

import ai.grakn.Grakn;
import ai.grakn.GraknGraph;
import ai.grakn.concept.Concept;
import ai.grakn.concept.Entity;
import ai.grakn.concept.EntityType;
import ai.grakn.concept.Instance;
import ai.grakn.concept.Relation;
import ai.grakn.concept.RelationType;
import ai.grakn.concept.Resource;
import ai.grakn.concept.ResourceType;
import ai.grakn.concept.RoleType;
import ai.grakn.concept.Rule;
import ai.grakn.concept.RuleType;
import ai.grakn.concept.Type;
import ai.grakn.concept.TypeName;
import ai.grakn.exception.GraphRuntimeException;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

public class GraknGraphs extends AbstractGenerator<GraknGraph> {

    private static final int MAX_CACHED_GRAPHS = 10;
    private static Map<Integer, Set<GraknGraph>> GRAPH_CACHE = new HashMap<>();

    private GraknGraph graph;

    public GraknGraphs() {
        super(GraknGraph.class);
    }

    private void mutateOnce() {
        boolean succesfulMutation = false;

        while (!succesfulMutation) {
            succesfulMutation = true;
            try {
                random.choose(mutators).run();
            } catch (UnsupportedOperationException | GraphRuntimeException | GraphGeneratorException
                    | ClassCastException e) {
                // TODO: Remove ClassCastException when `hasResource` and `key` are fixed
                // We only catch acceptable exceptions for the graph API to throw
                succesfulMutation = false;
            }
        }
    }

    @Override
    public GraknGraph generate() {
        Set<GraknGraph> cache = GRAPH_CACHE.computeIfAbsent(status.size(), key -> Sets.newHashSet());

        if (cache.size() >= MAX_CACHED_GRAPHS) {
            return random.choose(cache);
        } else {
            String keyspace = UUID.randomUUID().toString().replaceAll("-", "a");
            graph = Grakn.factory(Grakn.IN_MEMORY, keyspace).getGraph();

            for (int i = 0; i < status.size(); i++) {
                mutateOnce();
            }

            cache.add(graph);

            return graph;
        }
    }

    private final ImmutableList<Runnable> mutators = ImmutableList.of(
            () -> graph.putEntityType(gen(TypeName.class)),
            () -> graph.putResourceType(gen(TypeName.class), gen(ResourceType.DataType.class)),
            () -> graph.putResourceTypeUnique(gen(TypeName.class), gen(ResourceType.DataType.class)),
            () -> graph.putRoleType(gen(TypeName.class)),
            () -> graph.putRelationType(gen(TypeName.class)),
            () -> graph.showImplicitConcepts(gen(Boolean.class)),
            () -> graph.rollback(),
            () -> graph.close(),
            () -> graph.open(),
            () -> type().playsRole(roleType()),
            () -> type().hasResource(resourceType()),
            () -> type().key(resourceType()),
            () -> type().setAbstract(true),
            () -> entityType().superType(entityType()),
            () -> entityType().addEntity(),
            () -> roleType().superType(roleType()),
            () -> resourceType().superType(resourceType()),
            () -> relationType().addRelation(),
            () -> relationType().hasRole(roleType()),
            () -> resourceType().superType(resourceType()),
            // () -> resourceType().putResource(gen(Object.class)), TODO: Enable this when doesn't throw a NPE
            // () -> resourceType().setRegex(gen(String.class)), TODO: Enable this when doesn't throw a NPE
            () -> ruleType().superType(ruleType()),
            // () -> ruleType().addRule(null, null), TODO: Generate patterns
            () -> instance().hasResource(resource()),
            () -> relation().scope(instance()),
            () -> relation().putRolePlayer(roleType(), instance()),
            () -> rule().setExpectation(true),
            () -> rule().setMaterialise(true),
            () -> rule().addHypothesis(type()),
            () -> rule().addConclusion(type())
    );

    private Concept concept() {
        Collection<Concept> concepts = Sets.newHashSet(graph.admin().getMetaConcept().subTypes());
        concepts.addAll(graph.admin().getMetaConcept().instances());
        return random.choose(concepts);
    }

    private Type type() {
        return random.choose(graph.admin().getMetaConcept().subTypes());
    }

    private EntityType entityType() {
        return random.choose(graph.admin().getMetaEntityType().subTypes());
    }

    private RoleType roleType() {
        return random.choose(graph.admin().getMetaRoleType().subTypes());
    }

    private <T> ResourceType<T> resourceType() {
        return random.choose((Collection<ResourceType<T>>) graph.admin().getMetaResourceType().subTypes());
    }

    private RelationType relationType() {
        return random.choose(graph.admin().getMetaRelationType().subTypes());
    }

    private RuleType ruleType() {
        return random.choose(graph.admin().getMetaRuleType().subTypes());
    }

    private Instance instance() {
        return chooseOrThrow(graph.admin().getMetaConcept().instances());
    }

    private Entity entity() {
        return chooseOrThrow(graph.admin().getMetaEntityType().instances());
    }

    private Relation relation() {
        return chooseOrThrow(graph.admin().getMetaRelationType().instances());
    }

    private Resource resource() {
        return chooseOrThrow((Collection<Resource>) graph.admin().getMetaResourceType().instances());
    }

    private Rule rule() {
        return chooseOrThrow(graph.admin().getMetaRuleType().instances());
    }

    private <T> T chooseOrThrow(Collection<? extends T> collection) {
        if (collection.isEmpty()) {
            throw new GraphGeneratorException();
        } else {
            return random.choose(collection);
        }
    }
}

class GraphGeneratorException extends RuntimeException {

}


