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

package ai.grakn.graph.internal;

import ai.grakn.Grakn;
import ai.grakn.GraknGraph;
import ai.grakn.concept.Concept;
import ai.grakn.concept.ConceptId;
import ai.grakn.concept.EntityType;
import ai.grakn.concept.Instance;
import ai.grakn.concept.Relation;
import ai.grakn.concept.RelationType;
import ai.grakn.concept.Resource;
import ai.grakn.concept.ResourceType;
import ai.grakn.concept.RoleType;
import ai.grakn.concept.RuleType;
import ai.grakn.concept.Type;
import ai.grakn.concept.TypeName;
import ai.grakn.exception.ConceptException;
import ai.grakn.exception.ConceptNotUniqueException;
import ai.grakn.exception.GraknValidationException;
import ai.grakn.exception.GraphRuntimeException;
import ai.grakn.exception.InvalidConceptValueException;
import ai.grakn.exception.MoreThanOneConceptException;
import ai.grakn.factory.SystemKeyspace;
import ai.grakn.graph.admin.ConceptCache;
import ai.grakn.graph.admin.GraknAdmin;
import ai.grakn.graql.QueryBuilder;
import ai.grakn.graql.internal.query.QueryBuilderImpl;
import ai.grakn.util.EngineCommunicator;
import ai.grakn.util.ErrorMessage;
import ai.grakn.util.REST;
import ai.grakn.util.Schema;
import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.GraphTraversal;
import org.apache.tinkerpop.gremlin.process.traversal.strategy.verification.ReadOnlyStrategy;
import org.apache.tinkerpop.gremlin.structure.Direction;
import org.apache.tinkerpop.gremlin.structure.Edge;
import org.apache.tinkerpop.gremlin.structure.Element;
import org.apache.tinkerpop.gremlin.structure.Graph;
import org.apache.tinkerpop.gremlin.structure.Vertex;
import org.javatuples.Pair;
import org.json.JSONArray;
import org.json.JSONObject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.TimeUnit;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import static ai.grakn.graph.internal.RelationImpl.generateNewHash;
import static com.sun.corba.se.impl.util.RepositoryId.cache;
import static org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.__.outE;

/**
 * <p>
 *    The Grakn Graph Base Implementation
 * </p>
 *
 * <p>
 *     This defines how a grakn graph sits on top of a Tinkerpop {@link Graph}.
 *     It mostly act as a construction object which ensure the resulting graph conforms to the Grakn Object model.
 * </p>
 *
 * @author fppt
 *
 * @param <G> A vendor specific implementation of a Tinkerpop {@link Graph}.
 */
public abstract class AbstractGraknGraph<G extends Graph> implements GraknGraph, GraknAdmin {
    protected final Logger LOG = LoggerFactory.getLogger(AbstractGraknGraph.class);
    private final String keyspace;
    private final String engine;
    private final boolean batchLoadingEnabled;
    private final G graph;
    private final ElementFactory elementFactory;

    private final ThreadLocal<Boolean> localShowImplicitStructures = new ThreadLocal<>();
    private final ThreadLocal<ConceptLog> localConceptLog = new ThreadLocal<>();
    private final ThreadLocal<Boolean> localIsOpen = new ThreadLocal<>();
    private final ThreadLocal<String> localClosedReason = new ThreadLocal<>();
    private final ThreadLocal<Boolean> localCommitRequired = new ThreadLocal<>();
    private final ThreadLocal<Map<TypeName, Type>> localCloneCache = new ThreadLocal<>();

    private Cache<TypeName, Type> cachedOntology = CacheBuilder.newBuilder()
            .maximumSize(1000)
            .expireAfterAccess(10, TimeUnit.MINUTES)
            .build();

    public AbstractGraknGraph(G graph, String keyspace, String engine, boolean batchLoadingEnabled) {
        this.graph = graph;
        this.keyspace = keyspace;
        this.engine = engine;
        elementFactory = new ElementFactory(this);

        localIsOpen.set(true);

        if(initialiseMetaConcepts()) commitTransaction();

        this.batchLoadingEnabled = batchLoadingEnabled;
        localShowImplicitStructures.set(false);
    }

    /**
     * @param concept A concept in the graph
     * @return True if the concept has been modified in the transaction
     */
    public abstract boolean isConceptModified(ConceptImpl concept);

    /**
     *
     * @return The number of open transactions currently.
     */
    public abstract int numOpenTx();

    /**
     * Opens the thread bound transaction
     */
    public void openTransaction(){
        localIsOpen.set(true);
    }

    @Override
    public String getKeyspace(){
        return keyspace;
    }

    Cache<TypeName, Type> getCachedOntology(){
        return cachedOntology;
    }

    @Override
    public boolean isClosed(){
        return !getBooleanFromLocalThread(localIsOpen);
    }

    @Override
    public boolean implicitConceptsVisible(){
        return getBooleanFromLocalThread(localShowImplicitStructures);
    }

    private boolean getCommitRequired(){
        return getBooleanFromLocalThread(localCommitRequired);
    }

    private boolean getBooleanFromLocalThread(ThreadLocal<Boolean> local){
        Boolean value = local.get();
        if(value == null) {
            return false;
        } else {
            return value;
        }
    }

    @Override
    public void showImplicitConcepts(boolean flag){
        localShowImplicitStructures.set(flag);
    }

    @Override
    public GraknAdmin admin(){
        return this;
    }

    @Override
    public <T extends Concept> T buildConcept(Vertex vertex) {
        return getElementFactory().buildConcept(vertex);
    }

    @Override
    public boolean isBatchLoadingEnabled(){
        return batchLoadingEnabled;
    }

    @SuppressWarnings("unchecked")
    private boolean initialiseMetaConcepts(){
        if(isMetaOntologyNotInitialised()){
            Vertex type = putVertex(Schema.MetaSchema.CONCEPT.getName(), Schema.BaseType.TYPE);
            Vertex entityType = putVertex(Schema.MetaSchema.ENTITY.getName(), Schema.BaseType.ENTITY_TYPE);
            Vertex relationType = putVertex(Schema.MetaSchema.RELATION.getName(), Schema.BaseType.RELATION_TYPE);
            Vertex resourceType = putVertex(Schema.MetaSchema.RESOURCE.getName(), Schema.BaseType.RESOURCE_TYPE);
            Vertex roleType = putVertex(Schema.MetaSchema.ROLE.getName(), Schema.BaseType.ROLE_TYPE);
            Vertex ruleType = putVertex(Schema.MetaSchema.RULE.getName(), Schema.BaseType.RULE_TYPE);
            Vertex inferenceRuleType = putVertex(Schema.MetaSchema.INFERENCE_RULE.getName(), Schema.BaseType.RULE_TYPE);
            Vertex constraintRuleType = putVertex(Schema.MetaSchema.CONSTRAINT_RULE.getName(), Schema.BaseType.RULE_TYPE);

            relationType.property(Schema.ConceptProperty.IS_ABSTRACT.name(), true);
            roleType.property(Schema.ConceptProperty.IS_ABSTRACT.name(), true);
            resourceType.property(Schema.ConceptProperty.IS_ABSTRACT.name(), true);
            ruleType.property(Schema.ConceptProperty.IS_ABSTRACT.name(), true);
            entityType.property(Schema.ConceptProperty.IS_ABSTRACT.name(), true);

            relationType.addEdge(Schema.EdgeLabel.SUB.getLabel(), type);
            roleType.addEdge(Schema.EdgeLabel.SUB.getLabel(), type);
            resourceType.addEdge(Schema.EdgeLabel.SUB.getLabel(), type);
            ruleType.addEdge(Schema.EdgeLabel.SUB.getLabel(), type);
            entityType.addEdge(Schema.EdgeLabel.SUB.getLabel(), type);
            inferenceRuleType.addEdge(Schema.EdgeLabel.SUB.getLabel(), ruleType);
            constraintRuleType.addEdge(Schema.EdgeLabel.SUB.getLabel(), ruleType);

            return true;
        }

        return false;
    }

    private boolean isMetaOntologyNotInitialised(){
        return getMetaConcept() == null;
    }

    public G getTinkerPopGraph(){
        if(isClosed()){
            String reason = localClosedReason.get();
            if(reason == null){
                throw new GraphRuntimeException(ErrorMessage.GRAPH_CLOSED.getMessage(getKeyspace()));
            } else {
                throw new GraphRuntimeException(reason);
            }
        }
        return graph;
    }

    @Override
    public GraphTraversal<Vertex, Vertex> getTinkerTraversal(){
        ReadOnlyStrategy readOnlyStrategy = ReadOnlyStrategy.instance();
        return getTinkerPopGraph().traversal().asBuilder().with(readOnlyStrategy).create(getTinkerPopGraph()).V();
    }

    @Override
    public QueryBuilder graql(){
        return new QueryBuilderImpl(this);
    }

    ElementFactory getElementFactory(){
        return elementFactory;
    }

    //----------------------------------------------General Functionality-----------------------------------------------
    private EdgeImpl addEdge(Concept from, Concept to, Schema.EdgeLabel type){
        return ((ConceptImpl)from).addEdge((ConceptImpl) to, type);
    }

    @Override
    public <T extends Concept> T  getConcept(Schema.ConceptProperty key, String value) {
        return getConcept(key, value, isBatchLoadingEnabled());
    }
    private  <T extends Concept> T  getConcept(Schema.ConceptProperty key, String value, Boolean byPassDuplicates) {
        Iterator<Vertex> vertices = getTinkerTraversal().has(key.name(), value);

        if(vertices.hasNext()){
            Vertex vertex = vertices.next();
            if(!byPassDuplicates && vertices.hasNext()) {
                throw new MoreThanOneConceptException(ErrorMessage.TOO_MANY_CONCEPTS.getMessage(key.name(), value));
            }
            return getElementFactory().buildConcept(vertex);
        } else {
            return null;
        }
    }

    private Set<ConceptImpl> getConcepts(Schema.ConceptProperty key, Object value){
        Set<ConceptImpl> concepts = new HashSet<>();
        getTinkerTraversal().has(key.name(), value).
            forEachRemaining(v -> {
                concepts.add(getElementFactory().buildConcept(v));
            });
        return concepts;
    }

    ConceptLog getConceptLog() {
        ConceptLog conceptLog = localConceptLog.get();
        if(conceptLog == null){
            localConceptLog.set(conceptLog = new ConceptLog(this));
            loadOntologyCacheIntoTransactionCache(conceptLog);
        }
        return conceptLog;
    }

    private Map<TypeName, Type> getCloneCache(){
        Map<TypeName, Type> cloneCache = localCloneCache.get();
        if(cloneCache == null){
            localCloneCache.set(cloneCache = new HashMap<>());
        }
        return cloneCache;
    }

    /**
     * Given a concept log bound to a specific thread the central ontology cache is read into this concept log.
     * This method performs this operation whilst making a deep clone of the cached concepts to ensure transactions
     * do not accidentally break the central ontology cache.
     *
     * @param conceptLog The thread bound concept log to read the snapshot into.
     */
    private void loadOntologyCacheIntoTransactionCache(ConceptLog conceptLog){
        ConcurrentMap<TypeName, Type> cachedOntologySnapshot = getCachedOntology().asMap();

        //Read central cache into conceptLog cloning only base concepts. Sets clones later
        for (Type type : cachedOntologySnapshot.values()) {
            conceptLog.cacheConcept((TypeImpl) clone(type));
        }

        //Iterate through cached clones completing the cloning process.
        //This part has to be done in a separate iteration otherwise we will infinitely recurse trying to clone everything
        for (Type type : getCloneCache().values()) {
            //noinspection unchecked
            ((TypeImpl) type).copyCachedConcepts(cachedOntologySnapshot.get(type.getName()));
        }

        //Purge clone cache to save memory
        localCloneCache.remove();
    }

    /**
     *
     * @param type The type to clone
     * @param <X> The type of the concept
     * @return The newly deep cloned set
     */
    @SuppressWarnings({"unchecked", "ConstantConditions"})
    <X extends Type> X clone(X type){
        //Is a cloning even needed?
        if(getCloneCache().containsKey(type.getName())){
            return (X) getCloneCache().get(type.getName());
        }

        //If the clone has not happened then make a new one
        Type clonedType = type.copy();

        //Update clone cache so we don't clone multiple concepts in the same transaction
        getCloneCache().put(clonedType.getName(), clonedType);

        return (X) clonedType;
    }

    /**
     *
     * @param types a set of concepts to clone
     * @param <X> the type of those concepts
     * @return the set of concepts deep cloned
     */
    <X extends Type> Set<X> clone(Set<X> types){
        return types.stream().map(this::clone).collect(Collectors.toSet());
    }

    void checkOntologyMutation(){
        if(isBatchLoadingEnabled()){
            throw new GraphRuntimeException(ErrorMessage.SCHEMA_LOCKED.getMessage());
        }
    }

    //----------------------------------------------Concept Functionality-----------------------------------------------
    //------------------------------------ Construction
    Vertex addVertex(Schema.BaseType baseType){
        Vertex vertex = getTinkerPopGraph().addVertex(baseType.name());
        vertex.property(Schema.ConceptProperty.ID.name(), vertex.id().toString());
        return vertex;
    }

    private Vertex putVertex(TypeName name, Schema.BaseType baseType){
        Vertex vertex;
        ConceptImpl concept = getConcept(Schema.ConceptProperty.NAME, name.getValue());
        if(concept == null) {
            vertex = addVertex(baseType);
            vertex.property(Schema.ConceptProperty.NAME.name(), name.getValue());
        } else {
            if(!baseType.name().equals(concept.getBaseType())) {
                throw new ConceptNotUniqueException(concept, name.getValue());
            }
            vertex = concept.getVertex();
        }
        return vertex;
    }

    @Override
    public EntityType putEntityType(String name) {
        return putEntityType(TypeName.of(name));
    }

    @Override
    public EntityType putEntityType(TypeName name) {
        return putType(name, Schema.BaseType.ENTITY_TYPE,
                v -> getElementFactory().buildEntityType(v, getMetaEntityType()));
    }

    private <T extends Type> T putType(TypeName name, Schema.BaseType baseType, Function<Vertex, T> factory){
        checkOntologyMutation();
        Type type = buildType(name, () -> factory.apply(putVertex(name, baseType)));
        return validateConceptType(type, baseType, () -> {
            throw new ConceptNotUniqueException(type, name.getValue());
        });
    }

    private <T extends Concept> T validateConceptType(Concept concept, Schema.BaseType baseType, Supplier<T> invalidHandler){
        if(concept != null && baseType.getClassType().isInstance(concept)){
            //noinspection unchecked
            return (T) concept;
        } else {
            return invalidHandler.get();
        }
    }

    /**
     * A helper method which either retrieves the type from the cache or builds it using a provided supplier
     *
     * @param name The name of the type to retrieve or build
     * @param dbBuilder A method which builds the type via a DB read or write
     *
     * @return The type which was either cached or built via a DB read or write
     */
    private Type buildType(TypeName name, Supplier<Type> dbBuilder){
        if(getConceptLog().isTypeCached(name)){
            return getConceptLog().getCachedType(name);
        } else {
            return dbBuilder.get();
        }
    }

    @Override
    public RelationType putRelationType(String name) {
        return putRelationType(TypeName.of(name));
    }

    @Override
    public RelationType putRelationType(TypeName name) {
        return putType(name, Schema.BaseType.RELATION_TYPE,
                v -> getElementFactory().buildRelationType(v, getMetaRelationType(), Boolean.FALSE)).asRelationType();
    }

    RelationType putRelationTypeImplicit(TypeName name) {
        return putType(name, Schema.BaseType.RELATION_TYPE,
                v -> getElementFactory().buildRelationType(v, getMetaRelationType(), Boolean.TRUE)).asRelationType();
    }

    @Override
    public RoleType putRoleType(String name) {
        return putRoleType(TypeName.of(name));
    }

    @Override
    public RoleType putRoleType(TypeName name) {
        return putType(name, Schema.BaseType.ROLE_TYPE,
                v -> getElementFactory().buildRoleType(v, getMetaRoleType(), Boolean.FALSE)).asRoleType();
    }

    RoleType putRoleTypeImplicit(TypeName name) {
        return putType(name, Schema.BaseType.ROLE_TYPE,
                v -> getElementFactory().buildRoleType(v, getMetaRoleType(), Boolean.TRUE)).asRoleType();
    }

    @Override
    public <V> ResourceType<V> putResourceType(String name, ResourceType.DataType<V> dataType) {
        return putResourceType(TypeName.of(name), dataType);
    }

    @SuppressWarnings("unchecked")
    @Override
    public <V> ResourceType<V> putResourceType(TypeName name, ResourceType.DataType<V> dataType) {
        return putResourceType(name, dataType, Boolean.FALSE);
    }

    @Override
    public <V> ResourceType <V> putResourceTypeUnique(String name, ResourceType.DataType<V> dataType){
        return putResourceTypeUnique(TypeName.of(name), dataType);
    }

    @SuppressWarnings("unchecked")
    @Override
    public <V> ResourceType<V> putResourceTypeUnique(TypeName name, ResourceType.DataType<V> dataType) {
        return putResourceType(name, dataType, Boolean.TRUE);
    }

    private <V> ResourceType <V> putResourceType(TypeName name, ResourceType.DataType<V> dataType, Boolean isUnique){

        @SuppressWarnings("unchecked")
        ResourceType<V> resourceType = putType(name, Schema.BaseType.RESOURCE_TYPE,
                v -> getElementFactory().buildResourceType(v, getMetaResourceType(), dataType, isUnique)).asResourceType();

        //These checks is needed here because caching will return a type by name without checking the datatype
        if(Schema.MetaSchema.isMetaName(name)) {
            throw new ConceptException(ErrorMessage.META_TYPE_IMMUTABLE.getMessage(name));
        } else if(!dataType.equals(resourceType.getDataType())){
            throw new InvalidConceptValueException(ErrorMessage.IMMUTABLE_VALUE.getMessage(resourceType.getDataType(), resourceType, dataType, Schema.ConceptProperty.DATA_TYPE.name()));
        } else if(resourceType.isUnique() ^ isUnique){
            throw new InvalidConceptValueException(ErrorMessage.IMMUTABLE_VALUE.getMessage(resourceType.isUnique(), resourceType, isUnique, Schema.ConceptProperty.IS_UNIQUE.name()));
        }

        return resourceType;
    }

    @Override
    public RuleType putRuleType(String name) {
        return putRuleType(TypeName.of(name));
    }

    @Override
    public RuleType putRuleType(TypeName name) {
        return putType(name, Schema.BaseType.RULE_TYPE,
                v ->  getElementFactory().buildRuleType(v, getMetaRuleType()));
    }

    //------------------------------------ Lookup
    public <T extends Concept> T getConceptByBaseIdentifier(Object baseIdentifier) {
        GraphTraversal<Vertex, Vertex> traversal = getTinkerPopGraph().traversal().V(baseIdentifier);
        if (traversal.hasNext()) {
            return getElementFactory().buildConcept(traversal.next());
        } else {
            return null;
        }
    }

    @Override
    public <T extends Concept> T getConcept(ConceptId id) {
        if(getConceptLog().isConceptCached(id)){
            return getConceptLog().getCachedConcept(id);
        } else {
            return getConcept(Schema.ConceptProperty.ID, id.getValue());
        }
    }
    private <T extends Type> T getTypeByName(TypeName name, Schema.BaseType baseType){
        Type type = buildType(name, ()->getConcept(Schema.ConceptProperty.NAME, name.getValue()));
        return validateConceptType(type, baseType, () -> null);
    }

    @Override
    public <V> Collection<Resource<V>> getResourcesByValue(V value) {
        HashSet<Resource<V>> resources = new HashSet<>();
        ResourceType.DataType dataType = ResourceType.DataType.SUPPORTED_TYPES.get(value.getClass().getTypeName());

        getConcepts(dataType.getConceptProperty(), value).forEach(concept -> {
            if(concept != null && concept.isResource()) {
                //noinspection unchecked
                resources.add(concept.asResource());
            }
        });

        return resources;
    }

    @Override
    public <T extends Type> T getType(TypeName name) {
        return getTypeByName(name, Schema.BaseType.TYPE);
    }

    @Override
    public EntityType getEntityType(String name) {
        return getTypeByName(TypeName.of(name), Schema.BaseType.ENTITY_TYPE);
    }

    @Override
    public RelationType getRelationType(String name) {
        return getTypeByName(TypeName.of(name), Schema.BaseType.RELATION_TYPE);
    }

    @Override
    public <V> ResourceType<V> getResourceType(String name) {
        return getTypeByName(TypeName.of(name), Schema.BaseType.RESOURCE_TYPE);
    }

    @Override
    public RoleType getRoleType(String name) {
        return getTypeByName(TypeName.of(name), Schema.BaseType.ROLE_TYPE);
    }

    @Override
    public RuleType getRuleType(String name) {
        return getTypeByName(TypeName.of(name), Schema.BaseType.RULE_TYPE);
    }

    @Override
    public Type getMetaConcept() {
        return getTypeByName(Schema.MetaSchema.CONCEPT.getName(), Schema.BaseType.TYPE);
    }

    @Override
    public RelationType getMetaRelationType() {
        return getTypeByName(Schema.MetaSchema.RELATION.getName(), Schema.BaseType.RELATION_TYPE);
    }

    @Override
    public RoleType getMetaRoleType() {
        return getTypeByName(Schema.MetaSchema.ROLE.getName(), Schema.BaseType.ROLE_TYPE);
    }

    @Override
    public ResourceType getMetaResourceType() {
        return getTypeByName(Schema.MetaSchema.RESOURCE.getName(), Schema.BaseType.RESOURCE_TYPE);
    }

    @Override
    public EntityType getMetaEntityType() {
        return getTypeByName(Schema.MetaSchema.ENTITY.getName(), Schema.BaseType.ENTITY_TYPE);
    }

    @Override
    public RuleType getMetaRuleType(){
        return getTypeByName(Schema.MetaSchema.RULE.getName(), Schema.BaseType.RULE_TYPE);
    }

    @Override
    public RuleType getMetaRuleInference() {
        return getTypeByName(Schema.MetaSchema.INFERENCE_RULE.getName(), Schema.BaseType.RULE_TYPE);
    }

    @Override
    public RuleType getMetaRuleConstraint() {
        return getTypeByName(Schema.MetaSchema.CONSTRAINT_RULE.getName(), Schema.BaseType.RULE_TYPE);
    }

    //-----------------------------------------------Casting Functionality----------------------------------------------
    //------------------------------------ Construction
    private CastingImpl addCasting(RoleTypeImpl role, InstanceImpl rolePlayer){
        CastingImpl casting = getElementFactory().buildCasting(addVertex(Schema.BaseType.CASTING), role).setHash(role, rolePlayer);
        if(rolePlayer != null) {
            EdgeImpl castingToRolePlayer = addEdge(casting, rolePlayer, Schema.EdgeLabel.ROLE_PLAYER); // Casting to RolePlayer
            castingToRolePlayer.setProperty(Schema.EdgeProperty.ROLE_TYPE, role.getId().getValue());
        }
        return casting;
    }
    CastingImpl addCasting(RoleTypeImpl role, InstanceImpl rolePlayer, RelationImpl relation){
        CastingImpl foundCasting  = null;
        if(rolePlayer != null) {
            foundCasting = getCasting(role, rolePlayer);
        }

        if(foundCasting == null){
            foundCasting = addCasting(role, rolePlayer);
        }

        // Relation To Casting
        EdgeImpl relationToCasting = relation.putEdge(foundCasting, Schema.EdgeLabel.CASTING);
        relationToCasting.setProperty(Schema.EdgeProperty.ROLE_TYPE, role.getId().getValue());
        getConceptLog().trackConceptForValidation(relation); //The relation is explicitly tracked so we can look them up without committing

        putShortcutEdges(relation, relation.type(), foundCasting);

        return foundCasting;
    }

    private CastingImpl getCasting(RoleTypeImpl role, InstanceImpl rolePlayer){
        try {
            String hash = CastingImpl.generateNewHash(role, rolePlayer);
            ConceptImpl concept = getConcept(Schema.ConceptProperty.INDEX, hash);
            if (concept != null) {
                return concept.asCasting();
            } else {
                return null;
            }
        } catch(GraphRuntimeException e){
            throw new MoreThanOneConceptException(ErrorMessage.TOO_MANY_CASTINGS.getMessage(role, rolePlayer));
        }
    }

    private void putShortcutEdges(RelationImpl relation, RelationType relationType, CastingImpl newCasting){
        Map<RoleType, Set<Instance>> roleMap = relation.allRolePlayers();

        //This ensures the latest casting is taken into account when transferring relations
        roleMap.computeIfAbsent(newCasting.getRole(), (k) -> new HashSet<>()).add(newCasting.getRolePlayer());

        Set<CastingImpl> castings = relation.getMappingCasting();

        for (CastingImpl fromCasting : castings) {
            RoleType fromRole = fromCasting.getRole();
            Instance from = fromCasting.getRolePlayer();

            for (CastingImpl toCasting : castings) {
                RoleType toRole = toCasting.getRole();
                Instance to = toCasting.getRolePlayer();

                if (from != null && to != null &&  (!fromRole.equals(toRole) || !from.equals(to)) ) {
                    putShortcutEdge(relation, relationType, fromRole, from, toRole, to);
                }
            }
        }
    }

    private void putShortcutEdge(Relation  relation, RelationType  relationType, RoleType fromRole, Instance from, RoleType  toRole, Instance to){
        InstanceImpl fromRolePlayer = (InstanceImpl) from;
        InstanceImpl toRolePlayer = (InstanceImpl) to;

        String hash = calculateShortcutHash(relation, relationType, fromRole, fromRolePlayer, toRole, toRolePlayer);
        boolean exists = getTinkerPopGraph().traversal().V(fromRolePlayer.getId().getRawValue()).
                    local(outE(Schema.EdgeLabel.SHORTCUT.getLabel()).has(Schema.EdgeProperty.SHORTCUT_HASH.name(), hash)).
                    hasNext();

        if (!exists) {
            EdgeImpl edge = addEdge(fromRolePlayer, toRolePlayer, Schema.EdgeLabel.SHORTCUT);
            edge.setProperty(Schema.EdgeProperty.RELATION_TYPE_NAME, relationType.getName().getValue());
            edge.setProperty(Schema.EdgeProperty.RELATION_ID, relation.getId().getValue());

            if (fromRolePlayer.getId() != null) {
                edge.setProperty(Schema.EdgeProperty.FROM_ID, fromRolePlayer.getId().getValue());
            }
            edge.setProperty(Schema.EdgeProperty.FROM_ROLE_NAME, fromRole.getName().getValue());

            if (toRolePlayer.getId() != null) {
                edge.setProperty(Schema.EdgeProperty.TO_ID, toRolePlayer.getId().getValue());
            }
            edge.setProperty(Schema.EdgeProperty.TO_ROLE_NAME, toRole.getName().getValue());

            edge.setProperty(Schema.EdgeProperty.FROM_TYPE_NAME, fromRolePlayer.type().getName().getValue());
            edge.setProperty(Schema.EdgeProperty.TO_TYPE_NAME, toRolePlayer.type().getName().getValue());
            edge.setProperty(Schema.EdgeProperty.SHORTCUT_HASH, hash);
        }
    }

    private String calculateShortcutHash(Relation relation, RelationType relationType, RoleType fromRole, Instance fromRolePlayer, RoleType toRole, Instance toRolePlayer){
        String hash = "";
        String relationIdValue = relationType.getId().getValue();
        String fromIdValue = fromRolePlayer.getId().getValue();
        String fromRoleValue = fromRole.getId().getValue();
        String toIdValue = toRolePlayer.getId().getValue();
        String toRoleValue = toRole.getId().getValue();
        String assertionIdValue = relation.getId().getValue();

        if(relationIdValue != null) hash += relationIdValue;
        if(fromIdValue != null) hash += fromIdValue;
        if(fromRoleValue != null) hash += fromRoleValue;
        if(toIdValue != null) hash += toIdValue;
        if(toRoleValue != null) hash += toRoleValue;
        hash += String.valueOf(assertionIdValue);

        return hash;
    }

    private RelationImpl getRelation(RelationType relationType, Map<RoleType, Set<Instance>> roleMap){
        String hash = generateNewHash(relationType, roleMap);
        RelationImpl concept = getConceptLog().getCachedRelation(hash);

        if(concept == null) {
            concept = getConcept(Schema.ConceptProperty.INDEX, hash);
        }
        return concept;
    }

    /**
     * Clears the graph completely.
     */
    @Override
    public void clear() {
        EngineCommunicator.contactEngine(getCommitLogEndPoint(), REST.HttpConn.DELETE_METHOD);
        innerClear();
    }

    @Override
    public void clear(ConceptCache conceptCache) {
        innerClear();
        conceptCache.clearAllJobs(getKeyspace());
    }

    private void innerClear(){
        clearGraph();
        closeGraph(ErrorMessage.CLOSED_CLEAR.getMessage());
    }

    //This is overridden by vendors for more efficient clearing approaches
    protected void clearGraph(){
        getTinkerPopGraph().traversal().V().drop().iterate();
    }

    /**
     * Closes the current graph, rendering it unusable.
     */
    @Override
    public void close() throws GraknValidationException {
        if(getCommitRequired()){
            commit();
        }
        localCommitRequired.remove();
        closeGraph(ErrorMessage.GRAPH_PERMANENTLY_CLOSED.getMessage(getKeyspace()));
    }

    private void closeGraph(String closedReason){
        try {
            graph.tx().close();
        } catch (UnsupportedOperationException e) {
            //Ignored for Tinker
        }
        localClosedReason.set(closedReason);
        localIsOpen.set(false);
        clearLocalVariables();
    }

    /**
     * Sets a thread local flag indicating that a commit is required when cloding the graph.
     */
    public void commitOnClose(){
        localCommitRequired.set(true);
    }

    /**
     * Commits the graph
     * @throws GraknValidationException when the graph does not conform to the object concept
     */
    public void commit() throws GraknValidationException {
        commit(this::submitCommitLogs);
    }

    /**
     * Commits the graph and adds concepts for post processing directly to the cache bypassing the REST API.
     *
     * @param conceptCache The concept Cache to store concepts in for processing later
     * @throws GraknValidationException when the graph does not conform to the object concept
     */
    @Override
    public void commit(ConceptCache conceptCache) throws GraknValidationException{
        commit((castings, resources) -> {
            if(conceptCache != null) {
                castings.forEach(pair -> conceptCache.addJobCasting(getKeyspace(), pair.getValue0(), pair.getValue1()));
                resources.forEach(pair -> conceptCache.addJobResource(getKeyspace(), pair.getValue0(), pair.getValue1()));
            }
        });
    }

    /**
     * Commits to the graph without submitting any commit logs.
     *
     * @throws GraknValidationException when the graph does not conform to the object concept
     */
    @Override
    public void commitNoLogs() throws GraknValidationException {
        commit((x, y) -> {});
    }

    private void clearLocalVariables(){
        getConceptLog().writeToCentralCache(false);
        localConceptLog.remove();
    }

    public void commit(BiConsumer<Set<Pair<String, ConceptId>>, Set<Pair<String,ConceptId>>> conceptLogger) throws GraknValidationException {
        validateGraph();

        Set<Pair<String, ConceptId>> castings = getConceptLog().getModifiedCastings().stream().
                map(casting -> new Pair<>(casting.getIndex(), casting.getId())).collect(Collectors.toSet());

        Set<Pair<String, ConceptId>> resources = getConceptLog().getModifiedResources().stream().
                map(resource -> new Pair<>(resource.getIndex(), resource.getId())).collect(Collectors.toSet());


        LOG.trace("Graph is valid. Committing graph . . . ");
        commitTransaction();

        LOG.trace("Graph committed.");
        getConceptLog().writeToCentralCache(true);
        clearLocalVariables();

        //No post processing should ever be done for the system keyspace
        if(!keyspace.equalsIgnoreCase(SystemKeyspace.SYSTEM_GRAPH_NAME) && (!castings.isEmpty() || !resources.isEmpty())) {
            conceptLogger.accept(castings, resources);
        }
    }

    protected void commitTransaction(){
        try {
            getTinkerPopGraph().tx().commit();
        } catch (UnsupportedOperationException e){
            //IGNORED
        }
    }


    void validateGraph() throws GraknValidationException {
        Validator validator = new Validator(this);
        if (!validator.validate()) {
            List<String> errors = validator.getErrorsFound();
            StringBuilder error = new StringBuilder();
            error.append(ErrorMessage.VALIDATION.getMessage(errors.size()));
            for (String s : errors) {
                error.append(s);
            }
            throw new GraknValidationException(error.toString());
        }
    }

    private void submitCommitLogs(Set<Pair<String, ConceptId>> castings, Set<Pair<String, ConceptId>> resources){
        JSONArray jsonArray = new JSONArray();

        loadCommitLogConcepts(jsonArray, Schema.BaseType.CASTING, castings);
        loadCommitLogConcepts(jsonArray, Schema.BaseType.RESOURCE, resources);

        JSONObject postObject = new JSONObject();
        postObject.put("concepts", jsonArray);
        LOG.debug("Response from engine [" + EngineCommunicator.contactEngine(getCommitLogEndPoint(), REST.HttpConn.POST_METHOD, postObject.toString()) + "]");

    }
    private void loadCommitLogConcepts(JSONArray jsonArray, Schema.BaseType baseType, Set<Pair<String, ConceptId>> concepts){
        concepts.forEach(concept -> {
            JSONObject jsonObject = new JSONObject();
            jsonObject.put(REST.Request.COMMIT_LOG_TYPE, baseType.name());
            jsonObject.put(REST.Request.COMMIT_LOG_INDEX, concept.getValue0());
            jsonObject.put(REST.Request.COMMIT_LOG_ID, concept.getValue1().getValue());
            jsonArray.put(jsonObject);
        });
    }
    private String getCommitLogEndPoint(){
        if(Grakn.IN_MEMORY.equals(engine)) {
            return Grakn.IN_MEMORY;
        }
        return engine + REST.WebPath.COMMIT_LOG_URI + "?" + REST.Request.KEYSPACE_PARAM + "=" + keyspace;
    }

    public void validVertex(Vertex vertex){
        if(vertex == null) {
            throw new IllegalStateException("The provided vertex is null");
        }

        //Sample read
        vertex.property(Schema.ConceptProperty.ID.name()).isPresent();
    }

    //------------------------------------------ Fixing Code for Postprocessing ----------------------------------------
    /**
     * Merges the provided duplicate castings.
     *
     * @param castingVertexIds The vertex Ids of the duplicate castings
     * @return if castings were merged and a commit is required.
     */
    @Override
    public boolean fixDuplicateCastings(String index, Set<ConceptId> castingVertexIds){
        Set<CastingImpl> castings = castingVertexIds.stream().
                map(id -> this.<CastingImpl>getConceptByBaseIdentifier(id.getValue())).collect(Collectors.toSet());
        if(castings.size() >= 1){
            //This is done to ensure we merge into the indexed casting. Needs to be cleaned up though
            CastingImpl mainCasting = getConcept(Schema.ConceptProperty.INDEX, index, true);
            castings.remove(mainCasting);

            //Fix the duplicates
            Set<RelationImpl> duplicateRelations = mergeCastings(mainCasting, castings);

            //Remove Redundant Relations
            deleteRelations(duplicateRelations);

            return true;
        }

        return false;
    }

    /**
     *
     * @param relations The duplicate relations to be merged
     */
    private void deleteRelations(Set<RelationImpl> relations){
        for (RelationImpl relation : relations) {
            String relationID = relation.getId().getValue();

            //Kill Shortcut Edges
            relation.rolePlayers().forEach(instance -> {
                if(instance != null) {
                    List<Edge> edges = getTinkerTraversal().
                            hasId(instance.getId().getValue()).
                            bothE(Schema.EdgeLabel.SHORTCUT.getLabel()).
                            has(Schema.EdgeProperty.RELATION_ID.name(), relationID).toList();

                    edges.forEach(Element::remove);
                }
            });

            relation.deleteNode();
        }
    }

    /**
     *
     * @param mainCasting The main casting to absorb all of the edges
     * @param castings The castings to whose edges will be transferred to the main casting and deleted.
     * @return A set of possible duplicate relations.
     */
    private Set<RelationImpl> mergeCastings(CastingImpl mainCasting, Set<CastingImpl> castings){
        RoleType role = mainCasting.getRole();
        Set<RelationImpl> relations = mainCasting.getRelations();
        Set<RelationImpl> relationsToClean = new HashSet<>();

        for (CastingImpl otherCasting : castings) {
            //Transfer assertion edges
            for(RelationImpl otherRelation : otherCasting.getRelations()){
                boolean transferEdge = true;

                //Check if an equivalent Relation is already connected to this casting. This could be a slow process
                for(Relation originalRelation: relations){
                    if(relationsEqual(originalRelation, otherRelation)){
                        relationsToClean.add(otherRelation);
                        transferEdge = false;
                        break;
                    }
                }

                //Perform the transfer
                if(transferEdge) {
                    EdgeImpl assertionToCasting = addEdge(otherRelation, mainCasting, Schema.EdgeLabel.CASTING);
                    assertionToCasting.setProperty(Schema.EdgeProperty.ROLE_TYPE, role.getId().getValue());
                }
            }

            getConceptLog().removeConcept(otherCasting);
            getTinkerPopGraph().traversal().V(otherCasting.getId().getRawValue()).next().remove();
        }

        return relationsToClean;
    }

    /**
     *
     * @param mainRelation The main relation to compare
     * @param otherRelation The relation to compare it with
     * @return True if the roleplayers of the relations are the same.
     */
    private boolean relationsEqual(Relation mainRelation, Relation otherRelation){
        return mainRelation.allRolePlayers().equals(otherRelation.allRolePlayers()) &&
                mainRelation.type().equals(otherRelation.type());
    }

    /**
     *
     * @param resourceVertexIds The resource vertex ids which need to be merged.
     * @return True if a commit is required.
     */
    @Override
    public boolean fixDuplicateResources(String index, Set<ConceptId> resourceVertexIds){
        Set<ResourceImpl> duplicates = resourceVertexIds.stream().
                map(id -> this.<ResourceImpl>getConceptByBaseIdentifier(id.getValue())).collect(Collectors.toSet());

        if(duplicates.size() >= 1){
            //This is done to ensure we merge into the indexed resource. Needs to be cleaned up though
            ResourceImpl<?> mainResource = getConcept(Schema.ConceptProperty.INDEX, index, true);
            duplicates.remove(mainResource);
            Iterator<ResourceImpl> it = duplicates.iterator();

            while(it.hasNext()){
                ResourceImpl<?> otherResource = it.next();
                Collection<Relation> otherRelations = otherResource.relations();

                //Delete the shortcut edges of the resource we going to delete.
                //This is so we can copy them uniquely later
                otherResource.getEdgesOfType(Direction.BOTH, Schema.EdgeLabel.SHORTCUT).forEach(EdgeImpl::delete);

                //Cope the actual relation
                for (Relation otherRelation : otherRelations) {
                    copyRelation(mainResource, otherResource, (RelationImpl) otherRelation);
                }

                otherResource.delete();
            }

            return true;
        }

        return false;
    }

    /**
     *
     * @param main The main instance to possibly acquire a new relation
     * @param other The other instance which already posses the relation
     * @param otherRelation The other relation to potentially be absorbed
     */
    private void copyRelation(ResourceImpl main, ResourceImpl<?> other, RelationImpl otherRelation){
        RelationType relationType = otherRelation.type();
        Set<RoleTypeImpl> roleTypesOfResource = new HashSet<>(); //All the role types which the resource must play by the end
        Map<RoleType, Set<Instance>> allRolePlayers = otherRelation.allRolePlayers();

        //Replace all occurrences of other with main. That we we can quickly find out if the relation on main exists
        for (Map.Entry<RoleType, Set<Instance>> allRolePlayerEntries : allRolePlayers.entrySet()) {

            Iterator<Instance> it = allRolePlayerEntries.getValue().iterator();
            while (it.hasNext()){
                Instance instance = it.next();
                if(instance.isResource() && instance.asResource().getValue().equals(other.getValue())){//If the values are the same replace with main
                    it.remove();
                    allRolePlayerEntries.getValue().add(main);
                    roleTypesOfResource.add((RoleTypeImpl) allRolePlayerEntries.getKey());
                }
            }
        }

        //See if a duplicate relation already exists
        RelationImpl foundRelation = getRelation(relationType, allRolePlayers);

        if(foundRelation != null){//If it exists delete the other one
            otherRelation.deleteNode(); //Raw deletion because the castings should remain
        } else { //If it doesn't exist transfer the edge to the relevant casting node
            foundRelation = otherRelation;
            roleTypesOfResource.forEach(roleType -> addCasting(roleType, main, otherRelation));
        }

        //Explicitly track this new relation so we don't create duplicates
        String newHash = generateNewHash(relationType, allRolePlayers);
        getConceptLog().getModifiedRelations().put(newHash, foundRelation);
    }
}
