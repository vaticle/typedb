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

package ai.grakn.util;

import ai.grakn.concept.Entity;
import ai.grakn.concept.EntityType;
import ai.grakn.concept.OntologyElement;
import ai.grakn.concept.Relation;
import ai.grakn.concept.RelationType;
import ai.grakn.concept.Resource;
import ai.grakn.concept.ResourceType;
import ai.grakn.concept.RoleType;
import ai.grakn.concept.Rule;
import ai.grakn.concept.RuleType;
import ai.grakn.concept.Type;
import ai.grakn.concept.TypeId;
import ai.grakn.concept.TypeLabel;
import org.apache.tinkerpop.gremlin.structure.Vertex;

import javax.annotation.CheckReturnValue;

/**
 * A type enum which restricts the types of links/concepts which can be created
 *
 * @author Filipe Teixeira
 */
public final class Schema {
    private Schema() {
        throw new UnsupportedOperationException();
    }

    /**
     * The different types of edges between vertices
     */
    public enum EdgeLabel {
        ISA("isa"),
        SUB("sub"),
        RELATES("relates"),
        PLAYS("plays"),
        HAS_SCOPE("has-scope"),
        HYPOTHESIS("hypothesis"),
        CONCLUSION("conclusion"),
        SHORTCUT("shortcut"),
        SHARD("shard");

        private final String label;

        EdgeLabel(String l) {
            label = l;
        }

        @CheckReturnValue
        public String getLabel() {
            return label;
        }
    }

    /**
     * The concepts which represent our internal schema
     */
    public enum MetaSchema {
        THING("thing", 1),
        ENTITY("entity", 2),
        ROLE("role", 3),
        RESOURCE("resource", 4),
        RELATION("relation", 5),
        RULE("rule", 6),
        INFERENCE_RULE("inference-rule", 7),
        CONSTRAINT_RULE("constraint-rule", 8);


        private final TypeLabel label;
        private final TypeId id;

        MetaSchema(String s, int i) {
            label = TypeLabel.of(s);
            id = TypeId.of(i);
        }

        @CheckReturnValue
        public TypeLabel getLabel() {
            return label;
        }

        @CheckReturnValue
        public TypeId getId(){
            return id;
        }

        @CheckReturnValue
        public static boolean isMetaLabel(TypeLabel label) {
            for (MetaSchema metaSchema : MetaSchema.values()) {
                if (metaSchema.getLabel().equals(label)) return true;
            }
            return false;
        }
    }

    /**
     * Base Types reflecting the possible objects in the concept
     */
    public enum BaseType {
        //Ontology Elements
        ONTOLOGY_ELEMENT(OntologyElement.class),
        TYPE(Type.class),
        ROLE_TYPE(RoleType.class),
        RELATION_TYPE(RelationType.class),
        RESOURCE_TYPE(ResourceType.class),
        ENTITY_TYPE(EntityType.class),
        RULE_TYPE(RuleType.class),

        //Instances
        RELATION(Relation.class),
        ENTITY(Entity.class),
        RESOURCE(Resource.class),
        RULE(Rule.class),

        //Internal
        SHARD(Vertex.class);

        private final Class classType;

        BaseType(Class classType){
            this.classType = classType;
        }

        @CheckReturnValue
        public Class getClassType(){
            return classType;
        }
    }

    /**
     * An enum which defines the non-unique mutable properties of the concept.
     */
    public enum VertexProperty {
        //Unique Properties
        TYPE_LABEL(String.class), INDEX(String.class), ID(String.class), TYPE_ID(Integer.class),

        //Other Properties
        INSTANCE_TYPE_ID(Integer.class), IS_ABSTRACT(Boolean.class), IS_IMPLICIT(Boolean.class),
        REGEX(String.class), DATA_TYPE(String.class), SHARD_COUNT(Long.class), CURRENT_TYPE_ID(Integer.class),
        RULE_LHS(String.class), RULE_RHS(String.class), CURRENT_SHARD(String.class),

        //Supported Data Types
        VALUE_STRING(String.class), VALUE_LONG(Long.class),
        VALUE_DOUBLE(Double.class), VALUE_BOOLEAN(Boolean.class),
        VALUE_INTEGER(Integer.class), VALUE_FLOAT(Float.class),
        VALUE_DATE(Long.class);

        private final Class dataType;

        VertexProperty(Class dataType) {
            this.dataType = dataType;
        }

        @CheckReturnValue
        public Class getDataType() {
            return dataType;
        }
    }

    /**
     * A property enum defining the possible labels that can go on the edge label.
     */
    public enum EdgeProperty {
        ROLE_TYPE_ID(Integer.class),
        RELATION_TYPE_ID(Integer.class),
        REQUIRED(Boolean.class);

        private final Class dataType;

        EdgeProperty(Class dataType) {
            this.dataType = dataType;
        }

        @CheckReturnValue
        public Class getDataType() {
            return dataType;
        }
    }

    /**
     * This stores the schema which is required when implicitly creating roles for the has-resource methods
     */
    public enum ImplicitType {
        /**
         * The label of the generic has-resource relationship, used for attaching resources to instances with the 'has' syntax
         */
        HAS("has-%s"),

        /**
         * The label of a role in has-resource, played by the owner of the resource
         */
        HAS_OWNER("has-%s-owner"),

        /**
         * The label of a role in has-resource, played by the resource
         */
        HAS_VALUE("has-%s-value"),

        /**
         * The label of the generic key relationship, used for attaching resources to instances with the 'has' syntax and additionally constraining them to be unique
         */
        KEY("key-%s"),

        /**
         * The label of a role in key, played by the owner of the key
         */
        KEY_OWNER("key-%s-owner"),

        /**
         * The label of a role in key, played by the resource
         */
        KEY_VALUE("key-%s-value");

        private final String label;

        ImplicitType(String label) {
            this.label = label;
        }

        @CheckReturnValue
        public TypeLabel getLabel(TypeLabel resourceType) {
            return resourceType.map(resource -> String.format(label, resource));
        }

        @CheckReturnValue
        public TypeLabel getLabel(String resourceType) {
            return TypeLabel.of(String.format(label, resourceType));
        }
    }

    /**
     * An enum representing analytics schema elements
     */
    public enum Analytics {

        DEGREE("degree"),
        CLUSTER("cluster");

        private final String label;

        Analytics(String label) {
            this.label = label;
        }

        @CheckReturnValue
        public TypeLabel getLabel() {
            return TypeLabel.of(label);
        }
    }

    /**
     *
     * @param typeLabel The resource type label
     * @param value The value of the resource
     * @return A unique id for the resource
     */
    @CheckReturnValue
    public static String generateResourceIndex(TypeLabel typeLabel, String value){
        return Schema.BaseType.RESOURCE.name() + "-" + typeLabel + "-" + value;
    }
}
