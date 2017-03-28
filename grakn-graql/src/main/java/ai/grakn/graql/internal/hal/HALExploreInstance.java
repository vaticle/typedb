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

package ai.grakn.graql.internal.hal;

import ai.grakn.concept.Concept;
import ai.grakn.util.REST;
import com.theoryinpractise.halbuilder.api.Representation;
import com.theoryinpractise.halbuilder.api.RepresentationFactory;
import com.theoryinpractise.halbuilder.standard.StandardRepresentationFactory;

import static ai.grakn.graql.internal.hal.HALUtils.DIRECTION_PROPERTY;
import static ai.grakn.graql.internal.hal.HALUtils.EXPLORE_CONCEPT_LINK;
import static ai.grakn.graql.internal.hal.HALUtils.OUTBOUND_EDGE;
import static ai.grakn.graql.internal.hal.HALUtils.generateConceptState;

/**
 * Class used to build the HAL representation of a given concept.
 */

class HALExploreInstance {

    private final RepresentationFactory factory;
    private final Representation halResource;
    private final String keyspace;
    private final int limit;
    private final int offset;
    private final String resourceLinkPrefix;


    HALExploreInstance(Concept concept, String keyspace, int offset, int limit) {

        //building HAL concepts using: https://github.com/HalBuilder/halbuilder-core
        resourceLinkPrefix = REST.WebPath.CONCEPT_BY_ID_URI;
        this.keyspace = keyspace;
        this.offset = offset;
        this.limit = limit;
        factory = new StandardRepresentationFactory();
        halResource = factory.newRepresentation(resourceLinkPrefix + concept.getId() + getURIParams());

        generateStateAndLinks(halResource, concept);
        populateEmbedded(halResource, concept);

    }

    private String getURIParams() {
        // If limit -1, we don't append the limit parameter to the URI string
        String limitParam = (this.limit >= 0) ? "&limit=" + this.limit : "";
        return "?keyspace=" + this.keyspace + "&offset=" + this.offset + limitParam;
    }

    private void generateStateAndLinks(Representation resource, Concept concept) {
        resource.withLink(EXPLORE_CONCEPT_LINK, REST.WebPath.CONCEPT_BY_ID_EXPLORE_URI + concept.getId() + getURIParams());
        generateConceptState(resource, concept);
    }

    private void populateEmbedded(Representation halResource, Concept concept) {

        // Instance resources
        concept.asInstance().resources().forEach(currentResource -> {
            Representation embeddedResource = factory.newRepresentation(resourceLinkPrefix + currentResource.getId() + getURIParams())
                    .withProperty(DIRECTION_PROPERTY, OUTBOUND_EDGE);
            generateStateAndLinks(embeddedResource, currentResource);
            halResource.withRepresentation(currentResource.type().getName().getValue(), embeddedResource);
        });
    }


    public String render() {
        return halResource.toString(RepresentationFactory.HAL_JSON);
    }
}
