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
package ai.grakn.client;

import ai.grakn.Keyspace;
import ai.grakn.graql.Query;
import static ai.grakn.util.REST.Request.Graql.INFER;
import static ai.grakn.util.REST.Request.Graql.MATERIALISE;
import static ai.grakn.util.REST.Request.Graql.MULTI;
import static ai.grakn.util.REST.Request.KEYSPACE;
import static ai.grakn.util.REST.Response.ContentType.APPLICATION_JSON_GRAQL;
import static ai.grakn.util.REST.Response.ContentType.APPLICATION_TEXT;
import ai.grakn.util.SimpleURI;
import com.google.common.collect.ImmutableMap;
import com.sun.jersey.api.client.Client;
import com.sun.jersey.api.client.ClientResponse;
import java.net.URI;
import java.util.List;
import java.util.Optional;
import javax.ws.rs.core.Response.Status;
import javax.ws.rs.core.Response.Status.Family;
import javax.ws.rs.core.UriBuilder;
import mjson.Json;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Grakn http client. Extend this for more http endpoint.
 *
 * @author Domenico Corapi
 */
public class GraknClient {
    private final Logger LOG = LoggerFactory.getLogger(GraknClient.class);

    private final Client asyncHttpClient;
    private final String graqlExecuteURL;
    private final String keyspaceURL;

    public GraknClient(SimpleURI url)  {
        this.asyncHttpClient = Client.create();
        String urlWithSchema = url.toStringWithSchema();
        this.graqlExecuteURL = urlWithSchema + "/kb/graql/execute";
        this.keyspaceURL = urlWithSchema + "/keyspaces/{keyspace}";
    }

    public List<QueryResponse> graqlExecute(List<Query<?>> queryList, String keyspace)
            throws GraknClientException {
        String body = queryList.stream().map(Object::toString).reduce("; ", String::concat).substring(2);
        URI fullURI = UriBuilder.fromPath(graqlExecuteURL)
                .queryParam(MATERIALISE, "false")
                .queryParam(INFER, "false")
                .queryParam(MULTI, "true")
                .queryParam(KEYSPACE, keyspace).build();
        ClientResponse response = asyncHttpClient.resource(fullURI.toString())
                .accept(APPLICATION_JSON_GRAQL)
                .type(APPLICATION_TEXT)
                .post(ClientResponse.class, body);
            int statusCode = response.getStatus();
        String entity = response.getEntity(String.class);
        if (!response.getStatusInfo().getFamily().equals(Family.SUCCESSFUL)) {
            throw new GraknClientException("Failed graqlExecute. Error status: " + statusCode + ", error info: " + entity, response.getStatusInfo());
        }
        LOG.debug("Received {}", statusCode);
        response.close();
        return QueryResponse.from(queryList, entity);
    }

    public Optional<Keyspace> keyspace(String keyspace) throws GraknClientException {
        URI fullURI = UriBuilder.fromPath(keyspaceURL).buildFromMap(ImmutableMap.of("keyspace", keyspace));
        ClientResponse response = asyncHttpClient.resource(fullURI.toString())
                .accept(APPLICATION_JSON_GRAQL)
                .get(ClientResponse.class);
        int statusCode = response.getStatus();
        LOG.debug("Received {}", statusCode);
        if (response.getStatusInfo().getStatusCode() == Status.NOT_FOUND.getStatusCode()) {
            return Optional.empty();
        }
        String entity = response.getEntity(String.class);
        if (!response.getStatusInfo().getFamily().equals(Family.SUCCESSFUL)) {
            throw new GraknClientException("Failed keyspace. Error status: " + statusCode + ", error info: " + entity, response.getStatusInfo());
        }
        String value = Json.read(entity).at("value").asString();
        response.close();
        return Optional.of(Keyspace.of(value));
    }
}
