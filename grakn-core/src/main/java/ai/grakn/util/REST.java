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

/**
 * Class containing strings describing the REST API, including URIs and fields.
 *
 * @author Marco Scoppetta
 */
public class REST {

    /**
     * Class containing URIs to REST endpoints.
     */
    public static class WebPath{

        public static final String COMMIT_LOG_URI = "/commit_log";

        public static final String REMOTE_SHELL_URI = "/shell/remote";

        /**
         * URIs to visualiser controller
         */
        public static class Graph {
            public static final String GRAQL = "/graql";
        }

        /**
         * URIs to Tasks Controller endpoints
         */
        public static class Tasks {
            public static final String TASKS = "/tasks";
            public static final String GET = "/tasks/:id";
            public static final String STOP = "/tasks/:id/stop";
        }

        /**
         * URIs to System Controller endpoints
         */
        public static class System {
            public static final String CONFIGURATION = "/configuration";
            public static final String KEYSPACES = "/keyspaces";
        }

        public static class Concept {
            public static final String CONCEPT = "/concept";
        }

        public static final String NEW_SESSION_URI="/auth/session/";
        public static final String IS_PASSWORD_PROTECTED_URI="/auth/enabled/";

        public static final String ALL_USERS = "/user/all";
        public static final String ONE_USER = "/user/one";
    }

    /**
     * Class containing request fields and content types.
     */
    public static class Request {
        public static final String QUERY_FIELD = "query";
        public static final String ID_PARAMETER = ":id";
        public static final String KEYSPACE_PARAM = "keyspace";
        public static final String GRAPH_CONFIG_PARAM = "graphConfig";
        public static final String TASK_STATUS_PARAMETER = "status";
        public static final String TASK_CLASS_NAME_PARAMETER = "className";
        public static final String TASK_CREATOR_PARAMETER = "creator";
        public static final String TASK_RUN_AT_PARAMETER = "runAt";
        public static final String TASK_RUN_INTERVAL_PARAMETER = "interval";
        public static final String TASK_LOADER_INSERTS = "inserts";
        public static final String LIMIT_PARAM = "limit";
        public static final String OFFSET_PARAM = "offset";
        public static final String COMMIT_LOG_TYPE = "concept-base-type";
        public static final String COMMIT_LOG_ID = "concept-vertex-id";
        public static final String COMMIT_LOG_INDEX = "concept-index";
    }

    /**
     * Class listing possible graph configuration options.
     */
    public static class GraphConfig{
        public static final String DEFAULT = "default";
        public static final String COMPUTER = "computer";
    }

    /**
     * Class listing various HTTP connection strings.
     */
    public static class HttpConn{
        public static final int OK = 200;
        public static final String UTF8 = "UTF8";
        public static final String CONTENT_LENGTH = "Content-Length";
        public static final String CONTENT_TYPE = "Content-Type";
        public static final String POST_METHOD = "POST";
        public static final String DELETE_METHOD = "DELETE";
        public static final String GET_METHOD = "GET";
        public static final String APPLICATION_POST_TYPE = "application/POST";
    }

    /**
     * Class listing various strings found in responses from the REST API.
     */
    public static class Response{

        /**
         * Response content types
         */
        public static class ContentType {
            public static final String APPLICATION_JSON_GRAQL = "application/graql+json";
            public static final String APPLICATION_TEXT = "application/text";
            public static final String APPLICATION_HAL ="application/hal+json";
        }

    }

    /**
     * Class listing various strings used in the JSON messages sent using websockets for the remote Graql shell.
     */
    public static class RemoteShell {
        public static final String ACTION = "action";
        public static final String ACTION_INIT = "init";
        public static final String ACTION_QUERY = "query";
        public static final String ACTION_END = "end";
        public static final String ACTION_ERROR = "error";
        public static final String ACTION_COMMIT = "commit";
        public static final String ACTION_ROLLBACK = "rollback";
        public static final String ACTION_CLEAN = "clean";
        public static final String ACTION_PING = "ping";
        public static final String ACTION_TYPES = "types";
        public static final String ACTION_DISPLAY = "display";

        public static final String USERNAME = "username";
        public static final String PASSWORD = "password";
        public static final String KEYSPACE = "keyspace";
        public static final String OUTPUT_FORMAT = "outputFormat";
        public static final String IMPLICIT = "implicit";
        public static final String INFER = "infer";
        public static final String MATERIALISE = "materialise";
        public static final String QUERY = "query";
        public static final String QUERY_RESULT = "result";
        public static final String ERROR = "error";
        public static final String TYPES = "types";
        public static final String DISPLAY = "display";
    }
}
