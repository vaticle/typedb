/*
 * GRAKN.AI - THE KNOWLEDGE GRAPH
 * Copyright (C) 2018 Grakn Labs Ltd
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
package ai.grakn.batch;

import javax.ws.rs.core.Response.Status.Family;
import javax.ws.rs.core.Response.StatusType;

/**
 * Exceptions generated by the client
 *
 * @author Domenico Corapi
 */
public class GraknClientException extends Exception {

    private final boolean retriable;

    public GraknClientException(String s) {
        this(s, false);
    }

    public GraknClientException(String s, boolean retriable) {
        super(s);
        this.retriable = retriable;
    }

    public GraknClientException(String s, StatusType statusInfo) {
        this(s, statusInfo.getFamily().equals(Family.SERVER_ERROR));
    }

    public boolean isRetriable() {
        return retriable;
    }
}
