/*
 * Grakn - A Distributed Semantic Database
 * Copyright (C) 2016-2018 Grakn Labs Limited
 *
 * Grakn is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
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

package ai.grakn.engine.controller.response;

import ai.grakn.engine.Jacksonisable;
import ai.grakn.util.REST;
import ai.grakn.util.REST.WebPath;
import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.auto.value.AutoValue;

import javax.annotation.CheckReturnValue;

/**
 * <p>
 *     Response object representing {@link ai.grakn.Keyspace}
 * </p>
 *
 * @author Filipe Peliz Pinto Teixeira
 */
@AutoValue
public abstract class Keyspace implements Jacksonisable {

    @CheckReturnValue
    public abstract ai.grakn.Keyspace value();

    @CheckReturnValue
    @JsonCreator
    public static Keyspace of(ai.grakn.Keyspace value){
        return new AutoValue_Keyspace(value);
    }

    @CheckReturnValue
    @JsonProperty("@id")
    public String id(){
        return REST.resolveTemplate(WebPath.KB_KEYSPACE, name());
    }

    @CheckReturnValue
    @JsonProperty
    public String name(){
        return value().getValue();
    }

    @CheckReturnValue
    @JsonProperty
    public String types(){
        return REST.resolveTemplate(WebPath.KEYSPACE_TYPE, name());
    }

    @CheckReturnValue
    @JsonProperty
    public String roles(){
        return REST.resolveTemplate(WebPath.KEYSPACE_ROLE, name());
    }

    @CheckReturnValue
    @JsonProperty
    public String rules(){
        return REST.resolveTemplate(WebPath.KEYSPACE_RULE, name());
    }

    @CheckReturnValue
    @JsonProperty
    public String graql(){
        return REST.resolveTemplate(WebPath.KEYSPACE_GRAQL, name());
    }
}
