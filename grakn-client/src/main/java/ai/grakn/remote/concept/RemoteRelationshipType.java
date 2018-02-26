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

package ai.grakn.remote.concept;

import ai.grakn.concept.Concept;
import ai.grakn.concept.ConceptId;
import ai.grakn.concept.Relationship;
import ai.grakn.concept.RelationshipType;
import ai.grakn.concept.Role;
import ai.grakn.remote.RemoteGraknTx;
import com.google.auto.value.AutoValue;

import java.util.stream.Stream;

/**
 * @author Felix Chapman
 */
@AutoValue
abstract class RemoteRelationshipType extends RemoteType<RelationshipType, Relationship> implements RelationshipType {

    public static RemoteRelationshipType create(RemoteGraknTx tx, ConceptId id) {
        return new AutoValue_RemoteRelationshipType(tx, id);
    }

    @Override
    public final Relationship addRelationship() {
        throw new UnsupportedOperationException(); // TODO: implement
    }

    @Override
    public final Stream<Role> relates() {
        throw new UnsupportedOperationException(); // TODO: implement
    }

    @Override
    public final RelationshipType relates(Role role) {
        throw new UnsupportedOperationException(); // TODO: implement
    }

    @Override
    public final RelationshipType deleteRelates(Role role) {
        throw new UnsupportedOperationException(); // TODO: implement
    }

    @Override
    final RelationshipType asSelf(Concept concept) {
        return concept.asRelationshipType();
    }
}
