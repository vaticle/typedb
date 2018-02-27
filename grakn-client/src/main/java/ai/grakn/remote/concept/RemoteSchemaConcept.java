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
import ai.grakn.concept.Label;
import ai.grakn.concept.LabelId;
import ai.grakn.concept.Rule;
import ai.grakn.concept.SchemaConcept;
import ai.grakn.graql.GetQuery;
import ai.grakn.graql.Var;
import ai.grakn.grpc.ConceptProperty;

import java.util.stream.Stream;

import static ai.grakn.graql.Graql.var;
import static ai.grakn.util.Schema.MetaSchema.THING;

/**
 * @author Felix Chapman
 *
 * @param <Self> The exact type of this class
 */
abstract class RemoteSchemaConcept<Self extends SchemaConcept> extends RemoteConcept implements SchemaConcept {

    @Override
    public final Label getLabel() {
        return getProperty(ConceptProperty.LABEL);
    }

    @Override
    public final Boolean isImplicit() {
        return getProperty(ConceptProperty.IS_IMPLICIT);
    }

    @Override
    public final Self setLabel(Label label) {
        throw new UnsupportedOperationException(); // TODO: implement
    }

    @Override
    public final Self sup() {
        throw new UnsupportedOperationException(); // TODO: implement
    }

    @Override
    public final Stream<Self> sups() {
        Var x = var("x");
        GetQuery query = tx().graql().match(var().id(getId()).sub(x)).get();
        return query.stream()
                .map(answer -> answer.get(x))
                .filter(RemoteSchemaConcept::notMetaThing)
                .map(this::asSelf);
    }

    private static boolean notMetaThing(Concept concept) {
        return !concept.isSchemaConcept() || !concept.asSchemaConcept().getLabel().equals(THING.getLabel());
    }

    @Override
    public final Stream<Self> subs() {
        Var x = var("x");
        Var y = var("y");
        GetQuery query = tx().graql().match(x.sub(y), y.id(getId())).get();
        return query.stream()
                .map(answer -> answer.get(x))
                .map(this::asSelf);
    }

    @Override
    public final LabelId getLabelId() {
        throw new UnsupportedOperationException(); // TODO: remove from API
    }

    @Override
    public final Stream<Rule> getRulesOfHypothesis() {
        throw new UnsupportedOperationException(); // TODO: remove from API
    }

    @Override
    public final Stream<Rule> getRulesOfConclusion() {
        throw new UnsupportedOperationException(); // TODO: remove from API
    }

    abstract Self asSelf(Concept concept);
}
