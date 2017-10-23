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

package ai.grakn.graql.internal.printer;

import ai.grakn.Keyspace;
import ai.grakn.concept.Concept;
import ai.grakn.graql.Var;
import ai.grakn.graql.admin.Answer;
import ai.grakn.graql.admin.AnswerExplanation;
import ai.grakn.graql.admin.VarPatternAdmin;
import ai.grakn.graql.internal.hal.HALBuilder;
import ai.grakn.graql.internal.reasoner.atom.Atom;
import ai.grakn.graql.internal.reasoner.explanation.RuleExplanation;
import ai.grakn.graql.internal.reasoner.query.ReasonerAtomicQuery;
import mjson.Json;

import java.util.Optional;


class HALPrinter extends JsonPrinter {

    private final Keyspace keyspace;
    private final int limitEmbedded;

    HALPrinter(Keyspace keyspace, int limitEmbedded) {
        this.keyspace = keyspace;
        this.limitEmbedded = limitEmbedded;
    }


    public Json graqlString(boolean inner, Concept concept, boolean inferred) {
        String json = HALBuilder.renderHALConceptData(concept, inferred, 0, keyspace, 0, limitEmbedded);
        return Json.read(json);
    }

    @Override
    public Json graqlString(boolean inner, Answer answer) {
        /**
         * How to identify concept inferred among the onoes in the answer.map()?
         */
        Json json = Json.object();

        answer.map().forEach((Var key, Concept value) -> {
            String keyString = key.getValue();
            json.set(keyString, graqlString(true, value, isInferred(key, value, answer)));
        });

        return json;
    }

    private boolean isInferred(Var key, Concept concept, Answer answer) {
        if (key == null) return false;

        //TO-DO add support for attributes
        if (!concept.isRelationship()) return false;

        //Here I already know the concept is a relationship so if rule expl -> true
        if (answer.getExplanation().isRuleExplanation()) return true;

        if (answer.getExplanation().isLookupExplanation()) return false;

        // Here we know we have a relationship but also a JoinExplanation
        Optional<Answer> subAnswer = answer.getExplanation().getAnswers().stream()
                .filter(a -> a.map().keySet().contains(key))
                .findFirst();

        return subAnswer.isPresent() && subAnswer.get().getExplanation().isRuleExplanation();
    }
}
