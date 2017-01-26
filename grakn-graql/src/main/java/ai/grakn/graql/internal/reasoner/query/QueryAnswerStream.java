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

package ai.grakn.graql.internal.reasoner.query;

import ai.grakn.concept.Concept;
import ai.grakn.graql.internal.reasoner.atom.NotEquals;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 *
 * <p>
 * Wrapper class for an answer stream providing higher level filtering facilities
 * as well as unification and join operations.
 * </p>
 *
 * @author Kasper Piskorski
 *
 */
public class QueryAnswerStream {
    private final Stream<Map<String, Concept>> stream;

    public QueryAnswerStream(Stream<Map<String, Concept>> s) {
        this.stream = s;
    }
    public Stream<Map<String, Concept>> stream() {return stream;}

    private static Map<String, Concept> varFilterOperator(Map<String, Concept> answer, Set<String> vars) {
        Map<String, Concept> filteredAnswer = new HashMap<>();
        vars.stream()
                .filter(answer::containsKey)
                .forEach(var -> filteredAnswer.put(var, answer.get(var)));
        return filteredAnswer;
    }

    private static boolean knownFilterOperator(Map<String, Concept> answer, QueryAnswers known) {
        boolean isKnown = false;
        Iterator<Map<String, Concept>> it = known.iterator();
        while (it.hasNext() && !isKnown) {
            Map<String, Concept> knownAnswer = it.next();
            isKnown = knownAnswer.entrySet().containsAll(answer.entrySet());
        }
        return !isKnown;
    }

    private static boolean nonEqualsOperator(Map<String, Concept> answer, Set<NotEquals> atoms) {
        if(atoms.isEmpty()) return false;
        boolean filter = false;
        Iterator<NotEquals> it = atoms.iterator();
        while (it.hasNext() && !filter) {
            filter = NotEquals.notEqualsOperator(answer, it.next());
        }
        return filter;
    }

    public static final BiFunction<Map<String, Concept>, Set<String>, Stream<Map<String, Concept>>> varFilterFunction = (a, vars) -> {
        Map<String, Concept> filteredAnswer = varFilterOperator(a, vars);
        return filteredAnswer.isEmpty() ? Stream.empty() : Stream.of(filteredAnswer);
    };

    public static final BiFunction<Map<String, Concept>, QueryAnswers, Stream<Map<String, Concept>>> knownFilterFunction =
            (a, known) -> knownFilterOperator(a, known) ? Stream.empty() : Stream.of(a);

    public static final BiFunction<Map<String, Concept>, Set<String>, Stream<Map<String, Concept>>> incompleteFilterFunction =
            (a, vars) -> a.keySet().containsAll(vars) ? Stream.of(a) : Stream.empty();

    public static final BiFunction<Map<String, Concept>, Set<NotEquals>, Stream<Map<String, Concept>>> nonEqualsFilterFunction =
            (a, atoms) -> nonEqualsOperator(a, atoms) ? Stream.empty() : Stream.of(a);

    /**
     * filter stream by constraining the variable set to the provided one
     * @param vars set of variable names
     * @return filtered answers
     */
    public QueryAnswerStream filterVars(Set<String> vars) {
        return new QueryAnswerStream(this.stream.flatMap(a -> varFilterFunction.apply(a, vars)));
    }

    /**
     * filter stream by discarding the already known ones
     * @param known set of known answers
     * @return filtered answers
     */
    public QueryAnswerStream filterKnown(QueryAnswers known){
        return new QueryAnswerStream(this.stream.flatMap(a -> knownFilterFunction.apply(a, known)));
    }

    /**
     * filter stream by discarding answers with incomplete set of variables
     * @param vars variable set considered complete
     * @return filtered answers
     */
    public QueryAnswerStream filterIncomplete(Set<String> vars) {
        return new QueryAnswerStream(this.stream.flatMap(a -> incompleteFilterFunction.apply(a, vars)));
    }

    /**
     * filter stream by applying NonEquals filters
     * @param query query containing filters
     * @return filtered answers
     */
    public QueryAnswerStream filterNonEquals(ReasonerQueryImpl query){
        Set<NotEquals> filters = query.getFilters();
        if(filters.isEmpty()) return new QueryAnswerStream(this.stream);
        return new QueryAnswerStream(this.stream.flatMap(a -> nonEqualsFilterFunction.apply(a, filters)));
    }

    private static Map<String, Concept> joinOperator(Map<String, Concept> m1, Map<String, Concept> m2){
        boolean isCompatible = true;
        Set<String> keysToCompare = new HashSet<>(m1.keySet());
        keysToCompare.retainAll(m2.keySet());
        Iterator<String> it = keysToCompare.iterator();
        while(it.hasNext() && isCompatible) {
            String var = it.next();
            isCompatible = m1.get(var).equals(m2.get(var));
        }
        if (isCompatible) {
            Map<String, Concept> merged = new HashMap<>(m1);
            merged.putAll(m2);
            return merged;
        } else return new HashMap<>();
    }

    private static final BiFunction<Map<String, Concept>, Map<String, Concept>, Stream<Map<String, Concept>>> joinFunction = (a1, a2) -> {
        Map<String, Concept> merged = joinOperator(a1, a2);
        return merged.isEmpty()? Stream.empty(): Stream.of(merged);
    };

    /**
     * perform a half-lazy join operation on two streams (this and stream2)
     * @param stream2 right operand of join operation
     * @return joined stream
     */
    public QueryAnswerStream join(QueryAnswerStream stream2) {
        Stream<Map<String, Concept>> result =  this.stream;
        Collection<Map<String, Concept>> c = stream2.stream().collect(Collectors.toSet());
        result = result.flatMap(a1 -> c.stream().flatMap(a2 -> joinFunction.apply(a1, a2)));
        return new QueryAnswerStream(result);
    }

    /**
     * perform a half-lazy join operation on two streams (stream and stream2)
     * @param stream left operand of join operation
     * @param stream2 right operand of join operation
     * @return joined stream
     */
    public static Stream<Map<String, Concept>> join(Stream<Map<String, Concept>> stream, Stream<Map<String, Concept>> stream2) {
        Collection<Map<String, Concept>> c = stream2.collect(Collectors.toSet());
        return stream.flatMap(a1 -> c.stream().flatMap(a2 -> joinFunction.apply(a1, a2)));
    }
}


