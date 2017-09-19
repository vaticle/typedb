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
 *
 */

package ai.grakn.graql.internal.gremlin.sets;

import ai.grakn.GraknTx;
import ai.grakn.concept.Label;
import ai.grakn.concept.SchemaConcept;
import ai.grakn.graql.Var;
import ai.grakn.graql.admin.VarProperty;
import ai.grakn.graql.internal.gremlin.EquivalentFragmentSet;
import ai.grakn.graql.internal.gremlin.fragment.Fragment;
import ai.grakn.graql.internal.gremlin.fragment.Fragments;
import com.google.common.collect.ImmutableSet;

import javax.annotation.Nullable;
import java.util.Set;

import static java.util.stream.Collectors.toSet;

/**
 * @author Felix Chapman
 */
class LabelFragmentSet extends EquivalentFragmentSet {

    private final VarProperty varProperty;
    private final Var type;
    private ImmutableSet<Label> labels;

    LabelFragmentSet(VarProperty varProperty, Var type, ImmutableSet<Label> labels) {
        super(Fragments.label(varProperty, type, labels));
        this.varProperty = varProperty;
        this.type = type;
        this.labels = labels;
    }

    Var type() {
        return type;
    }

    ImmutableSet<Label> labels() {
        return labels;
    }

    /**
     * Expand a {@link LabelFragmentSet} to match all sub-concepts of the single existing {@link Label}.
     *
     * Returns null if there is not exactly one label any of the {@link Label}s mentioned are not in the knowledge base.
     */
    @Nullable
    LabelFragmentSet tryExpandSubs(Var typeVar, GraknTx tx) {
        if (labels.size() != 1) return null;

        Label oldLabel = labels.iterator().next();

        SchemaConcept concept = tx.getSchemaConcept(oldLabel);
        if (concept == null) return null;

        Set<Label> newLabels = concept.subs().map(SchemaConcept::getLabel).collect(toSet());

        return new LabelFragmentSet(varProperty, typeVar, ImmutableSet.copyOf(newLabels));
    }

    /**
     * Optimise away any redundant {@link LabelFragmentSet}s. A {@link LabelFragmentSet} is considered redundant if:
     * <ol>
     *   <li>It refers to a schema concept that exists in the knowledge base
     *   <li>It is not associated with a user-defined variable
     *   <li>The variable it is associated with is not referred to in any other fragment
     *   <li>The fragment set is not the only remaining fragment set</li>
     * </ol>
     */
    static final FragmentSetOptimisation REDUNDANT_LABEL_ELIMINATION_OPTIMISATION = (fragmentSets, graph) -> {

        if (fragmentSets.size() <= 1) return false;

        Iterable<LabelFragmentSet> labelFragments =
                EquivalentFragmentSets.fragmentSetOfType(LabelFragmentSet.class, fragmentSets)::iterator;

        for (LabelFragmentSet labelSet : labelFragments) {

            boolean hasUserDefinedVar = labelSet.type().isUserDefinedName();
            if (hasUserDefinedVar) continue;

            boolean existsInGraph = labelSet.labels().stream().anyMatch(label -> graph.getSchemaConcept(label) != null);
            if (!existsInGraph) continue;

            boolean varReferredToInOtherFragment = fragmentSets.stream()
                    .filter(set -> !set.equals(labelSet))
                    .flatMap(set -> set.fragments().stream())
                    .map(Fragment::vars)
                    .anyMatch(vars -> vars.contains(labelSet.type()));

            if (!varReferredToInOtherFragment) {
                fragmentSets.remove(labelSet);
                return true;
            }
        }

        return false;
    };

}
