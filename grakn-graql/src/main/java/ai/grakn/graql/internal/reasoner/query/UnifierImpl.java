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

import ai.grakn.graql.VarName;
import ai.grakn.graql.admin.Unifier;
import com.google.common.collect.Maps;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import javafx.util.Pair;

/**
 *
 * <p>
 * Implementation of {@link Unifier} interface.
 * </p>
 *
 * @author Kasper Piskorski
 *
 */
public class UnifierImpl implements Unifier {

    //TODO turn it to multimap to accommodate all cases
    private final Map<VarName, VarName> unifier = new HashMap<>();


    /**
     * Identity unifier.
     */
    public UnifierImpl(){}
    public UnifierImpl(Map<VarName, VarName> map){
        unifier.putAll(map);
    }
    public UnifierImpl(Unifier u){
        unifier.putAll(u.map());
    }

    @Override
    public String toString(){
        return unifier.toString();
    }

    @Override
    public boolean equals(Object obj){
        if (obj == null || this.getClass() != obj.getClass()) return false;
        if (obj == this) return true;
        UnifierImpl u2 = (UnifierImpl) obj;
        return unifier.equals(u2.map());
    }

    @Override
    public int hashCode(){
        return unifier.hashCode();
    }

    @Override
    public boolean isEmpty() {
        return unifier.isEmpty();
    }

    @Override
    public Map<VarName, VarName> map() {
        return Maps.newHashMap(unifier);
    }

    @Override
    public Set<VarName> keySet() {
        return unifier.keySet();
    }

    @Override
    public Collection<VarName> values() {
        return unifier.values();
    }

    @Override
    public Set<Map.Entry<VarName, VarName>> mappings(){ return unifier.entrySet();}

    public VarName addMapping(VarName key, VarName value){
        return unifier.put(key, value);
    }

    @Override
    public VarName get(VarName key) {
        return unifier.get(key);
    }

    @Override
    public boolean containsKey(VarName key) {
        return unifier.containsKey(key);
    }

    @Override
    public boolean containsValue(VarName value) {
        return unifier.containsValue(value);
    }

    @Override
    public boolean containsAll(Unifier u) { return mappings().containsAll(u.mappings());}

    @Override
    public Unifier merge(Unifier d) {
        unifier.putAll(d.map());
        return this;
        /*
        if (Collections.disjoint(this.values(), d.keySet())){
            unifier.putAll(d.map());
            return this;
        }
        //TODO doesn't work with $x isa relation;
        Unifier merged = new UnifierImpl();
        Unifier inverse = this.inverse();
        this.mappings().stream().filter(m -> !d.containsKey(m.getValue())).forEach(m -> merged.addMapping(m.getKey(), m.getValue()));
        d.mappings().stream()
                .map(m -> {
                    VarName lVar = m.getKey();
                    if (inverse.containsKey(lVar)) return new Pair<>(inverse.get(lVar), m.getValue());
                    else return new Pair<>(m.getKey(), m.getValue());
                })
                .forEach(m -> merged.addMapping(m.getKey(), m.getValue()) );
        return merged;
        */
    }

    @Override
    public Unifier removeTrivialMappings() {
        Set<VarName> toRemove = unifier.entrySet().stream()
                .filter(e -> e.getKey() == e.getValue())
                .map(Map.Entry::getKey)
                .collect(Collectors.toSet());
        toRemove.forEach(unifier::remove);
        return this;
    }

    @Override
    public Unifier inverse() {
        return new UnifierImpl(
                unifier.entrySet().stream()
                .collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey))
        );
    }

    @Override
    public int size(){ return unifier.size();}
}
