package io.mindmaps.graql.internal.reasoner.rule;

import io.mindmaps.MindmapsGraph;
import io.mindmaps.concept.Rule;
import io.mindmaps.concept.Type;
import io.mindmaps.graql.internal.reasoner.predicate.Atomic;
import io.mindmaps.graql.internal.reasoner.query.AtomicQuery;
import io.mindmaps.graql.internal.reasoner.query.Query;
import io.mindmaps.util.ErrorMessage;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static io.mindmaps.graql.internal.reasoner.Utility.createFreshVariable;

public class InferenceRule {

    private final Query body;
    private final AtomicQuery head;

    private final Rule rule;

    public InferenceRule(Rule rl, MindmapsGraph graph){
        this.rule = rl;
        body = new Query(rule.getLHS(), graph);
        head = new AtomicQuery(rule.getRHS(), graph);
    }

    public Query getBody(){return body;}
    public AtomicQuery getHead(){return head;}

    private Type getRuleConclusionType() {
        Set<Type> types = new HashSet<>();
        Collection<Type> unfilteredTypes = rule.getConclusionTypes();
        for(Type type : unfilteredTypes)
            if (!type.isRoleType()) types.add(type);

        if (types.size() > 1)
            throw new IllegalArgumentException(ErrorMessage.NON_HORN_RULE.getMessage(rule.getId()));

        return types.iterator().next();
    }

    public Atomic getRuleConclusionAtom() {
        Set<Atomic> atoms = head.getAtoms();
        if (atoms.size() > 1)
            throw new IllegalArgumentException(ErrorMessage.NON_HORN_RULE.getMessage(body.toString()));

        Atomic atom = atoms.iterator().next();
        atom.setParentQuery(body);
        return atom;
    }

    public boolean isRuleRecursive() {
        boolean ruleRecursive = false;

        Type RHStype = getRuleConclusionType();
        if (rule.getHypothesisTypes().contains(RHStype) )
            ruleRecursive = true;

        return ruleRecursive;
    }

    private void propagateConstraints(Atomic parentAtom){
        body.addAtomConstraints(parentAtom.getSubstitutions());
        head.addAtomConstraints(body.getSubstitutions());

        if(parentAtom.isRelation()) {
            head.addAtomConstraints(parentAtom.getTypeConstraints());
            body.addAtomConstraints(parentAtom.getTypeConstraints());
        }
    }

    /**
     * propagate variables to child via a relation atom (atom variables are bound)
     * @param parentAtom   parent atom (predicate) being resolved (subgoal)
     */
    private void unifyViaAtom(Atomic parentAtom) {
        Atomic childAtom = getRuleConclusionAtom();
        Query parent = parentAtom.getParentQuery();
        Map<String, String> unifiers = childAtom.getUnifiers(parentAtom);

        //do alpha-conversion
        head.unify(unifiers);
        body.unify(unifiers);

        //check free variables for possible captures
        Set<String> childFVs = body.getVarSet();
        Set<String> parentBVs = parentAtom.getVarNames();
        Set<String> parentVars = parent.getVarSet();
        parentBVs.forEach(childFVs::remove);

        childFVs.forEach(chVar -> {
            // if (x e P) v (x e G)
            // x -> fresh
            if (parentVars.contains(chVar) /*|| globalVarMap.containsKey(chVar)*/) {
                String freshVar = createFreshVariable(body.getVarSet(), chVar);
                body.changeVarName(chVar, freshVar);
            }
        });
    }

    /**
     * make child query consistent by performing variable substitution so that parent variables are propagated
     * @param parentAtom   parent atom (predicate) being resolved (subgoal)
     */
   public void unify(Atomic parentAtom) {
        unifyViaAtom(parentAtom);
        propagateConstraints(parentAtom);
    }
}
