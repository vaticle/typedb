/*
 * MindmapsDB - A Distributed Semantic Database
 * Copyright (C) 2016  Mindmaps Research Ltd
 *
 * MindmapsDB is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * MindmapsDB is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with MindmapsDB. If not, see <http://www.gnu.org/licenses/gpl.txt>.
 */

package io.mindmaps.graql.internal.parser;

import com.google.common.collect.ImmutableMap;
import io.mindmaps.concept.ResourceType;
import io.mindmaps.graql.*;
import io.mindmaps.graql.internal.util.StringConverter;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

import static io.mindmaps.graql.Graql.var;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toSet;

/**
 * ANTLR visitor class for parsing a query
 */
// This class performs a lot of unchecked casts, because ANTLR's visit methods only return 'object'
@SuppressWarnings("unchecked")
class QueryVisitor extends GraqlBaseVisitor {

    private final QueryBuilder queryBuilder;
    private final ImmutableMap<String, Function<List<Object>, Aggregate>> aggregateMethods;

    QueryVisitor(
            ImmutableMap<String, Function<List<Object>, Aggregate>> aggregateMethods, QueryBuilder queryBuilder) {
        this.aggregateMethods = aggregateMethods;
        this.queryBuilder = queryBuilder;
    }

    @Override
    public Query<?> visitQueryEOF(GraqlParser.QueryEOFContext ctx) {
        return (Query<?>) visitQuery(ctx.query());
    }

    @Override
    public MatchQuery visitMatchEOF(GraqlParser.MatchEOFContext ctx) {
        return visitMatchQuery(ctx.matchQuery());
    }

    @Override
    public AskQuery visitAskEOF(GraqlParser.AskEOFContext ctx) {
        return visitAskQuery(ctx.askQuery());
    }

    @Override
    public InsertQuery visitInsertEOF(GraqlParser.InsertEOFContext ctx) {
        return visitInsertQuery(ctx.insertQuery());
    }

    @Override
    public DeleteQuery visitDeleteEOF(GraqlParser.DeleteEOFContext ctx) {
        return visitDeleteQuery(ctx.deleteQuery());
    }

    @Override
    public ComputeQuery visitComputeEOF(GraqlParser.ComputeEOFContext ctx) {
        return visitComputeQuery(ctx.computeQuery());
    }

    @Override
    public AggregateQuery<?> visitAggregateEOF(GraqlParser.AggregateEOFContext ctx) {
        return visitAggregateQuery(ctx.aggregateQuery());
    }

    @Override
    public MatchQuery visitMatchQuery(GraqlParser.MatchQueryContext ctx) {
        Collection<Pattern> patterns = visitPatterns(ctx.patterns());
        MatchQuery matchQuery = queryBuilder.match(patterns);
        return visitModifiers(ctx.modifiers()).apply(matchQuery);
    }

    @Override
    public AskQuery visitAskQuery(GraqlParser.AskQueryContext ctx) {
        return visitMatchQuery(ctx.matchQuery()).ask();
    }

    @Override
    public InsertQuery visitInsertQuery(GraqlParser.InsertQueryContext ctx) {
        Collection<Var> vars = visitInsertPatterns(ctx.insertPatterns());

        if (ctx.matchQuery() != null) {
            return visitMatchQuery(ctx.matchQuery()).insert(vars);
        } else {
            return queryBuilder.insert(vars);
        }

    }

    @Override
    public DeleteQuery visitDeleteQuery(GraqlParser.DeleteQueryContext ctx) {
        Collection<Var> getters = visitDeletePatterns(ctx.deletePatterns());
        return visitMatchQuery(ctx.matchQuery()).delete(getters);
    }

    @Override
    public ComputeQuery visitComputeQuery(GraqlParser.ComputeQueryContext ctx) {
        // TODO: Allow registering additional compute methods
        String computeMethod = visitId(ctx.id());

        if (ctx.subgraph() != null) {
            Set<String> typeIds = visitSubgraph(ctx.subgraph());
            return queryBuilder.compute(computeMethod, typeIds);
        } else {
            return queryBuilder.compute(computeMethod);
        }
    }

    @Override
    public Set<String> visitSubgraph(GraqlParser.SubgraphContext ctx) {
        return ctx.id().stream().map(this::visitId).collect(toSet());
    }

    @Override
    public AggregateQuery<?> visitAggregateQuery(GraqlParser.AggregateQueryContext ctx) {
        Aggregate aggregate = visitAggregate(ctx.aggregate());
        return visitMatchQuery(ctx.matchQuery()).aggregate(aggregate);
    }

    @Override
    public Aggregate<?, ?> visitCustomAgg(GraqlParser.CustomAggContext ctx) {
        String name = visitId(ctx.id());
        Function<List<Object>, Aggregate> aggregateMethod = aggregateMethods.get(name);

        List<Object> arguments = ctx.argument().stream().map(this::visit).collect(toList());

        return aggregateMethod.apply(arguments);
    }

    @Override
    public Aggregate<?, ? extends Map<String, ?>> visitSelectAgg(GraqlParser.SelectAggContext ctx) {
        Set aggregates = ctx.namedAgg().stream().map(this::visitNamedAgg).collect(toSet());

        // We can't handle cases when the aggregate types are wrong, because the user can provide custom aggregates
        return Graql.select(aggregates);
    }

    @Override
    public String visitVariableArgument(GraqlParser.VariableArgumentContext ctx) {
        return getVariable(ctx.VARIABLE());
    }

    @Override
    public Aggregate<?, ?> visitAggregateArgument(GraqlParser.AggregateArgumentContext ctx) {
        return visitAggregate(ctx.aggregate());
    }

    @Override
    public NamedAggregate<?, ?> visitNamedAgg(GraqlParser.NamedAggContext ctx) {
        String name = visitId(ctx.id());
        return visitAggregate(ctx.aggregate()).as(name);
    }

    @Override
    public List<Pattern> visitPatterns(GraqlParser.PatternsContext ctx) {
        return ctx.pattern().stream()
                .map(this::visitPattern)
                .collect(toList());
    }

    @Override
    public Pattern visitOrPattern(GraqlParser.OrPatternContext ctx) {
        return Graql.or(ctx.pattern().stream().map(this::visitPattern).collect(toList()));
    }

    @Override
    public Pattern visitAndPattern(GraqlParser.AndPatternContext ctx) {
        return Graql.and(visitPatterns(ctx.patterns()));
    }

    @Override
    public Var visitVarPattern(GraqlParser.VarPatternContext ctx) {
        Var var = visitVariable(ctx.variable());
        return getVarProperties(ctx.property()).apply(var);
    }

    @Override
    public UnaryOperator<Var> visitProperty(GraqlParser.PropertyContext ctx) {
        return (UnaryOperator<Var>) super.visitProperty(ctx);
    }

    @Override
    public UnaryOperator<Var> visitPropId(GraqlParser.PropIdContext ctx) {
        return var -> var.id(getString(ctx.STRING()));
    }

    @Override
    public UnaryOperator<Var> visitPropValFlag(GraqlParser.PropValFlagContext ctx) {
        return Var::value;
    }

    @Override
    public UnaryOperator<Var> visitPropVal(GraqlParser.PropValContext ctx) {
        return var -> var.value(visitValue(ctx.value()));
    }

    @Override
    public UnaryOperator<Var> visitPropValPred(GraqlParser.PropValPredContext ctx) {
        return var -> var.value(visitPredicate(ctx.predicate()));
    }

    @Override
    public UnaryOperator<Var> visitPropLhs(GraqlParser.PropLhsContext ctx) {
        return var -> var.lhs(getOriginalText(ctx.query()));
    }

    @Override
    public UnaryOperator<Var> visitPropRhs(GraqlParser.PropRhsContext ctx) {
        return var -> var.rhs(getOriginalText(ctx.query()));
    }

    @Override
    public UnaryOperator<Var> visitPropHasFlag(GraqlParser.PropHasFlagContext ctx) {
        return var -> var.has(visitId(ctx.id()));
    }

    @Override
    public UnaryOperator<Var> visitPropHas(GraqlParser.PropHasContext ctx) {
        return var -> var.has(visitId(ctx.id()), visitValue(ctx.value()));
    }

    @Override
    public UnaryOperator<Var> visitPropHasFull(GraqlParser.PropHasFullContext ctx) {
        String type = visitId(ctx.id());
        if (ctx.predicate() != null) {
            return var -> var.has(type, visitPredicate(ctx.predicate()));
        } else {
            return var -> var.has(type, var(getVariable(ctx.VARIABLE())));
        }
    }

    @Override
    public UnaryOperator<Var> visitPropResource(GraqlParser.PropResourceContext ctx) {
        return var -> var.hasResource(visitVariable(ctx.variable()));
    }

    @Override
    public UnaryOperator<Var> visitIsAbstract(GraqlParser.IsAbstractContext ctx) {
        return Var::isAbstract;
    }

    @Override
    public UnaryOperator<Var> visitPropDatatype(GraqlParser.PropDatatypeContext ctx) {
        return var -> var.datatype(getDatatype(ctx.DATATYPE()));
    }

    @Override
    public UnaryOperator<Var> visitPropRegex(GraqlParser.PropRegexContext ctx) {
        return var -> var.regex(getRegex(ctx.REGEX()));
    }

    @Override
    public UnaryOperator<Var> visitPropRel(GraqlParser.PropRelContext ctx) {
        return getVarProperties(ctx.roleOpt());
    }

    @Override
    public UnaryOperator<Var> visitInsertRel(GraqlParser.InsertRelContext ctx) {
        return getVarProperties(ctx.roleplayerRole());
    }

    @Override
    public UnaryOperator<Var> visitRoleOpt(GraqlParser.RoleOptContext ctx) {
        return (UnaryOperator<Var>) super.visitRoleOpt(ctx);
    }

    @Override
    public Collection<Var> visitInsertPatterns(GraqlParser.InsertPatternsContext ctx) {
        return ctx.insertPattern().stream()
                .map(this::visitInsertPattern)
                .collect(toList());
    }

    @Override
    public Var visitInsertPattern(GraqlParser.InsertPatternContext ctx) {
        Var var = visitVariable(ctx.variable());
        return getVarProperties(ctx.insert()).apply(var);
    }

    @Override
    public UnaryOperator<Var> visitInsert(GraqlParser.InsertContext ctx) {
        return (UnaryOperator<Var>) super.visitInsert(ctx);
    }

    @Override
    public Collection<Var> visitDeletePatterns(GraqlParser.DeletePatternsContext ctx) {
        return ctx.deletePattern().stream()
                .map(this::visitDeletePattern)
                .collect(toList());
    }

    @Override
    public Var visitDeletePattern(GraqlParser.DeletePatternContext ctx) {
        Var var = buildVar(ctx.VARIABLE());
        return getVarProperties(ctx.delete()).apply(var);
    }

    @Override
    public UnaryOperator<Var> visitDelete(GraqlParser.DeleteContext ctx) {
        return (UnaryOperator<Var>) super.visitDelete(ctx);
    }

    @Override
    public UnaryOperator<Var> visitRoleplayerRole(GraqlParser.RoleplayerRoleContext ctx) {
        return var -> var.rel(visitVariable(ctx.variable(0)), visitVariable(ctx.variable(1)));
    }

    @Override
    public UnaryOperator<Var> visitRoleplayerOnly(GraqlParser.RoleplayerOnlyContext ctx) {
        return var -> var.rel(visitVariable(ctx.variable()));
    }


    @Override
    public UnaryOperator<Var> visitIsa(GraqlParser.IsaContext ctx) {
        return var -> var.isa(visitVariable(ctx.variable()));
    }

    @Override
    public UnaryOperator<Var> visitAko(GraqlParser.AkoContext ctx) {
        return var -> var.ako(visitVariable(ctx.variable()));
    }

    @Override
    public UnaryOperator<Var> visitHasRole(GraqlParser.HasRoleContext ctx) {
        return var -> var.hasRole(visitVariable(ctx.variable()));
    }

    @Override
    public UnaryOperator<Var> visitPlaysRole(GraqlParser.PlaysRoleContext ctx) {
        return var -> var.playsRole(visitVariable(ctx.variable()));
    }

    @Override
    public UnaryOperator<Var> visitHasScope(GraqlParser.HasScopeContext ctx) {
        return var -> var.hasScope(visitVariable(ctx.variable()));
    }

    @Override
    public String visitId(GraqlParser.IdContext ctx) {
        if (ctx.ID() != null) {
            return ctx.ID().getText();
        } else {
            return getString(ctx.STRING());
        }
    }

    @Override
    public Var visitVariable(GraqlParser.VariableContext ctx) {
        if (ctx == null) {
            return var();
        } else if (ctx.id() != null) {
            return Graql.id(visitId(ctx.id()));
        } else {
            return buildVar(ctx.VARIABLE());
        }
    }

    @Override
    public ValuePredicate visitPredicateEq(GraqlParser.PredicateEqContext ctx) {
        return Graql.eq(visitValue(ctx.value()));
    }

    @Override
    public ValuePredicate visitPredicateNeq(GraqlParser.PredicateNeqContext ctx) {
        return Graql.neq(visitValue(ctx.value()));
    }

    @Override
    public ValuePredicate visitPredicateGt(GraqlParser.PredicateGtContext ctx) {
        return Graql.gt(visitValue(ctx.value()));
    }

    @Override
    public ValuePredicate visitPredicateGte(GraqlParser.PredicateGteContext ctx) {
        return Graql.gte(visitValue(ctx.value()));
    }

    @Override
    public ValuePredicate visitPredicateLt(GraqlParser.PredicateLtContext ctx) {
        return Graql.lt(visitValue(ctx.value()));
    }

    @Override
    public ValuePredicate visitPredicateLte(GraqlParser.PredicateLteContext ctx) {
        return Graql.lte(visitValue(ctx.value()));
    }

    @Override
    public ValuePredicate visitPredicateContains(GraqlParser.PredicateContainsContext ctx) {
        return Graql.contains(getString(ctx.STRING()));
    }

    @Override
    public ValuePredicate visitPredicateRegex(GraqlParser.PredicateRegexContext ctx) {
        return Graql.regex(getRegex(ctx.REGEX()));
    }

    @Override
    public ValuePredicate visitPredicateAnd(GraqlParser.PredicateAndContext ctx) {
        return visitPredicate(ctx.predicate(0)).and(visitPredicate(ctx.predicate(1)));
    }

    @Override
    public ValuePredicate visitPredicateOr(GraqlParser.PredicateOrContext ctx) {
        return visitPredicate(ctx.predicate(0)).or(visitPredicate(ctx.predicate(1)));
    }

    @Override
    public ValuePredicate visitPredicateParens(GraqlParser.PredicateParensContext ctx) {
        return visitPredicate(ctx.predicate());
    }

    @Override
    public String visitValueString(GraqlParser.ValueStringContext ctx) {
        return getString(ctx.STRING());
    }

    @Override
    public Long visitValueInteger(GraqlParser.ValueIntegerContext ctx) {
        return getInteger(ctx.INTEGER());
    }

    @Override
    public Double visitValueReal(GraqlParser.ValueRealContext ctx) {
        return Double.valueOf(ctx.REAL().getText());
    }

    @Override
    public Object visitValueBoolean(GraqlParser.ValueBooleanContext ctx) {
        return Boolean.valueOf(ctx.BOOLEAN().getText());
    }

    @Override
    public UnaryOperator<MatchQuery> visitModifiers(GraqlParser.ModifiersContext ctx) {
        Stream<UnaryOperator<MatchQuery>> modifiers = ctx.modifier().stream().map(this::visitModifier);
        return chainOperators(modifiers);
    }

    @Override
    public UnaryOperator<MatchQuery> visitModifierSelect(GraqlParser.ModifierSelectContext ctx) {
        Set<String> names = ctx.VARIABLE().stream().map(this::getVariable).collect(toSet());
        return matchQuery -> matchQuery.select(names);
    }

    @Override
    public UnaryOperator<MatchQuery> visitModifierLimit(GraqlParser.ModifierLimitContext ctx) {
        return matchQuery -> matchQuery.limit(getInteger(ctx.INTEGER()));
    }

    @Override
    public UnaryOperator<MatchQuery> visitModifierOffset(GraqlParser.ModifierOffsetContext ctx) {
        return matchQuery -> matchQuery.offset(getInteger(ctx.INTEGER()));
    }

    @Override
    public UnaryOperator<MatchQuery> visitModifierDistinct(GraqlParser.ModifierDistinctContext ctx) {
        return MatchQuery::distinct;
    }

    @Override
    public UnaryOperator<MatchQuery> visitModifierOrderBy(GraqlParser.ModifierOrderByContext ctx) {
        // decide which ordering method to use
        String var = getVariable(ctx.VARIABLE());
        if (ctx.id() != null) {
            String type = visitId(ctx.id());
            if (ctx.ORDER() != null) {
                return matchQuery -> matchQuery.orderBy(var, type, getOrder(ctx.ORDER()));
            } else {
                return matchQuery -> matchQuery.orderBy(var, type);
            }
        } else {
            if (ctx.ORDER() != null) {
                return matchQuery -> matchQuery.orderBy(var, getOrder(ctx.ORDER()));
            } else {
                return matchQuery -> matchQuery.orderBy(var);
            }
        }
    }

    @Override
    public Pattern visitPatternSep(GraqlParser.PatternSepContext ctx) {
        return visitPattern(ctx.pattern());
    }

    private Aggregate<?, ?> visitAggregate(GraqlParser.AggregateContext ctx) {
        return (Aggregate) visit(ctx);
    }

    private Pattern visitPattern(GraqlParser.PatternContext ctx) {
        return (Pattern) visit(ctx);
    }

    private UnaryOperator<MatchQuery> visitModifier(GraqlParser.ModifierContext ctx) {
        return (UnaryOperator<MatchQuery>) visit(ctx);
    }

    private ValuePredicate visitPredicate(GraqlParser.PredicateContext ctx) {
        return (ValuePredicate) visit(ctx);
    }

    private Comparable<?> visitValue(GraqlParser.ValueContext ctx) {
        return (Comparable<?>) visit(ctx);
    }

    private String getVariable(TerminalNode variable) {
        // Remove '$' prefix
        return variable.getText().substring(1);
    }

    private String getRegex(TerminalNode string) {
        // Remove surrounding /.../
        return getString(string);
    }

    private String getString(TerminalNode string) {
        // Remove surrounding quotes
        String unquoted = string.getText().substring(1, string.getText().length() - 1);
        return StringConverter.unescapeString(unquoted);
    }

    /**
     * Compose two functions together into a single function
     */
    private <T> UnaryOperator<T> compose(UnaryOperator<T> before, UnaryOperator<T> after) {
        return x -> after.apply(before.apply(x));
    }

    /**
     * Chain a stream of functions into a single function, which applies each one after the other
     */
    private <T> UnaryOperator<T> chainOperators(Stream<UnaryOperator<T>> operators) {
        return operators.reduce(UnaryOperator.identity(), this::compose);
    }

    private UnaryOperator<Var> getVarProperties(List<? extends ParserRuleContext> contexts) {
        return chainOperators(contexts.stream().map(ctx -> (UnaryOperator<Var>) visit(ctx)));
    }

    private long getInteger(TerminalNode integer) {
        return Long.valueOf(integer.getText());
    }

    private boolean getOrder(TerminalNode order) {
        return order.getText().equals("asc");
    }

    private ResourceType.DataType getDatatype(TerminalNode datatype) {
        switch (datatype.getText()) {
            case "long":
                return ResourceType.DataType.LONG;
            case "double":
                return ResourceType.DataType.DOUBLE;
            case "string":
                return ResourceType.DataType.STRING;
            case "boolean":
                return ResourceType.DataType.BOOLEAN;
            default:
                throw new RuntimeException("Unrecognized datatype " + datatype.getText());
        }
    }

    private Var buildVar(TerminalNode variable) {
        Var var;
        if (variable != null) {
            var = var(getVariable(variable));
        } else {
            var = var();
        }
        return var;
    }

    private String getOriginalText(ParserRuleContext ctx) {
        int start = ctx.start.getStartIndex();
        int stop = ctx.stop.getStopIndex();
        Interval interval = new Interval(start, stop);
        return ctx.start.getInputStream().getText(interval);
    }
}
