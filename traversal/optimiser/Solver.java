/*
 * Copyright (C) 2021 Vaticle
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
 *
 */

package com.vaticle.typedb.core.traversal.optimiser;

import com.google.ortools.linearsolver.MPSolver;
import com.google.ortools.linearsolver.MPSolverParameters;
import com.google.ortools.linearsolver.MPVariable;
import com.vaticle.typedb.core.common.exception.TypeDBException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.google.ortools.linearsolver.MPSolverParameters.IncrementalityValues.INCREMENTALITY_ON;
import static com.google.ortools.linearsolver.MPSolverParameters.IntegerParam.INCREMENTALITY;
import static com.google.ortools.linearsolver.MPSolverParameters.IntegerParam.PRESOLVE;
import static com.google.ortools.linearsolver.MPSolverParameters.PresolveValues.PRESOLVE_ON;
import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_STATE;
import static com.vaticle.typedb.core.common.iterator.Iterators.iterate;

public class Solver {

    private final List<IntVariable> variables;
    private final Set<Constraint> constraints;
    private final Map<IntVariable, Double> objectiveCoefficients;
    private SolverStatus status;
    private MPSolver solver;
    private MPSolverParameters parameters;

    private enum SolverStatus {
        INACTIVE, ACTIVE
    }

    public Solver() {
        variables = new ArrayList<>();
        constraints = new HashSet<>();
        objectiveCoefficients = new HashMap<>();
        status = SolverStatus.INACTIVE;
    }

    // TODO think about threading
    public ResultStatus solve(long timeLimitMillis) {
        if (status == SolverStatus.INACTIVE) activate();
        solver.setTimeLimit(timeLimitMillis);
        return ResultStatus.of(solver.solve(parameters));
    }

    private void activate() {
        // TODO think about threading
        solver = MPSolver.createSolver("SCIP");
        solver.objective().setMinimization();
        parameters = new MPSolverParameters();
        parameters.setIntegerParam(PRESOLVE, PRESOLVE_ON.swigValue());
        parameters.setIntegerParam(INCREMENTALITY, INCREMENTALITY_ON.swigValue());
        variables.forEach(var -> var.activate(solver));
        constraints.forEach(constraint -> constraint.activate(solver));
        applyHints();
        status = SolverStatus.ACTIVE;
        assert variables.size() == solver.numVariables();
    }

    public void deactivate() {
        // TODO if this is synchronized, it doesn't have to be idempotent?
        solver.delete();
        parameters.delete();
        variables.forEach(IntVariable::deactivate);
        constraints.forEach(Constraint::deactivate);
        status = SolverStatus.INACTIVE;
        // TODO think about threading
    }

    private void applyHints() {
        assert iterate(variables).allMatch(IntVariable::hasHint);
        MPVariable[] mpVariables = new MPVariable[variables.size()];
        double[] hints = new double[variables.size()];
        for (int i = 0; i < variables.size(); i++) {
            mpVariables[i] = variables.get(i).mpVariable;
            hints[i] = variables.get(i).getHint();
        }
        solver.setHint(mpVariables, hints);
    }

    public enum ResultStatus {
        NOT_SOLVED, OPTIMAL, FEASIBLE, ERROR;

        static ResultStatus of(MPSolver.ResultStatus mpStatus) {
            switch (mpStatus) {
                case NOT_SOLVED:
                    return NOT_SOLVED;
                case OPTIMAL:
                    return OPTIMAL;
                case FEASIBLE:
                    return FEASIBLE;
                case INFEASIBLE:
                case UNBOUNDED:
                case ABNORMAL:
                    return ERROR;
                default:
                    throw TypeDBException.of(ILLEGAL_STATE);
            }
        }
    }

    public void setObjectiveCoefficient(IntVariable var, double coeff) {
        objectiveCoefficients.put(var, coeff);
    }

    public Constraint makeConstraint(double lowerBound, double upperBound, String name) {
        Constraint constraint = new Constraint(lowerBound, upperBound, name);
        constraints.add(constraint);
        return constraint;
    }

    public IntVariable makeIntVar(double lowerBound, double upperBound, String name) {
        IntVariable var = new IntVariable(lowerBound, upperBound, name);
        variables.add(var);
        return var;
    }

    public void resetHints() {
        variables.forEach(IntVariable::clearHint);
    }

    @Override
    public String toString() {
        // TODO use exportLPFormat
        return "Solver{" +
                "variables=" + variables +
                ", constraints=" + constraints +
                ", objectiveCoefficients=" + objectiveCoefficients +
                ", status=" + status +
                ", solver=" + solver +
                ", parameters=" + parameters +
                '}';
    }
}