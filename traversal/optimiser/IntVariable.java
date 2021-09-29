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
import com.google.ortools.linearsolver.MPVariable;

public class IntVariable extends Variable {

    private final double lowerBound;
    private final double upperBound;
    private Status status;
    private Integer initial;
    private Integer solution;
    MPVariable mpVariable;

    public IntVariable(double lowerBound, double upperBound, String name) {
        super(name);
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
        this.status = Status.INACTIVE;
    }

    @Override
    MPVariable mpVariable() {
        assert status == Status.ACTIVE;
        return mpVariable;
    }

    @Override
    public void recordValue() {
        assert status == Status.ACTIVE;
        solution = (int) Math.round(mpVariable.solutionValue());
    }

    public int solutionValue() {
        assert solution != null;
        return solution;
    }

    @Override
    public void activate(MPSolver mpSolver) {
        assert status == Status.INACTIVE;
        // TODO think about threading, idempotency
        this.mpVariable = mpSolver.makeIntVar(lowerBound, upperBound, name);
        this.status = Status.ACTIVE;
    }

    @Override
    public void deactivate() {
        this.mpVariable.delete();
        this.status = Status.INACTIVE;
    }

    @Override
    public boolean hasInitial() {
        return initial != null;
    }

    public void setInitial(int initial) {
        this.initial = initial;
    }

    @Override
    public void clearInitial() {
        initial = null;
    }

    @Override
    public double getInitial() {
        assert hasInitial();
        return initial;
    }

}
