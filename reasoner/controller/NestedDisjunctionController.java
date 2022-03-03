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

package com.vaticle.typedb.core.reasoner.controller;

import com.vaticle.typedb.core.concept.answer.ConceptMap;
import com.vaticle.typedb.core.concurrent.actor.ActorExecutorGroup;
import com.vaticle.typedb.core.pattern.Disjunction;
import com.vaticle.typedb.core.reasoner.computation.actor.Monitor;

import java.util.function.Function;

public class NestedDisjunctionController
        extends DisjunctionController<NestedDisjunctionController.NestedDisjunctionProcessor, NestedDisjunctionController>{

    private final Monitor.MonitorRef monitorRef;

    public NestedDisjunctionController(Driver<NestedDisjunctionController> driver, Disjunction disjunction,
                                       ActorExecutorGroup executorService, Monitor.MonitorRef monitorRef, Registry registry) {
        super(driver, disjunction, executorService, registry);
        this.monitorRef = monitorRef;
    }

    @Override
    protected Function<Driver<NestedDisjunctionProcessor>, NestedDisjunctionProcessor> createProcessorFunc(ConceptMap bounds) {
        return driver -> new NestedDisjunctionProcessor(
                driver, driver(), monitorRef, disjunction, bounds,
                NestedDisjunctionProcessor.class.getSimpleName() + "(pattern:" + disjunction + ", bounds: " + bounds + ")"
        );
    }

    @Override
    public NestedDisjunctionController asController() {
        return this;
    }

    protected static class NestedDisjunctionProcessor
            extends DisjunctionController.DisjunctionProcessor<NestedDisjunctionController, NestedDisjunctionProcessor> {

        protected NestedDisjunctionProcessor(Driver<NestedDisjunctionProcessor> driver,
                                             Driver<NestedDisjunctionController> controller,
                                             Monitor.MonitorRef monitorRef, Disjunction disjunction, ConceptMap bounds, String name) {
            super(driver, controller, monitorRef, disjunction, bounds, name);
        }
    }
}
