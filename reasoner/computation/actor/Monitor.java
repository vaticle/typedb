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

package com.vaticle.typedb.core.reasoner.computation.actor;

import com.vaticle.typedb.core.concurrent.actor.Actor;
import com.vaticle.typedb.core.reasoner.computation.reactive.Reactive;
import com.vaticle.typedb.core.reasoner.utils.Tracer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class Monitor extends Actor<Monitor> {

    private static final Logger LOG = LoggerFactory.getLogger(Controller.class);
    private boolean terminated;
    // TODO: Reactive elements from inside other actors shouldn't have been sent here over an actor boundary.
    private final Map<Reactive, Set<Reactive.Provider<?>>> paths;
    private final Map<Reactive, Set<ReactiveGraph>> reactiveGraphMembership;
    private final Map<Reactive, Integer> reactiveAnswerCounts;
    private final Set<Reactive.Provider<?>> sources;
    private final Set<Reactive.Provider<?>> finishedSources;

    public Monitor(Driver<Monitor> driver, String name) {
        super(driver, name);
        this.paths = new HashMap<>();
        this.reactiveGraphMembership = new HashMap<>();
        this.reactiveAnswerCounts = new HashMap<>();
        this.sources = new HashSet<>();
        this.finishedSources = new HashSet<>();
    }

    private <R> void registerRoot(Driver<? extends Processor<R, ?, ?, ?>> processor, Reactive.Receiver.Finishable<R> receiver) {
        // We assume that this is called before the root has any connected paths registered
        // TODO: What if a new root is registered which shares paths with an already complete ReactiveGraph? It should be able to find all of its contained paths
        ReactiveGraph reactiveGraph = new ReactiveGraph(processor, receiver);
        reactiveGraphMembership.computeIfAbsent(receiver, r -> new HashSet<>()).add(reactiveGraph);
    }

    private <R> void registerPath(Reactive.Receiver<R> receiver, Reactive.Provider<R> provider) {
        paths.computeIfAbsent(receiver, p -> new HashSet<>()).add(provider);
        Set<ReactiveGraph> receiverGraphs = reactiveGraphMembership.get(receiver);
        if (receiverGraphs != null) {
            addToGraphs(provider, receiverGraphs);
            propagateReactiveGraphs(provider, receiverGraphs);
        }
    }

    void addToGraphs(Reactive.Provider<?> provider, Set<ReactiveGraph> reactiveGraphs) {
        Set<ReactiveGraph> providerGraphs = reactiveGraphMembership.computeIfAbsent(provider, r -> new HashSet<>());
        providerGraphs.addAll(reactiveGraphs);
        reactiveGraphs.forEach(g -> g.reactives.add(provider));
    }

    private <R> void propagateReactiveGraphs(Reactive.Provider<R> provider, Set<ReactiveGraph> parentGraphs) {
        Set<Reactive.Provider<?>> children = paths.get(provider);
        children.forEach(child -> {
            addToGraphs(child, parentGraphs);
            propagateReactiveGraphs(child, parentGraphs);
        });
    }

    private <R> void registerSource(Reactive.Provider<R> source) {
        sources.add(source);
    }

    private <R> void sourceFinished(Reactive.Provider<R> source) {
        finishedSources.add(source);
        checkFinished(reactiveGraphMembership.get(source));
    }

    private <R> void createAnswer(int numCreated, Reactive.Provider<R> provider) {
        reactiveAnswerCounts.putIfAbsent(provider, 0);
        reactiveAnswerCounts.computeIfPresent(provider, (r, c) -> c + numCreated);
        checkFinished(reactiveGraphMembership.get(provider));
    }

    private <R> void consumeAnswer(Reactive.Receiver<R> receiver) {
        Integer newCount = reactiveAnswerCounts.computeIfPresent(receiver, (r, c) -> c - 1);
        assert newCount != null;
        checkFinished(reactiveGraphMembership.get(receiver));
    }

    private void checkFinished(Set<ReactiveGraph> reactiveGraphs) {
        reactiveGraphs.forEach(reactiveGraph -> reactiveGraph.checkFinished(reactiveAnswerCounts, sources, finishedSources));
    }

    private static class ReactiveGraph {

        private final Driver<? extends Processor<?, ?, ?, ?>> rootProcessor;
        private final Reactive.Receiver.Finishable<?> root;
        private final Set<Reactive> reactives;

        ReactiveGraph(Driver<? extends Processor<?,?,?,?>> rootProcessor, Reactive.Receiver.Finishable<?> root) {
            this.rootProcessor = rootProcessor;
            this.root = root;
            this.reactives = new HashSet<>();
            this.reactives.add(root);
        }

        void checkFinished(Map<Reactive, Integer> reactiveAnswerCounts, Set<Reactive.Provider<?>> sources,
                           Set<Reactive.Provider<?>> finishedSources) {
            if (sourcesFinished(sources, finishedSources) && count(reactiveAnswerCounts) == 0) {
                rootProcessor.execute(actor -> actor.onFinished(root));
            }
        }

        private boolean sourcesFinished(Set<Reactive.Provider<?>> sources, Set<Reactive.Provider<?>> finishedSources) {
            Set<Reactive> unfinished = new HashSet<>(sources);
            unfinished.retainAll(reactives);
            unfinished.removeAll(finishedSources);
            return unfinished.isEmpty();
        }

        int count(Map<Reactive, Integer> reactiveAnswerCounts) {
            int count = 0;
            for (Reactive reactive : reactives) count += reactiveAnswerCounts.get(reactive);
            assert count >= 0;
            return count;
        }

    }

    @Override
    protected void exception(Throwable e) {

    }

    public void terminate(Throwable cause) {
        LOG.debug("Actor terminated.", cause);
        this.terminated = true;
    }

    public static class MonitorRef {  // TODO: Rename to MonitorWrapper

        private final Driver<Monitor> monitor;

        public MonitorRef(Driver<Monitor> monitor) {
            this.monitor = monitor;
        }

        public <R> void registerRoot(Driver<? extends Processor<R, ?, ?, ?>> processor, Reactive.Receiver.Finishable<R> receiver) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.registerRoot(receiver, monitor));
            monitor.execute(actor -> actor.registerRoot(processor, receiver));
        }

        public <R> void registerPath(Reactive.Receiver<R> receiver, @Nullable Reactive.Provider<R> provider) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.registerPath(receiver, provider, monitor));
            monitor.execute(actor -> actor.registerPath(receiver, provider));
        }

        public <R> void registerSource(Reactive.Provider<R> source) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.registerSource(source, monitor));
            monitor.execute(actor -> actor.registerSource(source));
        }

        public <R> void sourceFinished(Reactive.Provider<R> provider) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.sourceFinished(provider, monitor));
            monitor.execute(actor -> actor.sourceFinished(provider));
        }

        public <R> void createAnswer(Reactive.Provider<R> provider) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.createAnswer(1, provider, monitor));
            monitor.execute(actor -> actor.createAnswer(1, provider));
        }

        public <R> void createAnswer(int numCreated, Reactive.Provider<R> provider) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.createAnswer(numCreated, provider, monitor));
            monitor.execute(actor -> actor.createAnswer(numCreated, provider));
        }

        public <R> void consumeAnswer(Reactive.Receiver<R> receiver) {
            Tracer.getIfEnabled().ifPresent(tracer -> tracer.consumeAnswer(receiver, monitor));
            monitor.execute(actor -> actor.consumeAnswer(receiver));
        }

        public void syncAndReportPathFork(int numForks, Reactive forker) {
        }

        public void syncAndReportPathJoin(Reactive joiner) {
        }

        public void reportPathJoin(Reactive joiner) {
        }

    }

}
