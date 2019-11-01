// Copyright 2017 JanusGraph Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package grakn.core.graph.diskstorage.util;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import grakn.core.graph.diskstorage.BackendException;
import grakn.core.graph.diskstorage.Entry;
import grakn.core.graph.diskstorage.EntryList;
import grakn.core.graph.diskstorage.StaticBuffer;
import grakn.core.graph.diskstorage.keycolumnvalue.KeyColumnValueStore;
import grakn.core.graph.diskstorage.keycolumnvalue.KeyIterator;
import grakn.core.graph.diskstorage.keycolumnvalue.KeyRangeQuery;
import grakn.core.graph.diskstorage.keycolumnvalue.KeySliceQuery;
import grakn.core.graph.diskstorage.keycolumnvalue.SliceQuery;
import grakn.core.graph.diskstorage.keycolumnvalue.StoreTransaction;
import grakn.core.graph.util.stats.MetricManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.List;
import java.util.Map;

/**
 * This class instruments an arbitrary KeyColumnValueStore backend with Metrics.
 * The cumulative runtime of, number of invocations of, and number of exceptions
 * thrown by each interface method are instrumented with Metrics (using Timer,
 * Counter, and Counter again, respectively). The Metric names are generated by
 * calling MetricRegistry#name(Class, String...)},
 * where methodName is the exact name of the method including capitalization,
 * and identifier is "time", "calls", or "exceptions".
 * <p>
 * In addition to the three standard metrics, {@code getSlice} and
 * {@code getKeys} have some additional metrics related to their return values.
 * {@code getSlice} carries metrics with the identifiers "entries-returned" and
 * "entries-histogram". The first is a counter of total Entry objects returned.
 * The second is a histogram of the size of Entry lists returned.
 * {@code getKeys} returns a {@link RecordIterator} that manages metrics for its
 * methods.
 * <p>
 * This implementation does not catch any exceptions. Exceptions emitted by the
 * backend store implementation are guaranteed to pass through this
 * implementation's methods.
 * <p>
 * The implementation includes repeated {@code try...catch} boilerplate that
 * could be reduced by using reflection to determine the method name and by
 * delegating Metrics object handling to a common helper that takes a Callable
 * closure, but I'm not sure that the extra complexity and potential performance
 * hit is worth it.
 *
 * @author Dan LaRocque (dalaro@hopcount.org)
 */
public class MetricInstrumentedStore implements KeyColumnValueStore {

    private final KeyColumnValueStore backend;

    private static final Logger LOG = LoggerFactory.getLogger(MetricInstrumentedStore.class);

    public static final String M_CONTAINS_KEY = "containsKey";
    public static final String M_GET_SLICE = "getSlice";
    public static final String M_MUTATE = "mutate";
    public static final String M_ACQUIRE_LOCK = "acquireLock";
    public static final String M_GET_KEYS = "getKeys";
    public static final String M_GET_PART = "getLocalKeyPartition";
    public static final String M_CLOSE = "close";

    public static final List<String> OPERATION_NAMES =
            ImmutableList.of(M_CONTAINS_KEY, M_GET_SLICE, M_MUTATE, M_ACQUIRE_LOCK, M_GET_KEYS);

    public static final String M_CALLS = "calls";
    public static final String M_TIME = "time";
    public static final String M_EXCEPTIONS = "exceptions";
    public static final String M_ENTRIES_COUNT = "entries-returned";
    public static final String M_ENTRIES_HISTO = "entries-histogram";

    public static final List<String> EVENT_NAMES =
            ImmutableList.of(M_CALLS, M_TIME, M_EXCEPTIONS, M_ENTRIES_COUNT, M_ENTRIES_HISTO);

    public static final String M_ITERATOR = "iterator";

    private final String metricsStoreName;

    public MetricInstrumentedStore(KeyColumnValueStore backend, String metricsStoreName) {
        this.backend = backend;
        this.metricsStoreName = metricsStoreName;
        LOG.debug("Wrapped Metrics named \"{}\" around store {}", metricsStoreName, backend);
    }

    @Override
    public EntryList getSlice(KeySliceQuery query, StoreTransaction txh) throws BackendException {
        return runWithMetrics(txh, metricsStoreName, M_GET_SLICE, () -> {
            final EntryList result = backend.getSlice(query, txh);
            recordSliceMetrics(txh, result);
            return result;
        });
    }

    @Override
    public Map<StaticBuffer, EntryList> getSlice(List<StaticBuffer> keys,
                                                 final SliceQuery query,
                                                 final StoreTransaction txh) throws BackendException {
        return runWithMetrics(txh, metricsStoreName, M_GET_SLICE, () -> {
            final Map<StaticBuffer, EntryList> results = backend.getSlice(keys, query, txh);

            for (EntryList result : results.values()) {
                recordSliceMetrics(txh, result);
            }
            return results;
        });
    }

    @Override
    public void mutate(StaticBuffer key,
                       final List<Entry> additions,
                       final List<StaticBuffer> deletions,
                       final StoreTransaction txh) throws BackendException {
        runWithMetrics(txh, metricsStoreName, M_MUTATE, (StorageCallable<Void>) () -> {
            backend.mutate(key, additions, deletions, txh);
            return null;
        });
    }

    @Override
    public void acquireLock(StaticBuffer key,
                            final StaticBuffer column,
                            final StaticBuffer expectedValue,
                            final StoreTransaction txh) throws BackendException {
        runWithMetrics(txh, metricsStoreName, M_ACQUIRE_LOCK, (StorageCallable<Void>) () -> {
            backend.acquireLock(key, column, expectedValue, txh);
            return null;
        });
    }

    @Override
    public KeyIterator getKeys(KeyRangeQuery query, StoreTransaction txh) throws BackendException {
        return runWithMetrics(txh, metricsStoreName, M_GET_KEYS, () -> {
            final KeyIterator ki = backend.getKeys(query, txh);
//            if (txh.getConfiguration().hasGroupName()) {
//                return MetricInstrumentedIterator.of(ki, txh.getConfiguration().getGroupName(), metricsStoreName, M_GET_KEYS, M_ITERATOR);
//            } else {
            return ki;
//            }
        });
    }

    @Override
    public KeyIterator getKeys(SliceQuery query, StoreTransaction txh) throws BackendException {
        return runWithMetrics(txh, metricsStoreName, M_GET_KEYS, () -> {
            final KeyIterator ki = backend.getKeys(query, txh);
//            if (txh.getConfiguration().hasGroupName()) {
//                return MetricInstrumentedIterator.of(ki, txh.getConfiguration().getGroupName(), metricsStoreName, M_GET_KEYS, M_ITERATOR);
//            } else {
            return ki;
//            }
        });
    }

    @Override
    public String getName() {
        return backend.getName();
    }

    @Override
    public void close() throws BackendException {
        backend.close();
    }

    private void recordSliceMetrics(StoreTransaction txh, List<Entry> row) {
        if (!txh.getConfiguration().hasGroupName())
            return;

        String p = txh.getConfiguration().getGroupName();
        final MetricManager mgr = MetricManager.INSTANCE;
//        mgr.getCounter(p, metricsStoreName, M_GET_SLICE, M_ENTRIES_COUNT).inc(row.size());
//        mgr.getHistogram(p, metricsStoreName, M_GET_SLICE, M_ENTRIES_HISTO).update(row.size());
    }

    static <T> T runWithMetrics(StoreTransaction txh, String storeName, String name, StorageCallable<T> impl) throws BackendException {

        if (!txh.getConfiguration().hasGroupName()) {
            return impl.call();
        }
        String prefix = txh.getConfiguration().getGroupName();
        Preconditions.checkNotNull(name);
        Preconditions.checkNotNull(impl);

        final MetricManager mgr = MetricManager.INSTANCE;
//        mgr.getCounter(prefix, storeName, name, M_CALLS).inc();
//        final Timer.Context tc = mgr.getTimer(prefix, storeName, name, M_TIME).time();

//        try {
        return impl.call();
//        } catch (BackendException | RuntimeException e) {
////            mgr.getCounter(prefix, storeName, name, M_EXCEPTIONS).inc();
//            throw e;
//        } finally {
////            tc.stop();
//        }
    }

    static <T> void runWithMetrics(String prefix, String name, IOCallable<T> impl) throws IOException {

        if (null == prefix) {
            impl.call();
            return;
        }

        Preconditions.checkNotNull(name);
        Preconditions.checkNotNull(impl);

        final MetricManager mgr = MetricManager.INSTANCE;
//        mgr.getCounter(prefix, null, MetricInstrumentedIterator.M_CLOSE, M_CALLS).inc();
//        final Timer.Context tc = mgr.getTimer(prefix, null, MetricInstrumentedIterator.M_CLOSE, M_TIME).time();

//        try {
        impl.call();
//        } catch (IOException e) {
//            mgr.getCounter(prefix, null, MetricInstrumentedIterator.M_CLOSE, M_EXCEPTIONS).inc();
//            throw e;
//        } finally {
//            tc.stop();
//        }
    }

    static <T> T runWithMetrics(String prefix, String name, UncheckedCallable<T> impl) {

        if (null == prefix) {
            return impl.call();
        }

        Preconditions.checkNotNull(name);
        Preconditions.checkNotNull(impl);

        final MetricManager mgr = MetricManager.INSTANCE;

//        mgr.getCounter(prefix, null, name, M_CALLS).inc();
//
//        final Timer.Context tc = mgr.getTimer(prefix, null, name, M_TIME).time();
//
//        try {
        return impl.call();
//        } catch (RuntimeException e) {
//            mgr.getCounter(prefix, null, name, M_EXCEPTIONS).inc();
//            throw e;
//        } finally {
//            tc.stop();
//        }
    }
}
