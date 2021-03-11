/*
 * Copyright (C) 2021 Grakn Labs
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
 */

package grakn.core.server;

import grabl.tracing.client.GrablTracingThreadStatic;
import grakn.core.Grakn;
import grakn.core.common.exception.GraknException;
import grakn.core.common.parameters.Arguments;
import grakn.core.common.parameters.Context;
import grakn.core.common.parameters.Options;
import grakn.core.server.common.RequestReader;
import grakn.core.server.common.ResponseBuilder;
import grakn.core.server.common.SynchronizedStreamObserver;
import grakn.core.server.common.TracingData;
import grakn.core.server.concept.ConceptService;
import grakn.core.server.concept.ThingService;
import grakn.core.server.concept.TypeService;
import grakn.core.server.logic.LogicService;
import grakn.core.server.logic.RuleService;
import grakn.core.server.query.QueryService;
import grakn.protocol.TransactionProto;
import io.grpc.Status;
import io.grpc.StatusRuntimeException;
import io.grpc.stub.StreamObserver;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Function;
import java.util.function.Predicate;

import static grabl.tracing.client.GrablTracingThreadStatic.continueTraceOnThread;
import static grakn.core.common.collection.Bytes.bytesToUUID;
import static grakn.core.common.exception.ErrorMessage.Internal.ILLEGAL_ARGUMENT;
import static grakn.core.common.exception.ErrorMessage.Server.DUPLICATE_REQUEST;
import static grakn.core.common.exception.ErrorMessage.Server.EMPTY_TRANSACTION_REQUEST;
import static grakn.core.common.exception.ErrorMessage.Server.ITERATION_WITH_UNKNOWN_ID;
import static grakn.core.common.exception.ErrorMessage.Server.UNKNOWN_REQUEST_TYPE;
import static grakn.core.common.exception.ErrorMessage.Session.SESSION_NOT_FOUND;
import static grakn.core.common.exception.ErrorMessage.Transaction.BAD_TRANSACTION_TYPE;
import static grakn.core.common.exception.ErrorMessage.Transaction.TRANSACTION_ALREADY_OPENED;
import static grakn.core.common.exception.ErrorMessage.Transaction.TRANSACTION_CLOSED;
import static grakn.core.common.exception.ErrorMessage.Transaction.TRANSACTION_NOT_OPENED;
import static grakn.core.server.common.RequestReader.applyDefaultOptions;

public class TransactionService implements StreamObserver<TransactionProto.Transaction.Reqs>, AutoCloseable {

    private static final Logger LOG = LoggerFactory.getLogger(TransactionService.class);
    private static final String TRACE_PREFIX = "transaction_services.";

    private final StreamObserver<TransactionProto.Transaction.Res> responder;
    private final ConcurrentMap<String, BatchedStream<?>> streams;
    private final GraknService graknSrv;
    private final AtomicBoolean isOpen;

    private volatile SessionService sessionSrv;
    private volatile Grakn.Transaction transaction;
    private volatile Services services;
    private volatile int networkLatencyMillis;

    public TransactionService(GraknService graknSrv, StreamObserver<TransactionProto.Transaction.Res> responder) {
        this.responder = SynchronizedStreamObserver.of(responder);
        this.streams = new ConcurrentHashMap<>();
        this.graknSrv = graknSrv;
        this.isOpen = new AtomicBoolean(false);
    }

    private class Services {

        private final ConceptService concept;
        private final LogicService logic;
        private final QueryService query;
        private final ThingService thing;
        private final TypeService type;
        private final RuleService rule;

        private Services() {
            concept = new ConceptService(TransactionService.this, transaction.concepts());
            logic = new LogicService(TransactionService.this, transaction.logic());
            query = new QueryService(TransactionService.this, transaction.query());
            thing = new ThingService(TransactionService.this, transaction.concepts());
            type = new TypeService(TransactionService.this, transaction.concepts());
            rule = new RuleService(TransactionService.this, transaction.logic());
        }
    }

    public Context.Transaction context() {
        return transaction.context();
    }

    @Override
    public void onNext(TransactionProto.Transaction.Reqs requests) {
        if (requests.getTransactionReqsList().isEmpty()) throw GraknException.of(EMPTY_TRANSACTION_REQUEST);
        else for (TransactionProto.Transaction.Req req : requests.getTransactionReqsList()) {
            execute(req);
        }
    }

    @Override
    public void onCompleted() { close(); }

    @Override
    public void onError(Throwable error) { close(error); }

    private synchronized void execute(TransactionProto.Transaction.Req request) {
        GrablTracingThreadStatic.ThreadTrace trace = null;
        try {
            trace = mayStartTrace(request, TRACE_PREFIX + request.getReqCase().name());
            switch (request.getReqCase()) {
                case REQ_NOT_SET:
                    throw GraknException.of(UNKNOWN_REQUEST_TYPE);
                case OPEN_REQ:
                    open(request);
                    break;
                default:
                    executeRequest(request);
            }
        } catch (Exception ex) {
            close(ex);
        } finally {
            mayCloseTrace(trace);
        }
    }

    private void executeRequest(TransactionProto.Transaction.Req request) {
        if (!isOpen.get()) {
            if (transaction != null) throw GraknException.of(TRANSACTION_CLOSED);
            else throw GraknException.of(TRANSACTION_NOT_OPENED);
        }
        switch (request.getReqCase()) {
            case ROLLBACK_REQ:
                rollback(request.getId());
                break;
            case COMMIT_REQ:
                commit(request.getId());
                break;
            case ITERATE_REQ:
                stream(request.getId());
                break;
            case QUERY_REQ:
                services.query.execute(request);
                break;
            case CONCEPT_MANAGER_REQ:
                services.concept.execute(request);
                break;
            case LOGIC_MANAGER_REQ:
                services.logic.execute(request);
                break;
            case THING_REQ:
                services.thing.execute(request);
                break;
            case TYPE_REQ:
                services.type.execute(request);
                break;
            case RULE_REQ:
                services.rule.execute(request);
                break;
            default:
                throw GraknException.of(ILLEGAL_ARGUMENT);
        }
    }

    private void open(TransactionProto.Transaction.Req request) {
        if (isOpen.get()) throw GraknException.of(TRANSACTION_ALREADY_OPENED);
        TransactionProto.Transaction.Open.Req openReq = request.getOpenReq();
        networkLatencyMillis = openReq.getLatencyMillis();
        sessionSrv = sessionService(graknSrv, openReq);
        sessionSrv.register(this);
        transaction = transaction(sessionSrv, openReq);
        services = new Services();
        responder.onNext(ResponseBuilder.Transaction.open(request.getId()));
        isOpen.set(true);
    }

    private static SessionService sessionService(GraknService graknSrv, TransactionProto.Transaction.Open.Req req) {
        UUID sessionID = bytesToUUID(req.getSessionId().toByteArray());
        SessionService sessionSrv = graknSrv.session(sessionID);
        if (sessionSrv == null) throw GraknException.of(SESSION_NOT_FOUND, sessionID);
        return sessionSrv;
    }

    private static Grakn.Transaction transaction(SessionService sessionSrv, TransactionProto.Transaction.Open.Req req) {
        Arguments.Transaction.Type type = Arguments.Transaction.Type.of(req.getType().getNumber());
        if (type == null) throw GraknException.of(BAD_TRANSACTION_TYPE, req.getType());
        Options.Transaction options = new Options.Transaction().parent(sessionSrv.options());
        applyDefaultOptions(options, req.getOptions());
        return sessionSrv.session().transaction(type, options);
    }

    private void commit(String requestID) {
        transaction.commit();
        respond(ResponseBuilder.Transaction.commit(requestID));
        close();
    }

    private void rollback(String requestId) {
        transaction.rollback();
        respond(ResponseBuilder.Transaction.rollback(requestId));
    }

    public void respond(TransactionProto.Transaction.Res response) {
        responder.onNext(response);
    }

    public <T> void stream(Iterator<T> iterator, String requestID,
                           Function<List<T>, TransactionProto.Transaction.Res> responseBuilderFn) {
        int size = transaction.context().options().responseBatchSize();
        stream(iterator, requestID, size, true, responseBuilderFn);
    }

    public <T> void stream(Iterator<T> iterator, String requestID, Options.Query options,
                           Function<List<T>, TransactionProto.Transaction.Res> responseBuilderFn) {
        stream(iterator, requestID, options.responseBatchSize(), options.prefetch(), responseBuilderFn);
    }

    private <T> void stream(Iterator<T> iterator, String requestID, int batchSize, boolean prefetch,
                            Function<List<T>, TransactionProto.Transaction.Res> responseBuilderFn) {
        BatchedStream<T> batchingIterator = new BatchedStream<>(
                iterator, requestID, batchSize, networkLatencyMillis, responseBuilderFn
        );
        streams.compute(requestID, (key, oldValue) -> {
            if (oldValue == null) return batchingIterator;
            else throw GraknException.of(DUPLICATE_REQUEST, requestID);
        });
        if (prefetch) batchingIterator.streamBatches();
        else respond(ResponseBuilder.Transaction.iterate(requestID, true));
    }

    private void stream(String requestId) {
        BatchedStream<?> stream = streams.get(requestId);
        if (stream == null) throw GraknException.of(ITERATION_WITH_UNKNOWN_ID, requestId);
        stream.streamBatches();
    }

    @Nullable
    private GrablTracingThreadStatic.ThreadTrace mayStartTrace(TransactionProto.Transaction.Req request, String name) {
        GrablTracingThreadStatic.ThreadTrace trace = null;
        Optional<TracingData> tracingData = RequestReader.getTracingData(request);
        if (tracingData.isPresent()) {
            trace = continueTraceOnThread(tracingData.get().rootID(), tracingData.get().parentID(), name);
        }
        return trace;
    }

    private void mayCloseTrace(@Nullable GrablTracingThreadStatic.ThreadTrace trace) {
        if (trace != null) trace.close();
    }

    @Override
    public synchronized void close() {
        if (isOpen.compareAndSet(true, false)) {
            transaction.close();
            responder.onCompleted();
            sessionSrv.remove(this);
        }
    }

    public synchronized void close(Throwable error) {
        if (isOpen.compareAndSet(true, false)) {
            transaction.close();
            responder.onError(ResponseBuilder.exception(error));
            sessionSrv.remove(this);
            if (error instanceof StatusRuntimeException &&
                    ((StatusRuntimeException) error).getStatus() == Status.CANCELLED) {
                LOG.debug(error.getMessage(), error);
            } else {
                LOG.error(error.getMessage(), error);
            }
        }
    }

    private class BatchedStream<T> {

        private static final int MAX_LATENCY_MILLIS = 3_000;

        private final Iterator<T> iterator;
        private final String requestID;
        private final Function<List<T>, TransactionProto.Transaction.Res> responseBuilderFn;
        private final int batchSize;
        private final int latencyMillis;

        BatchedStream(Iterator<T> iterator, String requestID, int batchSize, int latencyMillis,
                      Function<List<T>, TransactionProto.Transaction.Res> responseBuilderFn) {
            this.iterator = iterator;
            this.requestID = requestID;
            this.batchSize = batchSize;
            this.responseBuilderFn = responseBuilderFn;
            this.latencyMillis = Math.min(latencyMillis, MAX_LATENCY_MILLIS);
        }

        private void streamBatches() {
            streamBatchesUntil(i -> i < batchSize && iterator.hasNext());
            if (mayClose()) return;
            else respond(ResponseBuilder.Transaction.iterate(requestID, true));
            Instant compensationTime = Instant.now().plusMillis(latencyMillis);
            streamBatchesUntil(i -> iterator.hasNext() && Instant.now().isBefore(compensationTime));
            mayClose();
        }

        private void streamBatchesUntil(Predicate<Integer> predicate) {
            List<T> answers = new ArrayList<>();
            Instant startTime = Instant.now();
            for (int i = 0; predicate.test(i); i++) {
                answers.add(iterator.next());
                Instant currentTime = Instant.now();
                if (Duration.between(startTime, currentTime).toMillis() >= 1) {
                    respond(responseBuilderFn.apply(answers));
                    answers.clear();
                    startTime = currentTime;
                }
            }

            if (!answers.isEmpty()) respond(responseBuilderFn.apply(answers));
        }

        private boolean mayClose() {
            if (!iterator.hasNext()) respond(ResponseBuilder.Transaction.iterate(requestID, false));
            return !iterator.hasNext();
        }
    }
}
