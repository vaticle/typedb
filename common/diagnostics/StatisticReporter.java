/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

package com.vaticle.typedb.core.common.diagnostics;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ssl.HttpsURLConnection;
import java.io.IOException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import static java.lang.Math.abs;
import static java.util.concurrent.TimeUnit.MINUTES;

public class StatisticReporter {
    protected static final int REPORT_INTERVAL_MINUTES = 60;
    public static final String DISABLED_REPORTING_FILE_NAME = "_reporting_disabled";

    protected static final Logger LOG = LoggerFactory.getLogger(StatisticReporter.class);
    private final String deploymentID;
    private final Metrics metrics;
    private final boolean statisticsReportingEnabled;
    private final String reportingURI;
    private final Path dataDirectory;

    private ScheduledFuture<?> reportScheduledTask;
    private final ScheduledThreadPoolExecutor scheduled = new ScheduledThreadPoolExecutor(1);

    public StatisticReporter(String deploymentID, Metrics metrics, boolean statisticsReportingEnabled, String reportingURI, Path dataDirectory) {
        this.deploymentID = deploymentID;
        this.metrics = metrics;
        this.statisticsReportingEnabled = statisticsReportingEnabled;
        this.reportingURI = reportingURI;
        this.dataDirectory = dataDirectory;
    }

    public void startReporting() {
        if (statisticsReportingEnabled) {
            deleteDisabledReportingFileIfExists();
            scheduleReporting();
        } else {
            reportOnceIfNeeded();
        }
    }

    private boolean report() {
        try {
            String metricsJSON = metrics.formatReportingJSON();
            metrics.takeSnapshot(); // Forget about this period for consistency even if the https write is not successful

            HttpsURLConnection conn = (HttpsURLConnection) (new URL(reportingURI)).openConnection();

            conn.setRequestMethod("POST");
            conn.setRequestProperty("Charset", "utf-8");
            conn.setRequestProperty("Connection", "close");
            conn.setRequestProperty("Content-Type", "application/json");

            conn.setDoOutput(true);
            conn.getOutputStream().write(metricsJSON.getBytes(StandardCharsets.UTF_8));

            conn.connect();
            conn.getInputStream().readAllBytes();
            return true;
        } catch (Exception e) {
            if (LOG.isTraceEnabled()) LOG.trace("Failed to push diagnostics to {}: {}", reportingURI, e.getMessage());
            // do nothing and try again after the standard delay
            return false;
        }
    }

    private void scheduleReporting() {
        reportScheduledTask = scheduled.scheduleAtFixedRate(this::report, 1, 1, MINUTES);
    }

    private void reportOnceIfNeeded() {
        Path disabledReportingFile = dataDirectory.resolve(DISABLED_REPORTING_FILE_NAME);
        if (!disabledReportingFile.toFile().exists()) {
            scheduled.schedule(() -> {
                if (report()) {
                    saveDisabledReportingFile();
                }
            }, 1, TimeUnit.SECONDS);
        }
    }

    private void saveDisabledReportingFile() {
        try {
            Path disabledReportingFile = dataDirectory.resolve(DISABLED_REPORTING_FILE_NAME);
            Files.writeString(disabledReportingFile, LocalDateTime.now().toString());
        } catch (IOException e) {
            LOG.debug("Failed to save disabled reporting file: ", e);
        }
    }

    private void deleteDisabledReportingFileIfExists() {
        try {
            Files.deleteIfExists(dataDirectory.resolve(DISABLED_REPORTING_FILE_NAME));
        } catch (IOException e) {
            LOG.debug("Failed to delete disabled reporting file: ", e);
        }
    }

    private long calculateInitialDelay() {
        assert(REPORT_INTERVAL_MINUTES == 60); // Modify the algorithm if you change this value!
        int currentMinute = LocalDateTime.now().getMinute();
        int scheduledMinute = abs(deploymentID.hashCode()) % REPORT_INTERVAL_MINUTES;

        if (currentMinute > scheduledMinute) {
            return 60 - currentMinute + scheduledMinute;
        } else {
            return scheduledMinute - currentMinute;
        }
    }
}
