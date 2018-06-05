/*
 * Grakn - A Distributed Semantic Database
 * Copyright (C) 2016-2018 Grakn Labs Limited
 *
 * Grakn is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Grakn is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with Grakn. If not, see <http://www.gnu.org/licenses/agpl.txt>.
 */

package ai.grakn.bootup.graknengine;

import ai.grakn.GraknSystemProperty;
import ai.grakn.bootup.graknengine.pid.GraknPidFileStore;
import ai.grakn.bootup.graknengine.pid.GraknPidManager;
import ai.grakn.bootup.graknengine.pid.GraknPidStore;
import ai.grakn.engine.GraknEngineServerFactory;
import ai.grakn.engine.GraknEngineServer;
import ai.grakn.util.ErrorMessage;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;

/**
 *
 * Main class invoked by the 'grakn' bash script.
 *
 * NOTE: Please keep the class name "Grakn" as it is what will be displayed to the user.
 *
 * @author Ganeshwara Herawan Hananda
 * @author Michele Orsi
 *
 */
public class Grakn {

    private static final Logger LOG = LoggerFactory.getLogger(Grakn.class);

    /**
     *
     * Invocation from class '{@link ai.grakn.bootup.GraknBootup}'
     *
     * @param args
     */
    public static void main(String[] args) {
        Thread.setDefaultUncaughtExceptionHandler((Thread t, Throwable e) ->
                LOG.error(ErrorMessage.UNCAUGHT_EXCEPTION.getMessage(t.getName()), e));

        try {
            String graknPidFileProperty = Optional.ofNullable(GraknSystemProperty.GRAKN_PID_FILE.value())
                    .orElseThrow(() -> new RuntimeException(ErrorMessage.GRAKN_PIDFILE_SYSTEM_PROPERTY_UNDEFINED.getMessage()));

            Path pidfile = Paths.get(graknPidFileProperty);
            GraknPidStore graknPidStore = new GraknPidFileStore(pidfile);
            GraknPidManager graknPidManager = new GraknPidManager(graknPidStore);
            graknPidManager.trackGraknPid();

            // Start Engine
            GraknEngineServer graknEngineServer = GraknEngineServerFactory.createGraknEngineServer();
            graknEngineServer.start();
        } catch (IOException e) {
            LOG.error(ErrorMessage.UNCAUGHT_EXCEPTION.getMessage(), e);
        }
    }
}

