/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

package com.vaticle.typedb.core.server.common;

import java.io.File;
import java.nio.file.Path;

import static com.vaticle.typedb.core.server.common.Util.getTypedbDir;

public class Constants {

    static final File ASCII_LOGO_FILE = getTypedbDir().resolve("server/resources/typedb-ascii.txt").toFile();
    public static final Path CONFIG_PATH = getTypedbDir().resolve("server/conf/config.yml");
    public static final String TYPEDB_DISTRIBUTION_NAME = "TypeDB Core";
    public static final String TYPEDB_LOG_FILE_NAME = "typedb";
    public static final String TYPEDB_LOG_FILE_EXT = ".log";
    public static final String TYPEDB_LOG_ARCHIVE_EXT = ".log.gz";
    public static final String ERROR_REPORTING_URI = "https://3d710295c75c81492e57e1997d9e01e1@o4506315929812992.ingest.sentry.io/4506316048629760";
    public static final String DIAGNOSTICS_REPORTING_URI = "https://diagnostics.typedb.dev/";
    public static final String SERVER_ID_FILE_NAME = "_server_id";
    public static final int SERVER_ID_LENGTH = 16;
    public static final String SERVER_ID_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
}
