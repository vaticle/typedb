/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

package com.vaticle.typedb.core.server.parameters.util;

import com.vaticle.typedb.core.common.exception.TypeDBException;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Server.CLI_OPTION_MISSING_PREFIX;

public abstract class SubcommandParser<RESULT> {

    private static final String COMMAND_PREFIX = "typedb server";
    private final String[] tokens;
    private final String description;

    public SubcommandParser(String[] tokens, String description) {
        this.tokens = tokens;
        this.description = description;
    }

    public RESULT parse(String[] args) {
        return parse(parseArgs(args));
    }

    private Set<Option> parseArgs(String[] args) {
        Set<Option> parsed = new HashSet<>();
        for (int i = 0; i < args.length; i++) {
            String arg = args[i];
            if (arg.startsWith(Option.PREFIX)) {
                int index = arg.indexOf("=");
                if (index != -1) {
                    parsed.add(new Option(arg.substring(2, index), arg.substring(index + 1)));
                } else if (i + 1 == args.length || args[i + 1].startsWith(Option.PREFIX)) {
                    parsed.add(new Option(arg.substring(2)));
                } else {
                    parsed.add(new Option(arg.substring(2), args[++i]));
                }
            } else {
                throw TypeDBException.of(CLI_OPTION_MISSING_PREFIX, Option.PREFIX, arg);
            }
        }
        return parsed;
    }

    protected abstract RESULT parse(Set<Option> options);

    public String[] tokens() {
        return tokens;
    }

    public String usage() {
        return COMMAND_PREFIX + " " + String.join(" ", tokens) + "\t\t" + description;
    }

    public String help() {
        StringBuilder builder = new StringBuilder(String.format("%-40s \t\t %s\n", COMMAND_PREFIX + " " +
                String.join(" ", tokens), description));
        for (Help help : helpList()) {
            builder.append(help.toString());
        }
        return builder.toString();
    }

    public abstract List<Help> helpList();

}
