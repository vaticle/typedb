/*
 * Copyright (C) 2022 Vaticle
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

package com.vaticle.typedb.core.common.parameters;

import com.vaticle.typedb.core.common.exception.ErrorMessage;
import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.protocol.ConceptProto;

public class Concept {
    public enum Transitivity {
        EXPLICIT,
        TRANSITIVE;

        public static Transitivity of(ConceptProto.Type.Transitivity proto) {
            switch (proto) {
                case EXPLICIT: return EXPLICIT;
                case TRANSITIVE: return TRANSITIVE;
                case UNRECOGNIZED:
                default:
                    throw TypeDBException.of(ErrorMessage.Server.BAD_VALUE_TYPE, proto);
            }
        }
    }

    public enum OwnsFilter {
        KEYS,
        ALL;

        public static OwnsFilter of(ConceptProto.Type.OwnsFilter proto) {
            switch (proto) {
                case KEYS_ONLY: return KEYS;
                case ALL: return ALL;
                case UNRECOGNIZED:
                default:
                    throw TypeDBException.of(ErrorMessage.Server.BAD_VALUE_TYPE, proto);
            }
        }
    }

    public enum Existence {
        STORED, INFERRED,
    }
}
