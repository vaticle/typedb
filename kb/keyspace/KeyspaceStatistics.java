/*
 * Copyright (C) 2020 Grakn Labs
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

package grakn.core.kb.keyspace;

import grakn.core.kb.concept.api.Label;
import grakn.core.kb.concept.manager.ConceptManager;

/**
 * Store a shared map of statistics attached to each type
 */
public interface KeyspaceStatistics {
    long count(ConceptManager conceptManager, Label label);

    // TODO - not implemented yet
    long countOwnerships(ConceptManager conceptManager, Label owner, Label attributeOwned);
    void commit(ConceptManager conceptManager, StatisticsDelta statisticsDelta);
}
