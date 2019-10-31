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

package grakn.core.graph.diskstorage;


import org.janusgraph.diskstorage.BaseTransaction;
import org.janusgraph.diskstorage.BaseTransactionConfig;

/**
 * An extension to the {@link BaseTransaction} interface that exposes a
 * configuration object of type {@link BaseTransactionConfig} for this particular transaction.
 *
 */
public interface BaseTransactionConfigurable extends BaseTransaction {

    /**
     * Get the configuration for this transaction
     *
     * @return
     */
    BaseTransactionConfig getConfiguration();

}
