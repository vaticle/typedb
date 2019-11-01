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

package grakn.core.graph.graphdb.configuration;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import grakn.core.graph.core.JanusGraphFactory;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Collection of constants used throughput the JanusGraph codebase.
 */
public class JanusGraphConstants {

    public static final String JANUSGRAPH_PROPERTIES_FILE = "janusgraph.internal.properties";

    /**
     * Runtime version of JanusGraph, as read from a properties file inside the core jar
     */
    public static final String VERSION;

    /**
     * Name of the ids.store-name used by JanusGraph which is configurable
     */
    public static final String JANUSGRAPH_ID_STORE_NAME = "janusgraph_ids";

    /**
     * Storage format version currently used by JanusGraph, version 1 is for JanusGraph 0.2.x and below
     */
    public static final String STORAGE_VERSION;


    /**
     * List of FIXED fields that can be modified when graph.allow-upgrade is set to true
     */
    public static final Set<String> UPGRADEABLE_FIXED;

    static {

        /*
         * Preempt some potential NPEs with Preconditions bearing messages. They
         * are unlikely to fail outside of some crazy test environment. Still,
         * if something goes horribly wrong, even a cryptic error message is
         * better than a message-less NPE.
         */
        Package p = JanusGraphConstants.class.getPackage();
        Preconditions.checkNotNull(p, "Unable to load package containing class " + JanusGraphConstants.class);
        String packageName = p.getName();
        Preconditions.checkNotNull(packageName, "Unable to get name of package containing " + JanusGraphConstants.class);
        String resourceName = packageName.replace('.', '/') + "/" + JANUSGRAPH_PROPERTIES_FILE;

        Properties props = new Properties();

        try (InputStream is = JanusGraphFactory.class.getClassLoader().getResourceAsStream(resourceName)) {
            Preconditions.checkNotNull(is, "Unable to locate classpath resource " + resourceName + " containing JanusGraph version");
            props.load(is);
        } catch (IOException e) {
            throw new RuntimeException("Failed to load properties from " + resourceName, e);
        }

        VERSION = props.getProperty("janusgraph.version");
        STORAGE_VERSION = props.getProperty("janusgraph.storage-version");
        UPGRADEABLE_FIXED = getPropertySet(props, "janusgraph.upgradeable-fixed");
    }

    private static Set<String> getPropertySet(Properties props, String key) {
        ImmutableSet.Builder<String> buildSet = ImmutableSet.builder();
        buildSet.addAll(Stream.of(props.getProperty(key, "").split(",")).map(String::trim).filter(s -> !s.isEmpty()).collect(Collectors.toList()));
        return buildSet.build();
    }
}
