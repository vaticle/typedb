#
# Copyright (C) 2022 Vaticle
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#

load("@vaticle_bazel_distribution//artifact:rules.bzl", "deploy_artifact")
load("@vaticle_bazel_distribution//common:rules.bzl", "assemble_targz", "assemble_zip", "java_deps")
load("@vaticle_dependencies//tool/checkstyle:rules.bzl", "checkstyle_test")
load("@vaticle_dependencies//distribution:deployment.bzl", "deployment")
load("@vaticle_dependencies//builder/java:rules.bzl", "native_java_libraries")


package(default_visibility = ["//visibility:private",])

filegroup(
    name = "config",
    srcs = ["parameters/config.yml"],
    visibility = ["//visibility:public"],
)

genrule(
    name = "version-src",
    srcs = [
        "templates/Version.java",
        "//:VERSION",
    ],
    cmd = "VERSION=`cat $(location //:VERSION)`;sed -e \"s/{version}/$$VERSION/g\" $(location templates/Version.java) >> $@",
    outs = ["Version.java"],
)

java_library(
    name = "version",
    srcs = [":version-src"],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb-core-version:{pom_version}"],
    visibility = ["//test:__subpackages__"],
)

native_java_libraries(
    name = "server",
    srcs = glob(["*.java", "*/*.java", "*/*/*.java"], exclude=["templates/**", "test/**"]),
    native_libraries_deps = [
        # Internal dependencies
        "//:typedb",
        "//common:common",
        "//concurrent:concurrent",
        "//concept:concept",
        "//logic:logic",
        "//query:query",
        "//database:database",
        "//reasoner:reasoner",
        "//migrator:migrator",
    ],
    deps = [
        ":version",

        # External dependencies from Vaticle
        "@vaticle_typedb_common//:common",
        "@vaticle_typeql//java/pattern:pattern",
        "@vaticle_typeql//java:typeql-lang",
        "@vaticle_typeql//java/query",
        "@vaticle_typeql//java/common",
        "@vaticle_typedb_protocol//grpc/java:typedb-protocol",

        # External dependencies from Maven
        "@maven//:com_google_code_findbugs_jsr305",
        "@maven//:com_google_protobuf_protobuf_java",
        "@maven//:io_grpc_grpc_api",
        "@maven//:io_grpc_grpc_netty",
        "@maven//:io_grpc_grpc_stub",
        "@maven//:io_netty_netty_all",
        "@maven//:io_netty_netty_transport",
        "@maven//:org_slf4j_slf4j_api",
        "@maven//:ch_qos_logback_logback_classic",
        "@maven//:ch_qos_logback_logback_core",
    ],
    runtime_deps = [
        "@maven//:ch_qos_logback_logback_classic",
    ],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb-core-server:{pom_version}"],
    visibility = ["//visibility:public"],
)

genrule(
    name = "prepare-server-directories",
    srcs = [":config"],
    # TODO: can we find a way to create a directory without including an empty file in the outs?
    cmd = "cp $(location :config) $(@D)/conf/ && touch $(@D)/data/empty",
    outs = ["conf/config.yml", "data/empty"]
)

java_binary(
    name = "server-bin-linux-arm64",
    main_class = "com.vaticle.typedb.core.server.TypeDBServer",
    runtime_deps = [":server-linux-arm64"],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb-core-server-bin:{pom_version}"],
    data = [":prepare-server-directories"]
)

java_binary(
    name = "server-bin-linux-x86_64",
    main_class = "com.vaticle.typedb.core.server.TypeDBServer",
    runtime_deps = [":server-linux-x86_64"],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb-core-server-bin:{pom_version}"],
    data = [":prepare-server-directories"]
)

java_binary(
    name = "server-bin-mac-arm64",
    main_class = "com.vaticle.typedb.core.server.TypeDBServer",
    runtime_deps = [":server-mac-arm64"],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb-core-server-bin:{pom_version}"],
    data = [":prepare-server-directories"]
)

java_binary(
    name = "server-bin-mac-x86_64",
    main_class = "com.vaticle.typedb.core.server.TypeDBServer",
    runtime_deps = [":server-mac-x86_64"],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb-core-server-bin:{pom_version}"],
    data = [":prepare-server-directories"]
)

java_binary(
    name = "server-bin-windows-x86_64",
    main_class = "com.vaticle.typedb.core.server.TypeDBServer",
    runtime_deps = [":server-windows-x86_64"],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb-core-server-bin:{pom_version}"],
    data = [":prepare-server-directories"]
)

java_deps(
    name = "server-deps-linux-arm64",
    target = ":server-bin-linux-arm64",
    java_deps_root = "server/lib/",
    visibility = ["//:__pkg__"],
    maven_name = True,
    ignore_missing_maven_name = True,
)

java_deps(
    name = "server-deps-linux-x86_64",
    target = ":server-bin-linux-x86_64",
    java_deps_root = "server/lib/",
    visibility = ["//:__pkg__"],
    maven_name = True,
    ignore_missing_maven_name = True,
)

java_deps(
    name = "server-deps-mac-arm64",
    target = ":server-bin-mac-arm64",
    java_deps_root = "server/lib/",
    visibility = ["//:__pkg__"],
    maven_name = True,
    ignore_missing_maven_name = True,
)

java_deps(
    name = "server-deps-mac-x86_64",
    target = ":server-bin-mac-x86_64",
    java_deps_root = "server/lib/",
    visibility = ["//:__pkg__"],
    maven_name = True,
    ignore_missing_maven_name = True,
)

java_deps(
    name = "server-deps-windows-x86_64",
    target = ":server-bin-windows-x86_64",
    java_deps_root = "server/lib/",
    visibility = ["//:__pkg__"],
    maven_name = True,
    ignore_missing_maven_name = True,
)

assemble_files = {
    "//server:config": "server/conf/config.yml",
    "//server/resources:logo": "server/resources/typedb-ascii.txt",
    "//:LICENSE": "LICENSE",
}

empty_directories = [
    "server/data"
]

permissions = {
    "server/conf/config.yml" : "0755",
    "server/data" : "0755",
}

assemble_targz(
    name = "assemble-linux-arm64-targz",
    targets = ["server-deps-linux-arm64", "@vaticle_typedb_common//binary:assemble-bash-targz"],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-server-linux-arm64",
    visibility = ["//:__pkg__", "//test:__subpackages__"]
)

assemble_targz(
    name = "assemble-linux-x86_64-targz",
    targets = ["server-deps-linux-x86_64", "@vaticle_typedb_common//binary:assemble-bash-targz"],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-server-linux-x86_64",
    visibility = ["//:__pkg__", "//test:__subpackages__"]
)

assemble_zip(
    name = "assemble-mac-arm64-zip",
    targets = ["server-deps-mac-arm64", "@vaticle_typedb_common//binary:assemble-bash-targz"],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-server-mac-arm64",
    visibility = ["//:__pkg__", "//test:__subpackages__"]
)

assemble_zip(
    name = "assemble-mac-x86_64-zip",
    targets = ["server-deps-mac-x86_64", "@vaticle_typedb_common//binary:assemble-bash-targz"],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-server-mac-x86_64",
    visibility = ["//:__pkg__", "//test:__subpackages__"]
)

assemble_zip(
    name = "assemble-windows-x86_64-zip",
    targets = ["server-deps-windows-x86_64", "@vaticle_typedb_common//binary:assemble-bat-targz"],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-server-windows-x86_64",
    visibility = ["//:__pkg__", "//test:__subpackages__"]
)

deploy_artifact(
    name = "deploy-linux-arm64-targz",
    target = ":assemble-linux-arm64-targz",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-server-linux-arm64-{version}.tar.gz",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-linux-x86_64-targz",
    target = ":assemble-linux-x86_64-targz",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-server-linux-x86_64-{version}.tar.gz",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-mac-arm64-zip",
    target = ":assemble-mac-arm64-zip",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-server-mac-arm64-{version}.zip",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-mac-x86_64-zip",
    target = ":assemble-mac-x86_64-zip",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-server-mac-x86_64-{version}.zip",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-windows-x86_64-zip",
    target = ":assemble-windows-x86_64-zip",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-server-windows-x86_64-{version}.zip",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

checkstyle_test(
    name = "checkstyle",
    include = glob(["*", "*/*", "*/*/*"]),
    license_type = "agpl-header",
)
