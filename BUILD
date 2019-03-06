#
# GRAKN.AI - THE KNOWLEDGE GRAPH
# Copyright (C) 2018 Grakn Labs Ltd
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

exports_files(["grakn", "VERSION", "deployment.properties"], visibility = ["//visibility:public"])
load("@graknlabs_bazel_distribution//apt:rules.bzl", "assemble_apt", "deploy_apt")
load("@graknlabs_bazel_distribution//brew:rules.bzl", "deploy_brew")
load("@graknlabs_bazel_distribution//common:rules.bzl", "assemble_targz", "java_deps", "assemble_zip")
load("@graknlabs_bazel_distribution//github:rules.bzl", "deploy_github")
load("@graknlabs_bazel_distribution//rpm:rules.bzl", "assemble_rpm", "deploy_rpm")
load("@io_bazel_rules_docker//container:image.bzl", "container_image")
load("@io_bazel_rules_docker//container:container.bzl", "container_push")


deploy_github(
    name = "deploy-github-zip",
    target = ":assemble-zip-mac",
    deployment_properties = ":deployment.properties",
    version_file = "//:VERSION"
)


assemble_targz(
    name = "assemble-targz",
    targets = ["//server:server-deps",
               "//console:console-deps",
               "//bin:assemble-targz-bash"],
    additional_files = {
       "//server:services/cassandra/cassandra.yaml": "server/services/cassandra/cassandra.yaml",
       "//server:services/cassandra/logback.xml": "server/services/cassandra/logback.xml",
       "//server:services/grakn/grakn-core-ascii.txt": "server/services/grakn/grakn-core-ascii.txt",
    },
    empty_directories = [
        "server/db/cassandra",
        "server/db/queue"
    ],
    permissions = {
        "server/services/cassandra/cassandra.yaml": "0777",
        "server/db/cassandra": "0777",
        "server/db/queue": "0777",
    },
    output_filename = "grakn-core-all",
)

assemble_zip(
    name = "assemble-zip-mac",
    targets = ["//server:server-deps",
               "//console:console-deps",
               "//bin:assemble-targz-bash"],
    additional_files = {
        "//server:services/cassandra/cassandra.yaml": "server/services/cassandra/cassandra.yaml",
        "//server:services/cassandra/logback.xml": "server/services/cassandra/logback.xml",
        "//server:services/grakn/grakn-core-ascii.txt": "server/services/grakn/grakn-core-ascii.txt",
    },
    empty_directories = [
        "server/db/cassandra",
        "server/db/queue"
    ],
    permissions = {
        "server/services/cassandra/cassandra.yaml": "0777",
        "server/db/cassandra": "0777",
        "server/db/queue": "0777",
    },
    output_filename = "grakn-core-all-mac",
    visibility = ["//visibility:public"]
)

assemble_zip(
    name = "assemble-zip-windows",
    targets = ["//server:server-deps",
               "//console:console-deps",
               "//bin:assemble-targz-bat"],
    additional_files = {
        "//server:services/cassandra/cassandra.yaml": "server/services/cassandra/cassandra.yaml",
        "//server:services/cassandra/logback.xml": "server/services/cassandra/logback.xml",
        "//server:services/grakn/grakn-core-ascii.txt": "server/services/grakn/grakn-core-ascii.txt",
    },
    empty_directories = [
        "server/db/cassandra",
        "server/db/queue"
    ],
    permissions = {
        "server/services/cassandra/cassandra.yaml": "0777",
        "server/db/cassandra": "0777",
        "server/db/queue": "0777",
    },
    output_filename = "grakn-core-all-windows",
    visibility = ["//visibility:public"]
)

deploy_brew(
    name = "deploy-brew",
    version_file = "//:VERSION"
)

container_image(
    name = "assemble-docker",
    base = "@openjdk_image//image",
    tars = [":assemble-targz"],
    files = ["//bin:grakn-docker.sh"],
    ports = ["48555"],
    cmd = ["./grakn-docker.sh"],
    volumes = ["/server/db"]
)


container_push(
    name = "deploy-docker",
    image = ":assemble-docker",
    format = "Docker",
    registry = "index.docker.io",
    repository = "graknlabs/grakn-core",
)


# When a Bazel build or test is executed with RBE, it will be executed using the following platform.
# The platform is based on the standard rbe_ubuntu1604 from @bazel_toolchains,
# but with an additional setting dockerNetwork = standard because our tests need network access
platform(
    name = "rbe-platform",
    parents = ["@bazel_toolchains//configs/ubuntu16_04_clang/1.1:rbe_ubuntu1604"],
    remote_execution_properties = """
        {PARENT_REMOTE_EXECUTION_PROPERTIES}
        properties: {
          name: "dockerNetwork"
          value: "standard"
        }
        """,
)
