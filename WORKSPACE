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

workspace(name = "vaticle_typedb")

################################
# Load @vaticle_dependencies #
################################

load("//dependencies/vaticle:repositories.bzl", "vaticle_dependencies")
vaticle_dependencies()

# Load //builder/bazel for RBE
load("@vaticle_dependencies//builder/bazel:deps.bzl", "bazel_toolchain")
bazel_toolchain()

# Load //builder/java
load("@vaticle_dependencies//builder/java:deps.bzl", java_deps = "deps")
java_deps()
load("@vaticle_dependencies//library/maven:rules.bzl", "maven")

load("@rules_jvm_external//:repositories.bzl", "rules_jvm_external_deps")
rules_jvm_external_deps()

# Load //builder/antlr
load("@vaticle_dependencies//builder/antlr:deps.bzl", antlr_deps = "deps", "antlr_version")
antlr_deps()

load("@rules_antlr//antlr:lang.bzl", "JAVA")
load("@rules_antlr//antlr:repositories.bzl", "rules_antlr_dependencies")
rules_antlr_dependencies(antlr_version, JAVA)

# Load //builder/kotlin
load("@vaticle_dependencies//builder/kotlin:deps.bzl", kotlin_deps = "deps")
kotlin_deps()
load("@io_bazel_rules_kotlin//kotlin:repositories.bzl", "kotlin_repositories")
kotlin_repositories()
load("@io_bazel_rules_kotlin//kotlin:core.bzl", "kt_register_toolchains")
kt_register_toolchains()

# Load //builder/grpc
load("@vaticle_dependencies//builder/grpc:deps.bzl", grpc_deps = "deps")
grpc_deps()

load("@rules_proto_grpc//:repositories.bzl", "rules_proto_grpc_repos", "rules_proto_grpc_toolchains")
rules_proto_grpc_toolchains()
rules_proto_grpc_repos()

load("@rules_proto_grpc//java:repositories.bzl", rules_proto_grpc_java_repos = "java_repos")
rules_proto_grpc_java_repos()

load("@io_grpc_grpc_java//:repositories.bzl", "IO_GRPC_GRPC_JAVA_ARTIFACTS")
load("@vaticle_dependencies//library/maven:rules.bzl", "parse_unversioned")
io_grpc_artifacts = [parse_unversioned(c) for c in IO_GRPC_GRPC_JAVA_ARTIFACTS]

# Load //builder/python
load("@vaticle_dependencies//builder/python:deps.bzl", python_deps = "deps")
python_deps()

# Load //tool/common
load("@vaticle_dependencies//tool/common:deps.bzl", "vaticle_dependencies_ci_pip",
    vaticle_dependencies_tool_maven_artifacts = "maven_artifacts")
vaticle_dependencies_ci_pip()

# Load //tool/checkstyle
load("@vaticle_dependencies//tool/checkstyle:deps.bzl", checkstyle_deps = "deps")
checkstyle_deps()

# Load //tool/unuseddeps
load("@vaticle_dependencies//tool/unuseddeps:deps.bzl", unuseddeps_deps = "deps")
unuseddeps_deps()

######################################
# Load @vaticle_bazel_distribution #
######################################

load("//dependencies/vaticle:repositories.bzl", "vaticle_bazel_distribution")
vaticle_bazel_distribution()

# Load //common
load("@vaticle_bazel_distribution//common:deps.bzl", "rules_pkg")
rules_pkg()
load("@rules_pkg//:deps.bzl", "rules_pkg_dependencies")
rules_pkg_dependencies()

# Load //github
load("@vaticle_bazel_distribution//github:deps.bzl", github_deps = "deps")
github_deps()

# Load //pip
load("@vaticle_bazel_distribution//pip:deps.bzl", pip_deps = "deps")
pip_deps()

# Load @vaticle_bazel_distribution_cloudsmith
load("@vaticle_bazel_distribution//common/cloudsmith:deps.bzl", cloudsmith_deps = "deps")
cloudsmith_deps()
load("@vaticle_bazel_distribution_cloudsmith//:requirements.bzl", install_cloudsmith_deps = "install_deps")
install_cloudsmith_deps()

######################################
# Load @vaticle_dependencies//distribution/docker #
######################################

# must be loaded after `vaticle_bazel_distribution` to ensure
# `rules_pkg` is correctly patched (bazel-distribution #251)

# Load //distribution/docker
load("@vaticle_dependencies//distribution/docker:deps.bzl", docker_deps = "deps")
docker_deps()

load("@io_bazel_rules_go//go:deps.bzl", "go_register_toolchains", "go_rules_dependencies")
load("@bazel_gazelle//:deps.bzl", "gazelle_dependencies", "go_repository")
go_rules_dependencies()
go_register_toolchains(version = "1.18.3")
gazelle_dependencies()

load("@io_bazel_rules_docker//repositories:repositories.bzl", bazel_rules_docker_repositories = "repositories")
bazel_rules_docker_repositories()

load("@io_bazel_rules_docker//repositories:deps.bzl", bazel_rules_docker_container_deps = "deps")
bazel_rules_docker_container_deps()

load("@io_bazel_rules_docker//container:container.bzl", "container_pull")
container_pull(
  name = "vaticle_ubuntu_image",
  registry = "index.docker.io",
  repository = "vaticle/ubuntu",
  tag = "4ee548cea883c716055566847c4736a7ef791c38"
)

#####################################
# Load @vaticle/typedb dependencies #
#####################################

# We don't load Maven artifacts for @vaticle_typedb_common as they are only needed
# if you depend on @vaticle_typedb_common//test/server
load("//dependencies/vaticle:repositories.bzl", "vaticle_typedb_common","vaticle_typeql", "vaticle_typedb_protocol", "vaticle_typedb_behaviour")
vaticle_typedb_common()
vaticle_typeql()
vaticle_typedb_protocol()
vaticle_typedb_behaviour()

load("//dependencies/vaticle:artifacts.bzl", "vaticle_typedb_console_artifact")
vaticle_typedb_console_artifact()

# Load maven artifacts
load("@vaticle_typedb_common//dependencies/maven:artifacts.bzl", vaticle_typedb_common_artifacts = "artifacts")
load("@vaticle_typeql//dependencies/maven:artifacts.bzl", vaticle_typeql_artifacts = "artifacts")
load("@vaticle_typedb_protocol//dependencies/maven:artifacts.bzl", vaticle_typedb_protocol_artifacts = "artifacts")
load("//dependencies/maven:artifacts.bzl", vaticle_typedb_artifacts = "artifacts")

############################
# Load @maven dependencies #
############################
load("@vaticle_dependencies//library/maven:rules.bzl", "maven")
maven(
    vaticle_typedb_common_artifacts  +
    vaticle_dependencies_tool_maven_artifacts +
    vaticle_typeql_artifacts +
    vaticle_typedb_artifacts +
    io_grpc_artifacts,
    generate_compat_repositories = True,
)

load("@maven//:compat.bzl", "compat_repositories")
compat_repositories()

###############################################
# Create @vaticle_typedb_workspace_refs #
###############################################

load("@vaticle_bazel_distribution//common:rules.bzl", "workspace_refs")
workspace_refs(name = "vaticle_typedb_workspace_refs")
