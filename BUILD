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

load("//:deployment.bzl", deployment_github = "deployment", deployment_docker = "deployment")
load("@vaticle_bazel_distribution//apt:rules.bzl", "assemble_apt", "deploy_apt")
load("@vaticle_bazel_distribution//artifact:rules.bzl", "deploy_artifact")
load("@vaticle_bazel_distribution//brew:rules.bzl", "deploy_brew")
load("@vaticle_bazel_distribution//common:rules.bzl", "assemble_targz", "assemble_zip", "checksum", "assemble_versioned")
load("@vaticle_bazel_distribution//github:rules.bzl", "deploy_github")
load("@vaticle_bazel_distribution//common/targz:rules.bzl", "targz_edit")
load("@vaticle_dependencies//builder/java:rules.bzl", "native_java_libraries")
load("@vaticle_dependencies//distribution:deployment.bzl", "deployment")
load("@vaticle_dependencies//distribution/artifact:rules.bzl", "artifact_repackage")
load("@vaticle_dependencies//tool/checkstyle:rules.bzl", "checkstyle_test")
load("@vaticle_dependencies//tool/release/deps:rules.bzl", "release_validate_deps")
load("@io_bazel_rules_docker//container:image.bzl", docker_container_image = "container_image")
load("@io_bazel_rules_docker//container:container.bzl", docker_container_push = "container_push")

exports_files(
    ["VERSION", "deployment.bzl", "LICENSE", "README.md"],
)

native_java_libraries(
    name = "typedb",
    srcs = glob(["*.java"]),
    native_libraries_deps = [
        # Internal dependencies
        "//common:common",
        "//concept:concept",
        "//logic:logic",
        "//query:query",
    ],
    deps = [
        # Vaticle Dependencies
        "@vaticle_typedb_common//:common",
    ],
    tags = ["maven_coordinates=com.vaticle.typedb:typedb:{pom_version}"],
    visibility = ["//visibility:public"],
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

artifact_repackage(
    name = "console-artifact-jars-linux-arm64",
    srcs = ["@vaticle_typedb_console_artifact_linux-arm64//file"],
    files_to_keep = ["console"],
)

assemble_targz(
    name = "assemble-linux-arm64-targz",
    targets = [
        ":console-artifact-jars-linux-arm64",
        "//server:server-deps-linux-arm64",
        "@vaticle_typedb_common//binary:assemble-bash-targz"
    ],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-all-linux-arm64",
)

artifact_repackage(
    name = "console-artifact-jars-linux-x86_64",
    srcs = ["@vaticle_typedb_console_artifact_linux-x86_64//file"],
    files_to_keep = ["console"],
)

assemble_targz(
    name = "assemble-linux-x86_64-targz",
    targets = [
        ":console-artifact-jars-linux-x86_64",
        "//server:server-deps-linux-x86_64",
        "@vaticle_typedb_common//binary:assemble-bash-targz"
    ],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-all-linux-x86_64",
)

artifact_repackage(
    name = "console-artifact-jars-mac-arm64",
    srcs = ["@vaticle_typedb_console_artifact_mac-arm64//file"],
    files_to_keep = ["console"],
)

assemble_zip(
    name = "assemble-mac-arm64-zip",
    targets = [
        "//server:server-deps-mac-arm64",
        ":console-artifact-jars-mac-arm64",
        "@vaticle_typedb_common//binary:assemble-bash-targz",
    ],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-all-mac-arm64",
)

artifact_repackage(
    name = "console-artifact-jars-mac-x86_64",
    srcs = ["@vaticle_typedb_console_artifact_mac-x86_64//file"],
    files_to_keep = ["console"],
)

assemble_zip(
    name = "assemble-mac-x86_64-zip",
    targets = [
        "//server:server-deps-mac-x86_64",
        ":console-artifact-jars-mac-x86_64",
        "@vaticle_typedb_common//binary:assemble-bash-targz",
    ],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-all-mac-x86_64",
)

artifact_repackage(
    name = "console-artifact-jars-windows-x86_64",
    srcs = ["@vaticle_typedb_console_artifact_windows-x86_64//file"],
    files_to_keep = ["console"],
)

assemble_zip(
    name = "assemble-windows-x86_64-zip",
    targets = [
        "//server:server-deps-windows-x86_64",
        ":console-artifact-jars-windows-x86_64",
        "@vaticle_typedb_common//binary:assemble-bat-targz",
    ],
    additional_files = assemble_files,
    empty_directories = empty_directories,
    permissions = permissions,
    output_filename = "typedb-all-windows-x86_64",
)

deploy_artifact(
    name = "deploy-linux-arm64-targz",
    target = ":assemble-linux-arm64-targz",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-all-linux-arm64-{version}.tar.gz",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-linux-x86_64-targz",
    target = ":assemble-linux-x86_64-targz",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-all-linux-x86_64-{version}.tar.gz",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-mac-arm64-zip",
    target = ":assemble-mac-arm64-zip",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-all-mac-arm64-{version}.zip",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-mac-x86_64-zip",
    target = ":assemble-mac-x86_64-zip",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-all-mac-x86_64-{version}.zip",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

deploy_artifact(
    name = "deploy-windows-x86_64-zip",
    target = ":assemble-windows-x86_64-zip",
    artifact_group = "vaticle_typedb",
    artifact_name = "typedb-all-windows-x86_64-{version}.zip",
    release = deployment['cloudsmith.release'],
    snapshot = deployment['cloudsmith.snapshot'],
)

assemble_versioned(
    name = "assemble-versioned-all",
    targets = [
        ":assemble-linux-arm64-targz",
        ":assemble-linux-x86_64-targz",
        ":assemble-mac-arm64-zip",
        ":assemble-mac-x86_64-zip",
        ":assemble-windows-x86_64-zip",
        "//server:assemble-linux-arm64-targz",
        "//server:assemble-linux-x86_64-targz",
        "//server:assemble-mac-arm64-zip",
        "//server:assemble-mac-x86_64-zip",
        "//server:assemble-windows-x86_64-zip",
    ],
)

assemble_versioned(
    name = "assemble-versioned-mac",
    targets = [":assemble-mac-arm64-zip"],
)

checksum(
    name = "checksum-mac-arm64",
    archive = ":assemble-mac-arm64-zip",
)

checksum(
    name = "checksum-mac-x86_64",
    archive = ":assemble-mac-x86_64-zip",
)

deploy_github(
    name = "deploy-github",
    organisation = deployment_github['github.organisation'],
    repository = deployment_github['github.repository'],
    title = "TypeDB",
    title_append_version = True,
    release_description = "//:RELEASE_NOTES_LATEST.md",
    archive = ":assemble-versioned-all",
    draft = False
)

deploy_brew(
    name = "deploy-brew",
    snapshot = deployment['brew.snapshot'],
    release = deployment['brew.release'],
    formula = "//config/brew:typedb.rb",
    file_substitutions = {
        "//:checksum-mac-arm64": "{sha256-arm64}",
        "//:checksum-mac-x86_64": "{sha256-x86_64}",
    },
    version_file = "//:VERSION"
)

apt_depends = ["default-jre"]
apt_installation_dir = "/opt/typedb/core/"
apt_empty_dirs =[
    "/var/log/typedb/",
    "/opt/typedb/core/server/lib/",
    "/var/lib/typedb/core/data/",
    "/opt/typedb/core/console/lib/",
]
apt_symlinks = {
    "/opt/typedb/core/server/data": "/var/lib/typedb/core/data/",
    "/usr/local/bin/typedb": "/opt/typedb/core/typedb",
    "/opt/typedb/core/server/logs": "/var/log/typedb/",
    "/usr/lib/systemd/system/typedb.service": "/opt/typedb/core/typedb.service",
}

targz_edit(
    name = "console-artifact-native-x86_64.tar.gz",
    src = "@vaticle_typedb_console_artifact_linux-x86_64//file",
    strip_components = 1,
)

assemble_apt(
    name = "assemble-linux-x86_64-apt",
    package_name = "typedb",
    maintainer = "Vaticle <community@vaticle.com>",
    description = "TypeDB",
    depends = apt_depends,
    workspace_refs = "@vaticle_typedb_workspace_refs//:refs.json",
    archives = [
        "//server:server-deps-linux-x86_64",
        ":console-artifact-native-x86_64.tar.gz",
        "@vaticle_typedb_common//binary:assemble-bash-targz",
        "@vaticle_typedb_common//binary:assemble-apt-targz",
    ],
    installation_dir = apt_installation_dir,
    files = assemble_files,
    empty_dirs = apt_empty_dirs,
    empty_dirs_permission = "0777",
    symlinks = apt_symlinks,
    architecture = "amd64",
)

deploy_apt(
    name = "deploy-apt-x86_64",
    target = ":assemble-linux-x86_64-apt",
    snapshot = deployment['cloudsmith.snapshot'],
    release = deployment['cloudsmith.release'],
)

targz_edit(
    name = "console-artifact-native-arm64.tar.gz",
    src = "@vaticle_typedb_console_artifact_linux-arm64//file",
    strip_components = 1,
)

assemble_apt(
    name = "assemble-linux-arm64-apt",
    package_name = "typedb",
    maintainer = "Vaticle <community@vaticle.com>",
    description = "TypeDB",
    depends = apt_depends,
    workspace_refs = "@vaticle_typedb_workspace_refs//:refs.json",
    archives = [
        "//server:server-deps-linux-arm64",
        ":console-artifact-native-arm64.tar.gz",
        "@vaticle_typedb_common//binary:assemble-bash-targz",
        "@vaticle_typedb_common//binary:assemble-apt-targz",
    ],
    installation_dir = apt_installation_dir,
    files = assemble_files,
    empty_dirs = apt_empty_dirs,
    empty_dirs_permission = "0777",
    symlinks = apt_symlinks,
    architecture = "arm64",
)

deploy_apt(
    name = "deploy-apt-arm64",
    target = ":assemble-linux-arm64-apt",
    snapshot = deployment['cloudsmith.snapshot'],
    release = deployment['cloudsmith.release'],
)

release_validate_deps(
    name = "release-validate-deps",
    refs = "@vaticle_typedb_workspace_refs//:refs.json",
    tagged_deps = [
        "@vaticle_typeql",
        "@vaticle_typedb_common",
        "@vaticle_typedb_protocol",
    ],
    tags = ["manual"]  # in order for bazel test //... to not fail
)

docker_container_image(
    name = "assemble-docker",
    base = "@vaticle_ubuntu_image//image",
    tars = [":assemble-linux-x86_64-targz"],
    directory = "opt",
    workdir = "/opt/typedb-all-linux-x86_64",
    ports = ["1729"],
    env = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
    },
    cmd = ["/opt/typedb-all-linux-x86_64/typedb", "server"],
    volumes = ["/opt/typedb-all-linux-x86_64/server/data/"],
    visibility = ["//test:__subpackages__"],
)

docker_container_push(
    name = "deploy-docker-release-overwrite-latest-tag",
    image = ":assemble-docker",
    format = "Docker",
    registry = deployment_docker["docker.index"],
    repository = "{}/{}".format(
        deployment_docker["docker.organisation"],
        deployment_docker["docker.release.repository"],
    ),
    tag = "latest"
)

docker_container_push(
    name = "deploy-docker-release",
    image = ":assemble-docker",
    format = "Docker",
    registry = deployment_docker["docker.index"],
    repository = "{}/{}".format(
        deployment_docker["docker.organisation"],
        deployment_docker["docker.release.repository"],
    ),
    tag_file = ":VERSION",
)

checkstyle_test(
    name = "checkstyle",
    include = glob(["*", ".factory/*", "bin/*", ".circleci/*"]),
    exclude = glob([
        "*.md",
        ".circleci/windows/*",
        "docs/*",
        "tools/**",
    ]) + [
        ".bazelversion",
        ".bazel-remote-cache.rc",
        ".bazel-cache-credential.json",
        "LICENSE",
        "VERSION",
    ],
    license_type = "agpl-header",
)

checkstyle_test(
    name = "checkstyle-license",
    include = ["LICENSE"],
    license_type = "agpl-fulltext",
)

# CI targets that are not declared in any BUILD file, but are called externally
filegroup(
    name = "ci",
    data = [
        "@vaticle_dependencies//factory/analysis:dependency-analysis",
        "@vaticle_dependencies//library/maven:update",
        "@vaticle_dependencies//tool/bazelinstall:remote_cache_setup.sh",
        "@vaticle_dependencies//tool/release/notes:create",
        "@vaticle_dependencies//tool/checkstyle:test-coverage",
        "@vaticle_dependencies//tool/unuseddeps:unused-deps",
    ],
)
