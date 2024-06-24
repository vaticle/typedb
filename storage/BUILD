# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

load("@vaticle_dependencies//tool/checkstyle:rules.bzl", "checkstyle_test")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
package(default_visibility = [
    "//concept:__subpackages__",
    "//database:__subpackages__",
    "//encoding:__subpackages__",
    "//ir:__subpackages__",
    "//server:__subpackages__",
    "//storage/tests:__subpackages__",
    "//storage/benches:__subpackages__",
    "//traversal:__subpackages__",
    "//tests:__subpackages__",
])

rust_library(
    name = "storage",
    crate_root = "storage.rs",
    srcs = glob([
        "*.rs",
        "keyspace/*.rs",
        "snapshot/*.rs",
        "recovery/*.rs",
    ]),
    deps = [
        "//common/bytes",
        "//common/iterator",
        "//common/lending_iterator",
        "//common/logger",
        "//common/primitive",
        "//durability",
        "//resource",
        "//util/project",

        "@crates//:bincode",
        "@crates//:lz4",
        "@crates//:chrono",
        "@crates//:itertools",
        "@crates//:same-file",
        "@crates//:serde",
        "@crates//:rocksdb",
        "@crates//:tracing",
    ]
)

rust_test(
    name = "storage_unit_tests",
    crate = ":storage",
    deps = ["//util/test:test_utils"],
)

checkstyle_test(
    name = "checkstyle",
    include = glob([
        "*",
        "keyspace/*",
        "recovery/*",
        "snapshot/*",
    ]),
    exclude = glob([
        "Cargo.*",
    ]),
    license_type = "mpl-header",
)
