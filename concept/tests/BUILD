# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

load("@vaticle_dependencies//tool/checkstyle:rules.bzl", "checkstyle_test")
load("@rules_rust//rust:defs.bzl", "rust_test")
package(default_visibility = ["//visibility:public",])

rust_test(
    name = "test_statistics",
    srcs = glob([
        "test_statistics.rs",
    ]),
    deps = [
        "//common/bytes",
        "//common/lending_iterator",
        "//common/logger",
        "//common/primitive",
        "//concept",
        "//encoding",
        "//storage",
        "//durability",
        "//util/test:test_utils",

        "@crates//:rand",
        "@crates//:tracing",
    ]
)

rust_test(
    name = "test_thing",
    srcs = glob([
        "test_thing.rs",
    ]),
    deps = [
        "//common/bytes",
        "//common/lending_iterator",
        "//common/logger",
        "//common/primitive",
        "//concept",
        "//encoding",
        "//storage",
        "//durability",
        "//util/test:test_utils",

        "@crates//:rand",
        "@crates//:tracing",
    ]
)

rust_test(
    name = "test_type",
    srcs = glob([
        "test_type.rs",
    ]),
    deps = [
        "//common/bytes",
        "//common/logger",
        "//common/primitive",
        "//concept",
        "//encoding",
        "//storage",
        "//durability",
        "//util/test:test_utils",

        "@crates//:rand",
        "@crates//:tracing",
    ]
)

checkstyle_test(
    name = "checkstyle",
    include = glob(["*", "*/*", "*/*/*"]),
    license_type = "mpl-header",
)
