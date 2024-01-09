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

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

def vaticle_bazel_distribution():
    git_repository(
        name = "vaticle_bazel_distribution",
        remote = "https://github.com/krishnangovindraj/bazel-distribution",
        commit = "4f6130fae3595bda08eb73121ce1d5b411b6289d",
    )

def vaticle_dependencies():
    git_repository(
        name = "vaticle_dependencies",
        remote = "https://github.com/krishnangovindraj/dependencies",
        commit = "da4f5ba66210f830ab1847cf88296bec31c48455", # sync-marker: do not remove this comment, this is used for sync-dependencies by @vaticle_dependencies
    )

def vaticle_typeql():
    git_repository(
        name = "vaticle_typeql",
        remote = "https://github.com/krishnangovindraj/typeql",
        commit = "d2316604b44710a9d965f6273aa80182ba7c9de8",  # sync-marker: do not remove this comment, this is used for sync-dependencies by @vaticle_typeql
    )

def vaticle_typedb_common():
    git_repository(
        name = "vaticle_typedb_common",
        remote = "https://github.com/krishnangovindraj/typedb-common",
        commit = "9574419264352ce3eae620aaae87ed99d1706fe2",  # sync-marker: do not remove this comment, this is used for sync-dependencies by @vaticle_typedb_common
    )

def vaticle_typedb_protocol():
    git_repository(
        name = "vaticle_typedb_protocol",
        remote = "https://github.com/krishnangovindraj/typedb-protocol",
        commit = "472e871deff2baaa0e1fe0d7657e82c10687354a"
    )

def vaticle_typedb_behaviour():
    git_repository(
        name = "vaticle_typedb_behaviour",
        remote = "https://github.com/vaticle/typedb-behaviour",
        commit = "7bfccec5e600bf385dc64f493473897a639ec68c" # sync-marker: do not remove this comment, this is used for sync-dependencies by @vaticle_typedb_behaviour
    )
