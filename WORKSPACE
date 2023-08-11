#
# Copyright 2023 Google Inc
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

workspace(name = "com_google_smt_wrappers")

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# Load Dependencies

# Abseil libraries
http_archive(
  name = "com_google_absl",
  urls = ["https://github.com/abseil/abseil-cpp/archive/refs/tags/20230125.3.zip"],
  strip_prefix = "abseil-cpp-20230125.3",
)

# Bazel Skylib rules for Absiel
http_archive(
  name = "bazel_skylib",
  urls = ["https://github.com/bazelbuild/bazel-skylib/releases/download/1.2.1/bazel-skylib-1.2.1.tar.gz"],
  sha256 = "f7be3474d42aae265405a592bb7da8e171919d74c16f082a5457840f06054728",
)

# GoogleTest / Google Mock
http_archive(
  name = "com_google_googletest",
  urls = ["https://github.com/google/googletest/archive/refs/tags/v1.13.0.zip"],
  strip_prefix = "googletest-1.13.0",
)

# Google Benchmark
http_archive(
    name = "com_github_google_benchmark",
    urls = ["https://github.com/google/benchmark/archive/bf585a2789e30585b4e3ce6baf11ef2750b54677.zip"],
    strip_prefix = "benchmark-bf585a2789e30585b4e3ce6baf11ef2750b54677",
    sha256 = "2a778d821997df7d8646c9c59b8edb9a573a6e04c534c01892a40aa524a7b68c",
)

# RE2
http_archive(
  name = "com_google_re2",
  urls = ["https://github.com/google/re2/archive/refs/tags/2023-06-02.zip"],
  strip_prefix = "re2-2023-06-02",
)

# CC Foreign Dependencies rule repository
http_archive(
    name = "rules_foreign_cc",
    strip_prefix = "rules_foreign_cc-0.9.0",
    url = "https://github.com/bazelbuild/rules_foreign_cc/archive/0.9.0.tar.gz",
)

load("@rules_foreign_cc//foreign_cc:repositories.bzl", "rules_foreign_cc_dependencies")

rules_foreign_cc_dependencies()


_ALL_CONTENT = """\
filegroup(
    name = "all_srcs",
    srcs = glob(["**"]),
    visibility = ["//visibility:public"],
)
"""

# CVC4
http_archive(
  name = "cvc4",
  build_file_content = _ALL_CONTENT,
  urls = ["https://github.com/CVC4/CVC4-archived/archive/refs/tags/1.8.zip"], 
  strip_prefix = "CVC4-archived-1.8",
)

# Z3
# Note: Update version numbers from build in ./BUILD.bazel for the appropriate .so objects built.
http_archive(
  name = "z3",
  build_file_content = _ALL_CONTENT,
  urls = ["https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.12.2.zip"],
  strip_prefix = "z3-z3-4.12.2",
)


