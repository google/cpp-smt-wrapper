#
# Copyright 2023 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Generic SMT interface
#
# Clients should include a solver factory header, use the factory to create a
# solver, and then use the generic API in smt.h for all operations.
#
# Public API targets are marked with "//visibility:public"

# Libraries
# ===========================================================================

# Mock SMT solver for testing purposes.
cc_library(
    name = "mock_smt_lib",
    testonly = 1,
    srcs = ["mock_smt.h"],
    hdrs = ["mock_smt.h"],
    visibility = ["//visibility:public"],
    deps = [
        ":smt_lib",
        "@com_google_googletest//:gtest",
	      "@com_google_absl//absl/status:status",
        "@com_google_absl//absl/status:statusor",
    ],
)

# Generic SMT API Library.
cc_library(
    name = "smt_lib",
    srcs = [
        "smt.cc",
        "smt_ops.cc",
    ],
    hdrs = [
        "smt.h",
        "smt_ops.h",
        "smt_solver_factory.h",
        "smt_term.h",
    ],
    visibility = ["//visibility:public"],
    deps = [
	"//src/base:source_location",
        "@com_google_absl//absl/container:node_hash_map",
	"@com_google_absl//absl/status:status",
        "@com_google_absl//absl/status:statusor",
	"@com_google_absl//absl/strings:strings",
        "@com_google_absl//absl/types:optional",
	"@com_google_absl//absl/log:check",
	"@com_google_absl//absl/log:log",
    ],
)

# Implementation of an SMT interface for the Z3 Solver.
# Note that exceptions are enabled in this library for the sole purpose
# of catching exceptions thrown by Z3 and isolating the client from
# them.  No exceptions escape into client code.
cc_library(
    name = "z3_smt_lib",
    srcs = [
        "z3_smt_solver.cc",
        "z3_smt_solver_factory.cc",
    ],
    hdrs = [
        "z3_smt_solver.h",
        "z3_smt_solver_factory.h",
    ],
    copts = ["-fexceptions", "-Wno-sign-compare"],
    features = ["-use_header_modules"],  # Incompatible with -fexceptions.
    visibility = ["//visibility:public"],
    deps = [
        ":smt_lib",
        "@com_google_absl//absl/container:node_hash_map",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/strings:str_format",
        "//:z3",
	"@com_google_re2//:re2",
    ],
)

cc_library(
    name = "printing_smt_lib",
    srcs = [
        "printing_smt_solver.cc",
        "printing_smt_solver_factory.cc",
    ],
    hdrs = [
        "printing_smt_solver.h",
        "printing_smt_solver_factory.h",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":smt_lib",
	":z3_smt_lib",
	"@com_google_absl//absl/container:node_hash_map",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/strings",
    ],
)

# Tests
# ===========================================================================

# SMT operator tests.
cc_test(
    name = "smt_ops_test",
    size = "small",
    srcs = ["smt_ops_test.cc"],
    deps = [
        ":smt_lib",
        "@com_google_googletest//:gtest_main",
        "@com_google_absl//absl/types:optional",
    ],
)

# General SMT library tests.
cc_test(
    name = "smt_lib_test",
    size = "medium",
    srcs = ["smt_test.cc"],
    deps = [
        ":printing_smt_lib",
        ":smt_lib",
        ":z3_smt_lib",
	"//src/base/testing:status_matchers",
        "@com_google_googletest//:gtest_main",
        "@com_google_absl//absl/debugging:leak_check",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/strings",
    ],
)

# Z3-specific SMT library tests. Requires the use of "-fexeptions" because the
# tests utilize Z3 internal C++ types, that load a header file which includes
# exceptions.
cc_test(
    name = "z3_smt_lib_test",
    size = "small",
    srcs = ["z3_smt_solver_test.cc"],
    copts = ["-fexceptions"],
    features = ["-use_header_modules"],  # Incompatible with -fexceptions.
    deps = [
        ":smt_lib",
        ":z3_smt_lib",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_test(
    name = "printing_smt_lib_test",
    size = "small",
    srcs = ["printing_smt_solver_test.cc"],
    deps = [
        ":printing_smt_lib",
        ":smt_lib",
        "@com_google_googletest//:gtest_main",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
    ],
)
