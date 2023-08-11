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

# For similar functionality outside of this library, please duplicate these
# libraries instead of relying on them directly. These may be updated or removed
# in future versions if the functionality they provide is implemented by a common provider such as Abseil.

package_group(
  name = "smt_impl",
  packages = [
    "//src/smt",
    "//src/base/...",
  ],
)

cc_library(
    name = "source_location",
    hdrs = ["source_location.h"],
    deps = ["@com_google_absl//absl/base:config"],
    visibility = [":smt_impl"],
)

cc_test(
    name = "source_location_test",
    srcs = ["source_location_test.cc"],
    deps = [
        ":source_location",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_library(
    name = "status_helpers",
    srcs = [
        "status_builder.cc",
    ],
    hdrs = [
        "status_builder.h",
        "status_macros.h",
    ],
    visibility = [":smt_impl"],
    deps = [
        ":source_location",
        "@com_google_absl//absl/base:core_headers",
        "@com_google_absl//absl/base:log_severity",
	"@com_google_absl//absl/log:log",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/strings:cord",
    ],
)

cc_test(
    name = "status_builder_test",
    srcs = ["status_builder_test.cc"],
    deps = [
        ":source_location",
        ":status_helpers",
	"@com_google_googletest//:gtest_main",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "//src/base/testing:status_matchers",
    ],
)

cc_test(
    name = "status_macros_test",
    srcs = ["status_macros_test.cc"],
    deps = [
        ":source_location",
        ":status_helpers",
        "@com_google_googletest//:gtest_main",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)
