# 'verilog_syntax' is a program for checking Verilog/SystemVerilog syntax.

load("@rules_cc//cc:defs.bzl", "cc_binary")
load("//bazel:sh_test_with_runfiles_lib.bzl", "sh_test_with_runfiles_lib")
load("//bazel:variables.bzl", "STATIC_EXECUTABLES_FEATURE")

package(
    default_applicable_licenses = ["//:license"],
    default_visibility = ["//visibility:private"],
    features = ["layering_check"],
)

# v5.7.0: File index tracker for --export_indexed_json
cc_library(
    name = "file-index-tracker",
    srcs = ["file-index-tracker.cc"],
    hdrs = ["file-index-tracker.h"],
    deps = [
        "@nlohmann_json//:singleheader-json",
    ],
)

cc_binary(
    name = "verible-verilog-syntax",
    srcs = ["verilog-syntax.cc"],
    features = STATIC_EXECUTABLES_FEATURE,
    visibility = ["//visibility:public"],  # for verilog_style_lint.bzl
    deps = [
        ":file-index-tracker",  # v5.7.0: For --export_indexed_json
        "//verible/common/strings:mem-block",
        "//verible/common/text:concrete-syntax-tree",
        "//verible/common/text:parser-verifier",
        "//verible/common/text:text-structure",
        "//verible/common/text:token-info",
        "//verible/common/text:token-info-json",
        "//verible/common/util:enum-flags",
        "//verible/common/util:file-util",
        "//verible/common/util:init-command-line",
        "//verible/common/util:iterator-range",
        "//verible/common/util:logging",
        "//verible/verilog/CST:verilog-tree-json",
        "//verible/verilog/CST:verilog-tree-print",
        "//verible/verilog/analysis:include-file-resolver",
        "//verible/verilog/analysis:json-diagnostics",
        "//verible/verilog/analysis:package-context-resolver",
        "//verible/verilog/analysis:verilog-analyzer",
        "//verible/verilog/analysis/checkers:verilog-lint-rules",
        "//verible/verilog/parser:verilog-parser",
        "//verible/verilog/parser:verilog-token",
        "//verible/verilog/parser:verilog-token-classifications",
        "//verible/verilog/parser:verilog-token-enum",
        "@abseil-cpp//absl/flags:flag",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/strings",
        "@nlohmann_json//:singleheader-json",
    ],
)

sh_binary(
    name = "triage-parser",
    srcs = ["triage_parser.sh"],
)

sh_test_with_runfiles_lib(
    name = "verilog-syntax_test",
    size = "small",
    srcs = ["verilog_syntax_test.sh"],
    args = ["$(location :verible-verilog-syntax)"],
    data = [":verible-verilog-syntax"],
    deps = [],
)

cc_test(
    name = "verilog-syntax-unit_test",
    size = "small",
    srcs = ["verilog-syntax_test.cc"],
    deps = [
        "//verible/common/util:file-util",
        "//verible/verilog/analysis:verilog-analyzer",
        "@abseil-cpp//absl/strings",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "verilog-syntax-monitoring_test",
    size = "small",
    srcs = ["verilog-syntax-monitoring_test.cc"],
    deps = [
        "//verible/verilog/analysis:verilog-analyzer",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

# v5.7.0: File index tracker tests
cc_test(
    name = "file-index-tracker_test",
    size = "small",
    srcs = ["file-index-tracker_test.cc"],
    deps = [
        ":file-index-tracker",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
        "@nlohmann_json//:singleheader-json",
    ],
)

# v5.7.0: Version metadata tests
cc_test(
    name = "version-metadata_test",
    size = "small",
    srcs = ["version-metadata_test.cc"],
    deps = [
        "//verible/common/util:init-command-line",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
        "@nlohmann_json//:singleheader-json",
    ],
)
