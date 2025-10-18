# This package contains tools for semantic analysis and JSON export.

load("@rules_cc//cc:defs.bzl", "cc_binary", "cc_library", "cc_test")

package(
    default_applicable_licenses = ["//:license"],
    default_visibility = ["//verible/verilog:__subpackages__"],
    features = ["layering_check"],
)

cc_library(
    name = "json-exporter",
    srcs = ["json-exporter.cc"],
    hdrs = ["json-exporter.h"],
    deps = [
        "//verible/verilog/analysis:call-graph-enhancer",
        "//verible/verilog/analysis:data-flow-analyzer",
        "//verible/verilog/analysis:enhanced-unused-detector",
        "@nlohmann_json//:json",
    ],
)

cc_test(
    name = "json-exporter_test",
    srcs = ["json-exporter_test.cc"],
    deps = [
        ":json-exporter",
        "//verible/verilog/analysis:call-graph-enhancer",
        "//verible/verilog/analysis:data-flow-analyzer",
        "//verible/verilog/analysis:enhanced-unused-detector",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:verilog-analyzer",
        "//verible/verilog/analysis:verilog-project",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
        "@nlohmann_json//:json",
    ],
)

cc_binary(
    name = "verible-verilog-semantic",
    srcs = ["verible-verilog-semantic.cc"],
    deps = [
        ":json-exporter",
        "//verible/common/util:init-command-line",
        "//verible/verilog/analysis:call-graph-enhancer",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:verilog-analyzer",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/flags:flag",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/strings",
    ],
)

