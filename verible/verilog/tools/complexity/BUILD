# Code Complexity Analyzer

licenses(["notice"])

cc_library(
    name = "complexity-analyzer",
    srcs = ["complexity-analyzer.cc"],
    hdrs = ["complexity-analyzer.h"],
    deps = [
        "//verible/verilog/analysis:call-graph",
        "//verible/verilog/analysis:type-checker",
        "@abseil-cpp//absl/strings",
    ],
)

cc_test(
    name = "complexity-analyzer_test",
    srcs = ["complexity-analyzer_test.cc"],
    deps = [
        ":complexity-analyzer",
        "//verible/verilog/analysis:call-graph",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-checker",
        "//verible/verilog/analysis:type-inference",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/strings",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_binary(
    name = "verible-verilog-complexity",
    srcs = ["complexity-main.cc"],
    deps = [
        ":complexity-analyzer",
        "//verible/verilog/analysis:call-graph",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/flags:flag",
        "@abseil-cpp//absl/flags:parse",
        "@abseil-cpp//absl/strings",
    ],
)

