# Dead Code Elimination Tool

licenses(["notice"])

cc_library(
    name = "dead-code-eliminator",
    srcs = ["dead-code-eliminator.cc"],
    hdrs = ["dead-code-eliminator.h"],
    deps = [
        "//verible/verilog/analysis:call-graph",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/strings",
    ],
)

cc_test(
    name = "dead-code-eliminator_test",
    srcs = ["dead-code-eliminator_test.cc"],
    deps = [
        ":dead-code-eliminator",
        "//verible/verilog/analysis:call-graph",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/status",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "dead-code-eliminator_integration_test",
    srcs = ["dead-code-eliminator_integration_test.cc"],
    deps = [
        ":dead-code-eliminator",
        "//verible/verilog/analysis:call-graph",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:verilog-project",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_binary(
    name = "verible-verilog-deadcode",
    srcs = ["deadcode-main.cc"],
    deps = [
        ":dead-code-eliminator",
        "//verible/verilog/analysis:call-graph",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/flags:flag",
        "@abseil-cpp//absl/flags:parse",
        "@abseil-cpp//absl/strings",
    ],
)

