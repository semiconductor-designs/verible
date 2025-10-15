# Refactoring Tools

licenses(["notice"])

cc_library(
    name = "refactoring-engine",
    srcs = ["refactoring-engine.cc"],
    hdrs = ["refactoring-engine.h"],
    deps = [
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-inference",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/strings",
    ],
)

cc_test(
    name = "refactoring-engine_test",
    srcs = ["refactoring-engine_test.cc"],
    deps = [
        ":refactoring-engine",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-inference",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/status",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_binary(
    name = "verible-verilog-refactor",
    srcs = ["refactor-main.cc"],
    deps = [
        ":refactoring-engine",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-inference",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/flags:flag",
        "@abseil-cpp//absl/flags:parse",
        "@abseil-cpp//absl/strings",
    ],
)

