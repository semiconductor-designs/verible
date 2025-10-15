# VeriPG Integration

licenses(["notice"])

cc_library(
    name = "veripg-validator",
    srcs = ["veripg-validator.cc"],
    hdrs = ["veripg-validator.h"],
    deps = [
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-checker",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/strings",
    ],
)

cc_test(
    name = "veripg-validator_test",
    srcs = ["veripg-validator_test.cc"],
    deps = [
        ":veripg-validator",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-checker",
        "//verible/verilog/analysis:type-inference",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/status",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

