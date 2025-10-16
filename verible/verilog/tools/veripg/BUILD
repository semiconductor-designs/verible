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

cc_test(
    name = "veripg-validator_cdc_integration_test",
    srcs = ["veripg-validator_cdc_integration_test.cc"],
    data = glob(["testdata/cdc/*.sv"]),
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

cc_library(
    name = "rule-config",
    srcs = ["rule-config.cc"],
    hdrs = ["rule-config.h"],
    deps = [
        ":veripg-validator",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/status:statusor",
        "@abseil-cpp//absl/strings",
    ],
)

cc_library(
    name = "auto-fix-engine",
    srcs = ["auto-fix-engine.cc"],
    hdrs = ["auto-fix-engine.h"],
    deps = [
        ":veripg-validator",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/strings",
    ],
)

cc_test(
    name = "rule-config_test",
    srcs = ["rule-config_test.cc"],
    deps = [
        ":rule-config",
        ":veripg-validator",
        "@abseil-cpp//absl/status",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "auto-fix-engine_test",
    srcs = ["auto-fix-engine_test.cc"],
    deps = [
        ":auto-fix-engine",
        ":veripg-validator",
        "@abseil-cpp//absl/status",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "output-formatter",
    srcs = ["output-formatter.cc"],
    hdrs = ["output-formatter.h"],
    deps = [
        ":veripg-validator",
        "@abseil-cpp//absl/strings",
    ],
)

cc_test(
    name = "output-formatter_test",
    srcs = ["output-formatter_test.cc"],
    deps = [
        ":output-formatter",
        ":veripg-validator",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

