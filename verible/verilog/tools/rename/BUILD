# Symbol Renaming Tool

licenses(["notice"])

cc_library(
    name = "symbol-renamer",
    srcs = ["symbol-renamer.cc"],
    hdrs = ["symbol-renamer.h"],
    deps = [
        "//verible/common/text:symbol",
        "//verible/common/text:token-info",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-inference",
        "@abseil-cpp//absl/status",
        "@abseil-cpp//absl/status:statusor",
        "@abseil-cpp//absl/strings",
    ],
)

cc_test(
    name = "symbol-renamer_test",
    srcs = ["symbol-renamer_test.cc"],
    deps = [
        ":symbol-renamer",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-inference",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/status",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)

cc_binary(
    name = "verible-verilog-rename",
    srcs = ["rename-main.cc"],
    deps = [
        ":symbol-renamer",
        "//verible/verilog/analysis:symbol-table",
        "//verible/verilog/analysis:type-inference",
        "//verible/verilog/analysis:verilog-project",
        "@abseil-cpp//absl/flags:flag",
        "@abseil-cpp//absl/flags:parse",
        "@abseil-cpp//absl/strings",
    ],
)

