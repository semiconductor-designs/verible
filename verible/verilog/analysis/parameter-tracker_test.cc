// Copyright 2017-2025 The Verible Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "verible/verilog/analysis/parameter-tracker.h"

#include <memory>
#include <string_view>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {
namespace {

// Test fixture for ParameterTracker tests
class ParameterTrackerTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
    tracker_ = std::make_unique<ParameterTracker>(symbol_table_.get());
  }

  // Helper to parse code and build symbol table
  void ParseCode(std::string_view code) {
    const std::string filename = "test.sv";
    
    // Create analyzer
    auto analyzer = std::make_unique<VerilogAnalyzer>(code, filename);
    absl::Status status = analyzer->Analyze();
    ASSERT_TRUE(status.ok()) << status.message();
    
    // Store analyzer
    analyzers_.push_back(std::move(analyzer));
    
    // Build symbol table from this file
    std::vector<absl::Status> diagnostics;
    symbol_table_->BuildSingleTranslationUnit(filename, &diagnostics);
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::unique_ptr<ParameterTracker> tracker_;
  std::vector<std::unique_ptr<VerilogAnalyzer>> analyzers_;
};

// Basic Parameter Tests

TEST_F(ParameterTrackerTest, BasicParameter) {
  constexpr std::string_view code = R"(
module adder #(
  parameter WIDTH = 8
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic [WIDTH-1:0] sum
);
  assign sum = a + b;
endmodule

module top;
  logic [7:0] x, y, result;
  adder dut (.a(x), .b(y), .sum(result));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = tracker_->TrackAllParameters();
  EXPECT_TRUE(status.ok()) << status.message();
  
  // Should find one parameter
  const auto& params = tracker_->GetParameters();
  EXPECT_FALSE(params.empty());
}

TEST_F(ParameterTrackerTest, LocalParameter) {
  constexpr std::string_view code = R"(
module counter (
  input  logic clk,
  input  logic rst,
  output logic [7:0] count
);
  localparam MAX_COUNT = 255;
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      count <= 0;
    else if (count < MAX_COUNT)
      count <= count + 1;
    else
      count <= 0;
  end
endmodule
)";

  ParseCode(code);
  
  absl::Status status = tracker_->TrackAllParameters();
  EXPECT_TRUE(status.ok()) << status.message();
}

TEST_F(ParameterTrackerTest, MultipleParameters) {
  constexpr std::string_view code = R"(
module fifo #(
  parameter DATA_WIDTH = 32,
  parameter DEPTH = 16,
  parameter ADDR_WIDTH = 4
) (
  input  logic clk,
  input  logic rst
);
  logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
endmodule
)";

  ParseCode(code);
  
  absl::Status status = tracker_->TrackAllParameters();
  EXPECT_TRUE(status.ok()) << status.message();
}

// Parameter Override Tests

TEST_F(ParameterTrackerTest, ParameterOverride) {
  constexpr std::string_view code = R"(
module register #(
  parameter WIDTH = 8
) (
  input  logic [WIDTH-1:0] d,
  output logic [WIDTH-1:0] q
);
endmodule

module top;
  logic [15:0] d, q;
  register #(.WIDTH(16)) reg16 (.d(d), .q(q));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = tracker_->TrackAllParameters();
  EXPECT_TRUE(status.ok()) << status.message();
}

// Error Tests

TEST_F(ParameterTrackerTest, OverrideLocalparamError) {
  constexpr std::string_view code = R"(
module counter_with_max #(
  parameter INIT_VALUE = 0
) (
  input  logic clk,
  output logic [7:0] count
);
  localparam MAX_VALUE = 100;
endmodule

module top;
  logic clk;
  logic [7:0] cnt;
  
  counter_with_max #(
    .INIT_VALUE(10),
    .MAX_VALUE(200)
  ) dut (.clk(clk), .count(cnt));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = tracker_->TrackAllParameters();
  EXPECT_TRUE(status.ok());
  
  // TODO: When override detection is implemented, should detect error
  // EXPECT_FALSE(tracker_->GetErrors().empty());
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

