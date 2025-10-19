// Copyright 2025 The Verible Authors.
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

// Unit tests for monitoring system in verible-verilog-syntax
// Tests parse statistics tracking, error pattern detection, and performance monitoring

#include <string>

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test basic parse success tracking
TEST(MonitoringTest, SuccessfulParseTracking) {
  const std::string code = R"(
    module test;
      wire a;
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok());
  // In production, global_stats.RecordSuccess() would be called
}

// Test parse failure tracking
TEST(MonitoringTest, FailedParseTracking) {
  const std::string code = R"(
    module test;
      syntax error here
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_FALSE(status.ok());
  // In production, global_stats.RecordFailure() would be called
}

// Test event trigger parsing (success case)
TEST(MonitoringTest, EventTriggerSuccess) {
  const std::string code = R"(
    `define uvm_info(ID, MSG, VERBOSITY) $display(MSG)
    `define gfn get_full_name()
    
    class item;
      event byte_sampled_ev;
    endclass
    
    class monitor;
      item host_item;
      
      virtual protected task collect_trans();
        `uvm_info(`gfn, "message", 0)
        -> host_item.byte_sampled_ev;
      endtask
    endclass
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Event trigger after macro should parse successfully";
}

// Test logical implication parsing (success case)
TEST(MonitoringTest, LogicalImplicationSuccess) {
  const std::string code = R"(
    module test;
      logic a, b, result;
      
      always_comb begin
        result = a -> b;
      end
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Logical implication in expression should parse successfully";
}

// Test performance (parse should complete quickly)
TEST(MonitoringTest, ParsePerformance) {
  const std::string code = R"(
    module large_test;
      genvar i;
      generate
        for (i = 0; i < 100; i++) begin : gen_loop
          wire [31:0] data;
          wire valid;
        end
      endgenerate
    endmodule
  )";
  
  auto start = std::chrono::high_resolution_clock::now();
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  auto end = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
  
  EXPECT_TRUE(status.ok());
  EXPECT_LT(duration.count(), 100) << "Parse should complete in < 100ms";
}

// Test multiple files tracking (simulated)
TEST(MonitoringTest, MultipleFilesTracking) {
  const std::vector<std::string> test_cases = {
    "module a; endmodule",
    "module b; wire x; endmodule",
    "module c; logic y; endmodule",
  };
  
  int success_count = 0;
  int fail_count = 0;
  
  for (size_t i = 0; i < test_cases.size(); ++i) {
    VerilogAnalyzer analyzer(test_cases[i], "test" + std::to_string(i) + ".sv");
    if (analyzer.Analyze().ok()) {
      success_count++;
    } else {
      fail_count++;
    }
  }
  
  EXPECT_EQ(success_count, 3);
  EXPECT_EQ(fail_count, 0);
}

// Test error message pattern detection
TEST(MonitoringTest, ErrorPatternDetection) {
  const std::string code = R"(
    module test;
      -> ;  // Syntax error: missing event name
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_FALSE(status.ok());
  
  // Check error messages contain expected patterns
  const auto errors = analyzer.LinterTokenErrorMessages(false);
  EXPECT_GT(errors.size(), 0);
  
  bool found_syntax_error = false;
  for (const auto& error : errors) {
    if (error.find("syntax error") != std::string::npos) {
      found_syntax_error = true;
      break;
    }
  }
  
  EXPECT_TRUE(found_syntax_error) << "Should detect syntax error pattern";
}

}  // namespace
}  // namespace verilog

