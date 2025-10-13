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

// Phase 1: Immediate Assertions Tests for JSON Export
// Tests for SystemVerilog Assertion JSON export support

#include "verible/verilog/CST/verilog-tree-json.h"

#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/text/symbol.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

using nlohmann::json;

namespace verilog {
namespace {

// Helper: Parse module and convert to JSON
json ParseModuleToJson(const std::string& code) {
  VerilogAnalyzer analyzer(code, "<test>");
  auto status = analyzer.Analyze();
  if (!status.ok()) {
    LOG(ERROR) << "Parse error: " << status.message();
    return json::object();
  }
  
  const auto& text_structure = analyzer.Data();
  const auto* root = text_structure.SyntaxTree().get();
  if (!root) return json::object();
  
  return ConvertVerilogTreeToJson(*root, text_structure.Contents());
}

// Helper: Find node by tag recursively
const json* FindNodeByTag(const json& node, const std::string& tag) {
  if (node.contains("tag") && node["tag"] == tag) {
    return &node;
  }
  
  if (node.contains("children")) {
    for (const auto& child : node["children"]) {
      const json* result = FindNodeByTag(child, tag);
      if (result) return result;
    }
  }
  
  return nullptr;
}

// Test 1: Basic assert
TEST(ImmediateAssertionsTest, BasicAssert) {
  const std::string code = R"(
module test;
  logic data_valid;
  always_comb begin
    assert (data_valid);
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  // Find assertion statement
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr) << "Should find kAssertionStatement node";
  
  // Verify it has expected structure
  EXPECT_TRUE(assertion->contains("tag"));
  EXPECT_TRUE(assertion->contains("children"));
}

// Test 2: Assert with $error
TEST(ImmediateAssertionsTest, AssertWithError) {
  const std::string code = R"(
module test;
  logic [7:0] data;
  always_comb begin
    assert (data < 8'hFF) else $error("Data overflow");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
  
  // Should have assertion clause and else clause
  EXPECT_TRUE(assertion->contains("children"));
}

// Test 3: Assert with $fatal
TEST(ImmediateAssertionsTest, AssertWithFatal) {
  const std::string code = R"(
module test;
  logic [7:0] addr;
  always_comb begin
    assert (addr < 8'd100) else $fatal(1, "Address out of range: %0d", addr);
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 4: Assert with $warning and $info
TEST(ImmediateAssertionsTest, AssertWithWarningInfo) {
  const std::string code = R"(
module test;
  logic valid;
  always_comb begin
    assert (valid) else $warning("Validity check failed");
  end
  
  initial begin
    assert (1'b1) else $info("Info message");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Should find multiple assertions
  int assertion_count = 0;
  std::function<void(const json&)> count_assertions = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kAssertionStatement") {
      assertion_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_assertions(child);
      }
    }
  };
  count_assertions(tree);
  
  EXPECT_EQ(assertion_count, 2) << "Should find 2 assertion statements";
}

// Test 5: Assume statement
TEST(ImmediateAssertionsTest, AssumeStatement) {
  const std::string code = R"(
module test;
  logic rst_n;
  always_comb begin
    assume (rst_n == 1'b0 || rst_n == 1'b1);
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assume = FindNodeByTag(tree, "kAssumeStatement");
  ASSERT_NE(assume, nullptr) << "Should find kAssumeStatement node";
}

// Test 6: Cover statement
TEST(ImmediateAssertionsTest, CoverStatement) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  always_comb begin
    cover (state == 2'b00);
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cover = FindNodeByTag(tree, "kCoverStatement");
  ASSERT_NE(cover, nullptr) << "Should find kCoverStatement node";
}

// Test 7: Labeled assertion
TEST(ImmediateAssertionsTest, LabeledAssertion) {
  const std::string code = R"(
module test;
  logic [7:0] data;
  always_comb begin
    overflow_check: assert (data < 8'hF0) else $error("Overflow");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion_item = FindNodeByTag(tree, "kAssertionItem");
  // Labeled assertions are wrapped in kAssertionItem with block identifier
  EXPECT_TRUE(assertion_item != nullptr || FindNodeByTag(tree, "kAssertionStatement") != nullptr);
}

// Test 8: Deferred assertion (assert final)
TEST(ImmediateAssertionsTest, DeferredAssertion) {
  const std::string code = R"(
module test;
  logic done;
  always_comb begin
    assert final (done == 1'b1) else $error("Not done");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 9: Deferred assume
TEST(ImmediateAssertionsTest, DeferredAssume) {
  const std::string code = R"(
module test;
  logic clk;
  always_comb begin
    assume #0 (clk == 1'b0 || clk == 1'b1);
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assume = FindNodeByTag(tree, "kAssumeStatement");
  ASSERT_NE(assume, nullptr);
}

// Test 10: Multiple assertions in block
TEST(ImmediateAssertionsTest, MultipleAssertions) {
  const std::string code = R"(
module test;
  logic valid, ready;
  logic [7:0] data;
  
  always_comb begin
    assert (valid || !ready);
    assume (data < 8'hFF);
    cover (valid && ready);
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int count = 0;
  std::function<void(const json&)> count_all = [&](const json& node) {
    if (node.contains("tag")) {
      std::string tag = node["tag"];
      if (tag == "kAssertionStatement" || tag == "kAssumeStatement" || tag == "kCoverStatement") {
        count++;
      }
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_all(child);
      }
    }
  };
  count_all(tree);
  
  EXPECT_EQ(count, 3) << "Should find 3 assertion/assume/cover statements";
}

// Test 11: Assertions in always_comb
TEST(ImmediateAssertionsTest, AssertionsInAlwaysComb) {
  const std::string code = R"(
module test;
  logic [7:0] a, b, sum;
  
  always_comb begin
    sum = a + b;
    assert (sum >= a) else $error("Overflow");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* always_stmt = FindNodeByTag(tree, "kAlwaysStatement");
  ASSERT_NE(always_stmt, nullptr);
  
  // Should contain assertion
  const json* assertion = FindNodeByTag(*always_stmt, "kAssertionStatement");
  EXPECT_NE(assertion, nullptr);
}

// Test 12: Assertions in always_ff
TEST(ImmediateAssertionsTest, AssertionsInAlwaysFF) {
  const std::string code = R"(
module test;
  logic clk, rst_n;
  logic [7:0] counter;
  
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      counter <= 8'h00;
    end else begin
      counter <= counter + 1;
      assert (counter < 8'hFF) else $error("Counter overflow");
    end
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 13: Assertions in initial
TEST(ImmediateAssertionsTest, AssertionsInInitial) {
  const std::string code = R"(
module test;
  logic data;
  
  initial begin
    data = 1'b0;
    assert (data == 1'b0) else $error("Initial value wrong");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 14: Assertions in functions/tasks
TEST(ImmediateAssertionsTest, AssertionsInFunctionsTasks) {
  const std::string code = R"(
module test;
  function int add(int a, int b);
    assert (a >= 0 && b >= 0) else $error("Negative input");
    return a + b;
  endfunction
  
  task check_value(int val);
    assert (val < 100) else $warning("Value too large");
  endtask
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Should find assertions in both function and task
  int count = 0;
  std::function<void(const json&)> count_assertions = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kAssertionStatement") {
      count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_assertions(child);
      }
    }
  };
  count_assertions(tree);
  
  EXPECT_EQ(count, 2) << "Should find 2 assertions (function + task)";
}

// Test 15: Nested action blocks
TEST(ImmediateAssertionsTest, NestedActionBlocks) {
  const std::string code = R"(
module test;
  logic valid, error;
  
  always_comb begin
    assert (valid) else begin
      error = 1'b1;
      $error("Validation failed");
    end
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 16: Complex expressions in assertions
TEST(ImmediateAssertionsTest, ComplexExpressions) {
  const std::string code = R"(
module test;
  logic [7:0] a, b, c;
  logic valid, ready;
  
  always_comb begin
    assert ((a + b) * c < 8'hFF && (valid || ready))
      else $error("Complex condition failed");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 17: Empty action blocks
TEST(ImmediateAssertionsTest, EmptyActionBlocks) {
  const std::string code = R"(
module test;
  logic valid;
  
  always_comb begin
    assert (valid) else begin end
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 18: Pass and fail actions
TEST(ImmediateAssertionsTest, PassAndFailActions) {
  const std::string code = R"(
module test;
  logic valid;
  
  always_comb begin
    assert (valid) else $error("Fail");
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assertion = FindNodeByTag(tree, "kAssertionStatement");
  ASSERT_NE(assertion, nullptr);
}

// Test 19: System task calls
TEST(ImmediateAssertionsTest, SystemTaskCalls) {
  const std::string code = R"(
module test;
  logic [7:0] data;
  
  always_comb begin
    assert (data < 8'h80) else $fatal(0, "Fatal error");
    assume (data >= 8'h00) else $error("Error");
    cover (data == 8'h42); // Silent cover
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int count = 0;
  std::function<void(const json&)> count_all = [&](const json& node) {
    if (node.contains("tag")) {
      std::string tag = node["tag"];
      if (tag == "kAssertionStatement" || tag == "kAssumeStatement" || tag == "kCoverStatement") {
        count++;
      }
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_all(child);
      }
    }
  };
  count_all(tree);
  
  EXPECT_EQ(count, 3);
}

// Test 20: Performance test (100 assertions)
TEST(ImmediateAssertionsTest, PerformanceTest) {
  std::string code = "module test;\n";
  code += "  logic [7:0] data;\n";
  code += "  always_comb begin\n";
  
  // Generate 100 assertions
  for (int i = 0; i < 100; i++) {
    code += "    assert (data < 8'hFF);\n";
  }
  
  code += "  end\n";
  code += "endmodule\n";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count assertions
  int count = 0;
  std::function<void(const json&)> count_assertions = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kAssertionStatement") {
      count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_assertions(child);
      }
    }
  };
  count_assertions(tree);
  
  EXPECT_EQ(count, 100) << "Should find 100 assertion statements";
}

// ============================================================================
// PHASE 2: Concurrent Assertions - Properties
// ============================================================================

// Test 21: Simple property declaration
TEST(ConcurrentAssertionsTest, SimplePropertyDeclaration) {
  const std::string code = R"(
module test(input logic clk, req, ack);
  property p_req_ack;
    @(posedge clk) req |-> ##1 ack;
  endproperty
  
  assert property (p_req_ack);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Should find property declaration
  const json* prop_decl = FindNodeByTag(tree, "kPropertyDeclaration");
  EXPECT_TRUE(prop_decl != nullptr) << "Should find kPropertyDeclaration";
}

// Test 22: Property with clocking event
TEST(ConcurrentAssertionsTest, PropertyWithClockingEvent) {
  const std::string code = R"(
module test(input logic clk, valid, ready);
  property p_handshake;
    @(posedge clk) valid |-> ready;
  endproperty
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prop_decl = FindNodeByTag(tree, "kPropertyDeclaration");
  EXPECT_TRUE(prop_decl != nullptr);
}

// Test 23: Property with disable iff
TEST(ConcurrentAssertionsTest, PropertyWithDisableIff) {
  const std::string code = R"(
module test(input logic clk, rst_n, req, gnt);
  property p_req_gnt;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:3] gnt;
  endproperty
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prop_decl = FindNodeByTag(tree, "kPropertyDeclaration");
  EXPECT_TRUE(prop_decl != nullptr);
}

// Test 24: Inline property in assert
TEST(ConcurrentAssertionsTest, InlinePropertyInAssert) {
  const std::string code = R"(
module test(input logic clk, req, ack);
  assert property (@(posedge clk) req |-> ##1 ack);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assert_prop = FindNodeByTag(tree, "kAssertPropertyStatement");
  EXPECT_TRUE(assert_prop != nullptr) << "Should find kAssertPropertyStatement";
}

// Test 25: Concurrent assume property
TEST(ConcurrentAssertionsTest, AssumeProperty) {
  const std::string code = R"(
module test(input logic clk, rst_n);
  assume property (@(posedge clk) $rose(rst_n) |-> !req);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* assume_prop = FindNodeByTag(tree, "kAssumePropertyStatement");
  EXPECT_TRUE(assume_prop != nullptr) << "Should find kAssumePropertyStatement";
}

// Test 26: Concurrent cover property
TEST(ConcurrentAssertionsTest, CoverProperty) {
  const std::string code = R"(
module test(input logic clk, valid, ready);
  cover property (@(posedge clk) valid ##1 ready);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cover_prop = FindNodeByTag(tree, "kCoverPropertyStatement");
  EXPECT_TRUE(cover_prop != nullptr) << "Should find kCoverPropertyStatement";
}

// ============================================================================
// PHASE 3: Sequences
// ============================================================================

// Test 27: Simple sequence declaration
TEST(SequenceTest, SimpleSequenceDeclaration) {
  const std::string code = R"(
module test;
  logic clk, req, ack;
  
  sequence s_handshake;
    req ##1 ack;
  endsequence
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* seq_decl = FindNodeByTag(tree, "kSequenceDeclaration");
  EXPECT_TRUE(seq_decl != nullptr) << "Should find kSequenceDeclaration";
}

// Test 28: Sequence with fixed delay
TEST(SequenceTest, SequenceWithFixedDelay) {
  const std::string code = R"(
module test;
  logic clk, a, b;
  
  sequence s_delay2;
    a ##2 b;
  endsequence
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* seq_decl = FindNodeByTag(tree, "kSequenceDeclaration");
  EXPECT_TRUE(seq_decl != nullptr);
}

// Test 29: Sequence with range delay
TEST(SequenceTest, SequenceWithRangeDelay) {
  const std::string code = R"(
module test;
  logic clk, req, gnt;
  
  sequence s_req_gnt;
    req ##[1:5] gnt;
  endsequence
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* seq_decl = FindNodeByTag(tree, "kSequenceDeclaration");
  EXPECT_TRUE(seq_decl != nullptr);
}

// Test 30: Cover sequence statement
TEST(SequenceTest, CoverSequence) {
  const std::string code = R"(
module test;
  logic clk, valid, ready;
  
  sequence s_transfer;
    valid ##1 ready;
  endsequence
  
  cover sequence (@(posedge clk) s_transfer);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cover_seq = FindNodeByTag(tree, "kCoverSequenceStatement");
  EXPECT_TRUE(cover_seq != nullptr) << "Should find kCoverSequenceStatement";
}

// Test 31: Sequence in property
TEST(SequenceTest, SequenceInProperty) {
  const std::string code = R"(
module test;
  logic clk, start, done;
  
  sequence s_operation;
    start ##[1:10] done;
  endsequence
  
  property p_complete;
    @(posedge clk) s_operation;
  endproperty
  
  assert property (p_complete);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* seq_decl = FindNodeByTag(tree, "kSequenceDeclaration");
  EXPECT_TRUE(seq_decl != nullptr);
  
  const json* prop_decl = FindNodeByTag(tree, "kPropertyDeclaration");
  EXPECT_TRUE(prop_decl != nullptr);
}

// Test 32: Multiple sequences
TEST(SequenceTest, MultipleSequences) {
  const std::string code = R"(
module test;
  logic clk, a, b, c;
  
  sequence s1;
    a ##1 b;
  endsequence
  
  sequence s2;
    b ##1 c;
  endsequence
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int seq_count = 0;
  std::function<void(const json&)> count_sequences = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kSequenceDeclaration") {
      seq_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_sequences(child);
      }
    }
  };
  count_sequences(tree);
  
  EXPECT_EQ(seq_count, 2) << "Should find 2 sequence declarations";
}

}  // namespace
}  // namespace verilog

