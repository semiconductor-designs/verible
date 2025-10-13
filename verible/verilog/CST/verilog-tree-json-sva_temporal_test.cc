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

#include "verible/verilog/CST/verilog-tree-json.h"

#include <string>

#include "gtest/gtest.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

#undef ASSERT_OK
#define ASSERT_OK(value) ASSERT_TRUE((value).ok())

namespace verilog {
namespace {

// Helper function to parse and export JSON
std::string GetJSONFromCode(const std::string &code) {
  verilog::VerilogAnalyzer analyzer(code, "<test>");
  auto status = analyzer.Analyze();
  CHECK(status.ok()) << "Parse error: " << status.message();
  
  const auto& text_structure = analyzer.Data();
  const auto* root = text_structure.SyntaxTree().get();
  CHECK(root != nullptr) << "Parse error in test case";
  
  auto json_obj = verilog::ConvertVerilogTreeToJson(*root, text_structure.Contents());
  return json_obj.dump();
}

// Test 1: Basic throughout operator
TEST(SVATemporalTest, BasicThroughout) {
  const std::string code = R"(
module test;
  property p_throughout;
    @(posedge clk)
      req throughout valid;
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("throughout") != std::string::npos) 
    << "Should contain 'throughout' operator in JSON";
}

// Test 2: Throughout with sequences
TEST(SVATemporalTest, ThroughoutWithSequences) {
  const std::string code = R"(
module test;
  property p_throughout_seq;
    @(posedge clk)
      (req ##1 ack) throughout (valid ##[1:5] ready);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
}

// Test 3: Throughout with delay ranges
TEST(SVATemporalTest, ThroughoutWithRanges) {
  const std::string code = R"(
module test;
  property p_throughout_range;
    @(posedge clk)
      enable throughout (##[1:10] done);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
}

// Test 4: Nested throughout
TEST(SVATemporalTest, NestedThroughout) {
  const std::string code = R"(
module test;
  property p_nested_throughout;
    @(posedge clk)
      (a throughout b) throughout c;
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
}

// Test 5: Basic within operator
TEST(SVATemporalTest, BasicWithin) {
  const std::string code = R"(
module test;
  property p_within;
    @(posedge clk)
      req within ack;
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("within") != std::string::npos) 
    << "Should contain 'within' operator in JSON";
}

// Test 6: Within with delay ranges
TEST(SVATemporalTest, WithinWithRanges) {
  const std::string code = R"(
module test;
  property p_within_range;
    @(posedge clk)
      (req ##[1:5] ack) within (start ##[1:20] done);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("within") != std::string::npos);
}

// Test 7: Within nested in property
TEST(SVATemporalTest, WithinInProperty) {
  const std::string code = R"(
module test;
  property p_within_nested;
    @(posedge clk) disable iff (reset)
      req |-> (ack within ##[1:10] timeout);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("within") != std::string::npos);
}

// Test 8: Basic first_match
TEST(SVATemporalTest, BasicFirstMatch) {
  const std::string code = R"(
module test;
  property p_first_match;
    @(posedge clk)
      first_match(req ##[1:5] ack);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("first_match") != std::string::npos)
    << "Should contain 'first_match' operator in JSON";
}

// Test 9: First_match with sequences
TEST(SVATemporalTest, FirstMatchWithSequences) {
  const std::string code = R"(
module test;
  property p_first_match_seq;
    @(posedge clk)
      first_match((req ##1 gnt) ##[1:$] done);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("first_match") != std::string::npos);
}

// Test 10: First_match with throughout
TEST(SVATemporalTest, FirstMatchWithThroughout) {
  const std::string code = R"(
module test;
  property p_first_match_throughout;
    @(posedge clk)
      first_match(enable throughout (req ##[1:5] ack));
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("first_match") != std::string::npos);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
}

// Test 11: Combined temporal operators
TEST(SVATemporalTest, CombinedOperators) {
  const std::string code = R"(
module test;
  property p_combined;
    @(posedge clk) disable iff (reset)
      first_match((req throughout valid) within (start ##[1:20] done));
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("first_match") != std::string::npos);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
  EXPECT_TRUE(json.find("within") != std::string::npos);
}

// Test 12: Edge cases - empty sequences
TEST(SVATemporalTest, EdgeCases) {
  const std::string code = R"(
module test;
  property p_edge;
    @(posedge clk)
      1 throughout (##[0:$] done);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
}

// Test 13: Complex temporal property
TEST(SVATemporalTest, ComplexTemporalProperty) {
  const std::string code = R"(
module test;
  property p_complex;
    @(posedge clk) disable iff (reset)
      (req ##[1:3] gnt) |-> 
        first_match((busy throughout active) within (start ##[5:50] complete));
  endproperty
  
  assert property (p_complex);
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("first_match") != std::string::npos);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
  EXPECT_TRUE(json.find("within") != std::string::npos);
}

// Test 14: Real-world UVM pattern
TEST(SVATemporalTest, UVMPattern) {
  const std::string code = R"(
module test;
  // UVM-style bus protocol property
  property p_bus_protocol;
    @(posedge clk) disable iff (!rst_n)
      (valid && ready) |->
        first_match(
          (grant throughout (beat ##[1:16] last)) 
          within 
          (transfer_start ##[1:100] transfer_end)
        );
  endproperty
  
  ap_bus_protocol: assert property (p_bus_protocol)
    else $error("Bus protocol violation");
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("first_match") != std::string::npos);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
  EXPECT_TRUE(json.find("within") != std::string::npos);
}

// Test 15: OpenTitan assertion pattern
TEST(SVATemporalTest, OpenTitanPattern) {
  const std::string code = R"(
module test;
  // OpenTitan-style security property
  property p_security_check;
    @(posedge clk_i) disable iff (!rst_ni)
      (alert_trigger) |=>
        first_match(
          (escalate_en throughout (clear_req ##[1:8] clear_ack))
          within
          (alert_start ##[1:1000] alert_timeout)
        );
  endproperty
  
  `ASSERT(SecurityCheck, p_security_check)
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("first_match") != std::string::npos);
  EXPECT_TRUE(json.find("throughout") != std::string::npos);
  EXPECT_TRUE(json.find("within") != std::string::npos);
}

}  // namespace
}  // namespace verilog

