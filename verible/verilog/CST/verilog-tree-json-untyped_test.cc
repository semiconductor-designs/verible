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
  if (!status.ok()) {
    // Return empty string if parse fails
    return "";
  }
  
  const auto& text_structure = analyzer.Data();
  const auto* root = text_structure.SyntaxTree().get();
  if (!root) return "";
  
  auto json_obj = verilog::ConvertVerilogTreeToJson(*root, text_structure.Contents());
  return json_obj.dump();
}

// Test 1: Function with untyped argument
TEST(UntypedKeywordTest, FunctionWithUntypedArgument) {
  const std::string code = R"(
module test;
  function void print(untyped value);
    $display("Value: %p", value);
  endfunction
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos) 
    << "Should contain 'untyped' keyword in JSON";
  EXPECT_TRUE(!json.empty()) << "Should parse successfully";
}

// Test 2: Task with untyped argument
TEST(UntypedKeywordTest, TaskWithUntypedArgument) {
  const std::string code = R"(
module test;
  task process(untyped data);
    $display("Processing: %p", data);
  endtask
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Should parse successfully";
}

// Test 3: Multiple untyped arguments
TEST(UntypedKeywordTest, MultipleUntypedArguments) {
  const std::string code = R"(
module test;
  function void compare(untyped a, untyped b);
    if (a == b) $display("Equal");
  endfunction
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Should parse successfully";
}

// Test 4: Mixed types (untyped + typed)
TEST(UntypedKeywordTest, MixedTypes) {
  const std::string code = R"(
module test;
  function void mixed(int x, untyped y, string z);
    $display("x=%0d, y=%p, z=%s", x, y, z);
  endfunction
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Should parse successfully";
}

// Test 5: Class member with untyped
TEST(UntypedKeywordTest, ClassMemberUntyped) {
  const std::string code = R"(
class test_class;
  untyped data;
  
  function void set_data(untyped val);
    data = val;
  endfunction
endclass
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Should parse successfully";
}

// Test 6: Untyped with directions (input/output)
TEST(UntypedKeywordTest, UntypedWithDirections) {
  const std::string code = R"(
module test;
  function void convert(input untyped in_val, output untyped out_val);
    out_val = in_val;
  endfunction
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Should parse successfully";
}

// Test 7: Already working - let expression (regression)
TEST(UntypedKeywordTest, LetExpressionRegression) {
  const std::string code = R"(
module test;
  let process(untyped val) = (val > 0) ? val : -val;
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Let expression should still work";
}

// Test 8: Already working - sequence port (regression)
TEST(UntypedKeywordTest, SequencePortRegression) {
  const std::string code = R"(
module test;
  sequence seq(untyped data);
    data == 1;
  endsequence
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Sequence port should still work";
}

// Test 9: Already working - property formal (regression)
TEST(UntypedKeywordTest, PropertyFormalRegression) {
  const std::string code = R"(
module test;
  property p(untyped x);
    x > 0;
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Property formal should still work";
}

// Test 10: Complex real-world usage
TEST(UntypedKeywordTest, ComplexRealWorldUsage) {
  const std::string code = R"(
class generic_queue;
  untyped queue[$];
  
  function void push(untyped item);
    queue.push_back(item);
  endfunction
  
  function int size();
    return queue.size();
  endfunction
endclass
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("untyped") != std::string::npos);
  EXPECT_TRUE(!json.empty()) << "Complex usage should parse successfully";
}

}  // namespace
}  // namespace verilog

