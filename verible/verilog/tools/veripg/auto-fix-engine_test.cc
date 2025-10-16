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

#include "verible/verilog/tools/veripg/auto-fix-engine.h"

#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

// Test 1: AutoFixEngine construction
TEST(AutoFixEngineTest, Construction) {
  AutoFixEngine engine;
  // Default construction should succeed
}

// Test 2: GenerateFix for CDC_001 (safe=false)
TEST(AutoFixEngineTest, GenerateFixCDC_001) {
  AutoFixEngine engine;
  Violation v;
  v.rule = RuleId::kCDC_001;
  v.signal_name = "data_signal";
  v.message = "CDC without synchronizer";
  
  FixSuggestion fix = engine.GenerateFix(v);
  
  EXPECT_EQ(fix.rule_id, RuleId::kCDC_001);
  EXPECT_EQ(fix.safety, FixSafety::kUnsafe);
  EXPECT_FALSE(fix.code_snippet.empty());
  EXPECT_NE(fix.code_snippet.find("sync"), std::string::npos);
}

// Test 3: GenerateFix for NAM_001 (safe=true)
TEST(AutoFixEngineTest, GenerateFixNAM_001) {
  AutoFixEngine engine;
  Violation v;
  v.rule = RuleId::kNAM_001;
  v.signal_name = "MyModule";
  v.message = "Module name should be lowercase";
  
  FixSuggestion fix = engine.GenerateFix(v);
  
  EXPECT_EQ(fix.rule_id, RuleId::kNAM_001);
  EXPECT_EQ(fix.safety, FixSafety::kSafe);
  EXPECT_FALSE(fix.code_snippet.empty());
  EXPECT_NE(fix.code_snippet.find("my_module"), std::string::npos);
}

// Test 4: GenerateFix for STR_006 (safe=true)
TEST(AutoFixEngineTest, GenerateFixSTR_006) {
  AutoFixEngine engine;
  Violation v;
  v.rule = RuleId::kSTR_006;
  v.signal_name = "u1";
  v.message = "Instantiation without named ports";
  
  FixSuggestion fix = engine.GenerateFix(v);
  
  EXPECT_EQ(fix.rule_id, RuleId::kSTR_006);
  EXPECT_EQ(fix.safety, FixSafety::kSafe);
  EXPECT_FALSE(fix.code_snippet.empty());
}

// Test 5: GenerateFixes for multiple violations
TEST(AutoFixEngineTest, GenerateFixes_Multiple) {
  AutoFixEngine engine;
  
  std::vector<Violation> violations;
  Violation v1;
  v1.rule = RuleId::kNAM_001;
  v1.signal_name = "TestModule";
  violations.push_back(v1);
  
  Violation v2;
  v2.rule = RuleId::kCDC_001;
  v2.signal_name = "data";
  violations.push_back(v2);
  
  std::vector<FixSuggestion> fixes = engine.GenerateFixes(violations);
  
  EXPECT_EQ(fixes.size(), 2);
  EXPECT_EQ(fixes[0].rule_id, RuleId::kNAM_001);
  EXPECT_EQ(fixes[1].rule_id, RuleId::kCDC_001);
}

// Test 6: ApplySafeFixes framework
TEST(AutoFixEngineTest, ApplySafeFixes_Framework) {
  AutoFixEngine engine;
  std::vector<FixSuggestion> fixes;
  int fixes_applied = 0;
  
  auto status = engine.ApplySafeFixes("test.sv", fixes, &fixes_applied);
  
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(fixes_applied, 0);  // Framework only
}

// Test 7: GenerateFixCLK_001
TEST(AutoFixEngineTest, GenerateFixCLK_001) {
  AutoFixEngine engine;
  Violation v;
  v.rule = RuleId::kCLK_001;
  v.signal_name = "clk";
  
  FixSuggestion fix = engine.GenerateFix(v);
  
  EXPECT_EQ(fix.safety, FixSafety::kUnsafe);
  EXPECT_NE(fix.code_snippet.find("always_ff"), std::string::npos);
}

// Test 8: GenerateFixRST_001
TEST(AutoFixEngineTest, GenerateFixRST_001) {
  AutoFixEngine engine;
  Violation v;
  v.rule = RuleId::kRST_001;
  v.signal_name = "rst_n";
  
  FixSuggestion fix = engine.GenerateFix(v);
  
  EXPECT_EQ(fix.safety, FixSafety::kUnsafe);
  EXPECT_NE(fix.code_snippet.find("rst_n"), std::string::npos);
}

// Test 9: GenerateFixNAM_003 (parameter naming)
TEST(AutoFixEngineTest, GenerateFixNAM_003) {
  AutoFixEngine engine;
  Violation v;
  v.rule = RuleId::kNAM_003;
  v.signal_name = "data_width";
  
  FixSuggestion fix = engine.GenerateFix(v);
  
  EXPECT_EQ(fix.safety, FixSafety::kSafe);
  EXPECT_NE(fix.code_snippet.find("DATA_WIDTH"), std::string::npos);
}

// Test 10: GenerateFixSTR_008 (default clause)
TEST(AutoFixEngineTest, GenerateFixSTR_008) {
  AutoFixEngine engine;
  Violation v;
  v.rule = RuleId::kSTR_008;
  
  FixSuggestion fix = engine.GenerateFix(v);
  
  EXPECT_EQ(fix.safety, FixSafety::kUnsafe);
  EXPECT_NE(fix.code_snippet.find("default"), std::string::npos);
}

// Test 11: All 12 fix generators work
TEST(AutoFixEngineTest, All12FixGenerators) {
  AutoFixEngine engine;
  
  std::vector<RuleId> rules = {
    RuleId::kCDC_001, RuleId::kCLK_001, RuleId::kRST_001,
    RuleId::kNAM_001, RuleId::kNAM_003, RuleId::kNAM_004, RuleId::kNAM_005,
    RuleId::kWID_001,
    RuleId::kSTR_005, RuleId::kSTR_006, RuleId::kSTR_007, RuleId::kSTR_008
  };
  
  for (const auto& rule_id : rules) {
    Violation v;
    v.rule = rule_id;
    v.signal_name = "test";
    
    FixSuggestion fix = engine.GenerateFix(v);
    EXPECT_EQ(fix.rule_id, rule_id);
    EXPECT_FALSE(fix.code_snippet.empty());
  }
}

}  // namespace
}  // namespace tools
}  // namespace verilog

