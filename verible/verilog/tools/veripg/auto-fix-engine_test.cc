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

#include "verible/verilog/tools/veripg/auto-fix-engine.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

using ::testing::HasSubstr;

// Test: Generate fix for CDC_001
TEST(AutoFixEngineTest, GenerateFixCDC_001) {
  AutoFixEngine engine;
  
  Violation v;
  v.rule = RuleId::kCDC_001;
  v.signal_name = "data_cdc";
  
  AutoFix fix = engine.GenerateFixForViolation(v);
  
  EXPECT_EQ(fix.rule, RuleId::kCDC_001);
  EXPECT_EQ(fix.safety, FixSafety::kUnsafe);
  EXPECT_THAT(fix.description, HasSubstr("synchronizer"));
  EXPECT_THAT(fix.new_code, HasSubstr("_sync1"));
  EXPECT_THAT(fix.new_code, HasSubstr("_sync2"));
}

// Test: Generate fix for CLK_001
TEST(AutoFixEngineTest, GenerateFixCLK_001) {
  AutoFixEngine engine;
  
  Violation v;
  v.rule = RuleId::kCLK_001;
  
  AutoFix fix = engine.GenerateFixForViolation(v);
  
  EXPECT_EQ(fix.rule, RuleId::kCLK_001);
  EXPECT_EQ(fix.safety, FixSafety::kSafe);
  EXPECT_THAT(fix.description, HasSubstr("clock"));
  EXPECT_EQ(fix.old_code, "always_ff begin");
  EXPECT_EQ(fix.new_code, "always_ff @(posedge clk) begin");
}

// Test: Generate fix for NAM_001
TEST(AutoFixEngineTest, GenerateFixNAM_001) {
  AutoFixEngine engine;
  
  Violation v;
  v.rule = RuleId::kNAM_001;
  v.signal_name = "MyModule";
  
  AutoFix fix = engine.GenerateFixForViolation(v);
  
  EXPECT_EQ(fix.rule, RuleId::kNAM_001);
  EXPECT_EQ(fix.safety, FixSafety::kSafe);
  EXPECT_THAT(fix.description, HasSubstr("snake_case"));
  EXPECT_EQ(fix.old_code, "module MyModule");
  EXPECT_EQ(fix.new_code, "module my_module");
}

// Test: Apply safe fixes
TEST(AutoFixEngineTest, ApplySafeFixes) {
  AutoFixEngine engine;
  
  std::string source = "module MyModule;\nendmodule";
  
  AutoFix fix;
  fix.safety = FixSafety::kSafe;
  fix.old_code = "MyModule";
  fix.new_code = "my_module";
  
  std::string fixed;
  auto status = engine.ApplyFixes(source, {fix}, fixed);
  
  ASSERT_TRUE(status.ok());
  EXPECT_THAT(fixed, HasSubstr("my_module"));
  EXPECT_THAT(fixed, Not(HasSubstr("MyModule")));
}

// Test: Skip unsafe fixes without confirmation
TEST(AutoFixEngineTest, SkipUnsafeFixes) {
  AutoFixEngine engine;
  
  std::string source = "module test;\nendmodule";
  
  AutoFix fix;
  fix.safety = FixSafety::kUnsafe;
  fix.old_code = "test";
  fix.new_code = "test_modified";
  
  std::string fixed;
  auto status = engine.ApplyFixes(source, {fix}, fixed);
  
  ASSERT_TRUE(status.ok());
  // Unsafe fixes should not be applied automatically
  EXPECT_EQ(fixed, source);
}

}  // namespace
}  // namespace tools
}  // namespace verilog
