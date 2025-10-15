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

#include "verible/verilog/tools/complexity/complexity-analyzer.h"

#include "gtest/gtest.h"
#include "verible/verilog/analysis/call-graph.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace tools {
namespace {

class ComplexityAnalyzerTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
    call_graph_ = std::make_unique<analysis::CallGraph>(symbol_table_.get());
    type_inference_ = std::make_unique<analysis::TypeInference>(symbol_table_.get());
    type_checker_ = std::make_unique<analysis::TypeChecker>(symbol_table_.get(), type_inference_.get());
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::unique_ptr<analysis::CallGraph> call_graph_;
  std::unique_ptr<analysis::TypeInference> type_inference_;
  std::unique_ptr<analysis::TypeChecker> type_checker_;
};

// Test 1: Constructor
TEST_F(ComplexityAnalyzerTest, Constructor) {
  ComplexityAnalyzer analyzer(call_graph_.get());
  EXPECT_TRUE(true);
}

// Test 2: Constructor with type checker
TEST_F(ComplexityAnalyzerTest, ConstructorWithTypeChecker) {
  ComplexityAnalyzer analyzer(call_graph_.get(), type_checker_.get());
  EXPECT_TRUE(true);
}

// Test 3: Analyze empty call graph
TEST_F(ComplexityAnalyzerTest, AnalyzeEmpty) {
  ComplexityAnalyzer analyzer(call_graph_.get());
  
  auto report = analyzer.Analyze();
  EXPECT_EQ(report.total_functions, 0);
  EXPECT_EQ(report.average_complexity, 0);
}

// Test 4: Analyze simple call graph
TEST_F(ComplexityAnalyzerTest, AnalyzeSimple) {
  call_graph_->AddNode("func1");
  call_graph_->AddNode("func2");
  call_graph_->AddEdge("func1", "func2");
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  auto report = analyzer.Analyze();
  
  EXPECT_GT(report.total_functions, 0);
}

// Test 5: Text report generation
TEST_F(ComplexityAnalyzerTest, GenerateTextReport) {
  call_graph_->AddNode("test_func");
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  analyzer.Analyze();
  
  auto report = analyzer.GenerateReport(ReportFormat::kText);
  EXPECT_FALSE(report.empty());
  EXPECT_NE(report.find("Complexity Analysis Report"), std::string::npos);
}

// Test 6: JSON report generation
TEST_F(ComplexityAnalyzerTest, GenerateJsonReport) {
  call_graph_->AddNode("test_func");
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  analyzer.Analyze();
  
  auto report = analyzer.GenerateReport(ReportFormat::kJson);
  EXPECT_FALSE(report.empty());
  EXPECT_NE(report.find("total_functions"), std::string::npos);
}

// Test 7: HTML report generation
TEST_F(ComplexityAnalyzerTest, GenerateHtmlReport) {
  call_graph_->AddNode("test_func");
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  analyzer.Analyze();
  
  auto report = analyzer.GenerateReport(ReportFormat::kHtml);
  EXPECT_FALSE(report.empty());
  EXPECT_NE(report.find("<html>"), std::string::npos);
  EXPECT_NE(report.find("</html>"), std::string::npos);
}

// Test 8: Get function metrics (non-existent)
TEST_F(ComplexityAnalyzerTest, GetNonExistentFunctionMetrics) {
  ComplexityAnalyzer analyzer(call_graph_.get());
  analyzer.Analyze();
  
  auto metrics = analyzer.GetFunctionMetrics("nonexistent");
  EXPECT_EQ(metrics.name, "nonexistent");
  EXPECT_EQ(metrics.cyclomatic_complexity, 0);
}

// Test 9: Complex call graph
TEST_F(ComplexityAnalyzerTest, ComplexCallGraph) {
  // Create a more complex graph
  for (int i = 0; i < 10; ++i) {
    call_graph_->AddNode(absl::StrCat("func", i));
  }
  for (int i = 0; i < 9; ++i) {
    call_graph_->AddEdge(absl::StrCat("func", i), 
                          absl::StrCat("func", i + 1));
  }
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  auto report = analyzer.Analyze();
  
  EXPECT_EQ(report.total_functions, 10);
}

// Test 10: Null call graph
TEST_F(ComplexityAnalyzerTest, NullCallGraph) {
  ComplexityAnalyzer analyzer(nullptr);
  
  auto report = analyzer.Analyze();
  EXPECT_EQ(report.total_functions, 0);
}

// Test 11: Report before analyze
TEST_F(ComplexityAnalyzerTest, ReportBeforeAnalyze) {
  ComplexityAnalyzer analyzer(call_graph_.get());
  
  // Generate report without calling Analyze()
  auto report = analyzer.GenerateReport(ReportFormat::kText);
  EXPECT_FALSE(report.empty());
}

// Test 12: Multiple analyses
TEST_F(ComplexityAnalyzerTest, MultipleAnalyses) {
  call_graph_->AddNode("func1");
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  
  auto report1 = analyzer.Analyze();
  auto report2 = analyzer.Analyze();
  
  EXPECT_EQ(report1.total_functions, report2.total_functions);
}

// Test 13: Metrics consistency
TEST_F(ComplexityAnalyzerTest, MetricsConsistency) {
  call_graph_->AddNode("func1");
  call_graph_->AddNode("func2");
  call_graph_->AddNode("func3");
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  auto report = analyzer.Analyze();
  
  // Check that metrics are consistent
  EXPECT_GE(report.max_complexity, 0);
  EXPECT_GE(report.average_complexity, 0);
  EXPECT_LE(report.average_complexity, report.max_complexity);
}

// Test 14: Empty function name metrics
TEST_F(ComplexityAnalyzerTest, EmptyFunctionName) {
  ComplexityAnalyzer analyzer(call_graph_.get());
  analyzer.Analyze();
  
  auto metrics = analyzer.GetFunctionMetrics("");
  EXPECT_EQ(metrics.name, "");
}

// Test 15: All report formats
TEST_F(ComplexityAnalyzerTest, AllReportFormats) {
  call_graph_->AddNode("test");
  
  ComplexityAnalyzer analyzer(call_graph_.get());
  analyzer.Analyze();
  
  auto text = analyzer.GenerateReport(ReportFormat::kText);
  auto json = analyzer.GenerateReport(ReportFormat::kJson);
  auto html = analyzer.GenerateReport(ReportFormat::kHtml);
  
  EXPECT_FALSE(text.empty());
  EXPECT_FALSE(json.empty());
  EXPECT_FALSE(html.empty());
  
  // Each format should be different
  EXPECT_NE(text, json);
  EXPECT_NE(json, html);
  EXPECT_NE(text, html);
}

}  // namespace
}  // namespace tools
}  // namespace verilog

