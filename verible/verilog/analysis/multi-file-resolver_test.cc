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

#include "verible/verilog/analysis/multi-file-resolver.h"

#include <memory>
#include <string>
#include <vector>

#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace analysis {
namespace {

// Test fixture for MultiFileResolver tests
class MultiFileResolverTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
  }
  
  // Helper: Parse SystemVerilog code from memory
  void ParseCode(std::string_view code, std::string_view filename = "test.sv") {
    // Create and parse analyzer
    // IMPORTANT: Must keep analyzer alive! SymbolTable stores string_views into it
    auto analyzer = std::make_unique<VerilogAnalyzer>(code, filename);
    absl::Status parse_status = analyzer->Analyze();
    // Ignore parse errors for now
    
    // Add to project - this keeps ownership
    project_->UpdateFileContents(std::string(filename), analyzer.get());
    
    // Keep analyzer alive by storing it
    analyzers_.push_back(std::move(analyzer));
    
    // Build symbol table from this file
    std::vector<absl::Status> diagnostics;
    symbol_table_->BuildSingleTranslationUnit(filename, &diagnostics);
    // Ignore diagnostics for now - we just need the symbol table populated
  }
  
  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::vector<std::unique_ptr<VerilogAnalyzer>> analyzers_;  // Keep alive!
};

// Test fixture for DependencyGraph tests
class DependencyGraphTest : public ::testing::Test {
 protected:
  DependencyGraph graph_;
};

// ============================================================================
// Category 1: DependencyGraph Basic Operations (10 tests)
// ============================================================================

// Test 1: Add single dependency
TEST_F(DependencyGraphTest, AddSingleDependency) {
  graph_.AddDependency("module_a", "module_b");
  
  EXPECT_TRUE(graph_.HasDependency("module_a", "module_b"));
  EXPECT_FALSE(graph_.HasDependency("module_b", "module_a"));
}

// Test 2: Add multiple dependencies from same module
TEST_F(DependencyGraphTest, AddMultipleDependencies) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_a", "module_c");
  
  auto deps = graph_.GetDependencies("module_a");
  EXPECT_EQ(deps.size(), 2);
  EXPECT_TRUE(graph_.HasDependency("module_a", "module_b"));
  EXPECT_TRUE(graph_.HasDependency("module_a", "module_c"));
}

// Test 3: Get dependencies of a module
TEST_F(DependencyGraphTest, GetDependencies) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_a", "module_c");
  graph_.AddDependency("module_b", "module_d");
  
  auto deps_a = graph_.GetDependencies("module_a");
  EXPECT_EQ(deps_a.size(), 2);
  
  auto deps_b = graph_.GetDependencies("module_b");
  EXPECT_EQ(deps_b.size(), 1);
  
  auto deps_c = graph_.GetDependencies("module_c");
  EXPECT_EQ(deps_c.size(), 0);  // No dependencies
}

// Test 4: Get dependents (reverse dependencies)
TEST_F(DependencyGraphTest, GetDependents) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_c", "module_b");
  
  auto dependents = graph_.GetDependents("module_b");
  EXPECT_EQ(dependents.size(), 2);  // Both a and c depend on b
  
  auto dependents_a = graph_.GetDependents("module_a");
  EXPECT_EQ(dependents_a.size(), 0);  // Nothing depends on a
}

// Test 5: Get all modules in graph
TEST_F(DependencyGraphTest, GetAllModules) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_b", "module_c");
  
  auto all_modules = graph_.GetAllModules();
  EXPECT_EQ(all_modules.size(), 3);
  EXPECT_TRUE(all_modules.count("module_a") > 0);
  EXPECT_TRUE(all_modules.count("module_b") > 0);
  EXPECT_TRUE(all_modules.count("module_c") > 0);
}

// Test 6: Detect simple cycle (A -> B -> A)
TEST_F(DependencyGraphTest, DetectSimpleCycle) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_b", "module_a");
  
  EXPECT_TRUE(graph_.HasCycles());
  
  auto cycles = graph_.DetectCircularDependencies();
  EXPECT_GE(cycles.size(), 1);  // At least one cycle
}

// Test 7: No cycles in simple chain (A -> B -> C)
TEST_F(DependencyGraphTest, NoCyclesInChain) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_b", "module_c");
  
  EXPECT_FALSE(graph_.HasCycles());
  
  auto cycles = graph_.DetectCircularDependencies();
  EXPECT_EQ(cycles.size(), 0);
}

// Test 8: Detect longer cycle (A -> B -> C -> A)
TEST_F(DependencyGraphTest, DetectLongerCycle) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_b", "module_c");
  graph_.AddDependency("module_c", "module_a");
  
  EXPECT_TRUE(graph_.HasCycles());
  
  auto cycles = graph_.DetectCircularDependencies();
  EXPECT_GE(cycles.size(), 1);
}

// Test 9: Topological sort with no cycles
TEST_F(DependencyGraphTest, TopologicalSortNoCycles) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_b", "module_c");
  
  auto order = graph_.GetTopologicalOrder();
  EXPECT_GT(order.size(), 0);
  
  // module_c should come before module_b
  // module_b should come before module_a
  // (in topological order, leaves come first)
}

// Test 10: Topological sort with cycles returns empty
TEST_F(DependencyGraphTest, TopologicalSortWithCycles) {
  graph_.AddDependency("module_a", "module_b");
  graph_.AddDependency("module_b", "module_a");
  
  auto order = graph_.GetTopologicalOrder();
  EXPECT_EQ(order.size(), 0);  // Cannot do topological sort with cycles
}

// ============================================================================
// Category 2: MultiFileResolver Basic Operations (10 tests)
// ============================================================================

// Test 11: Construct resolver
TEST_F(MultiFileResolverTest, ConstructResolver) {
  MultiFileResolver resolver(symbol_table_.get());
  // Should construct without error
}

// Test 12: Resolve empty symbol table
TEST_F(MultiFileResolverTest, ResolveEmptySymbolTable) {
  MultiFileResolver resolver(symbol_table_.get());
  
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  auto modules = resolver.GetAllModuleNames();
  EXPECT_EQ(modules.size(), 0);
}

// Test 13: Get module definition (not found)
TEST_F(MultiFileResolverTest, GetModuleDefinitionNotFound) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  const SymbolTableNode* node = resolver.GetModuleDefinition("non_existent");
  EXPECT_EQ(node, nullptr);
}

// Test 14: Has module definition (not found)
TEST_F(MultiFileResolverTest, HasModuleDefinitionNotFound) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  EXPECT_FALSE(resolver.HasModuleDefinition("non_existent"));
}

// Test 15: Get all module names (empty)
TEST_F(MultiFileResolverTest, GetAllModuleNamesEmpty) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  auto modules = resolver.GetAllModuleNames();
  EXPECT_EQ(modules.size(), 0);
}

// Test 16: Get module instances (empty)
TEST_F(MultiFileResolverTest, GetModuleInstancesEmpty) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  auto instances = resolver.GetModuleInstances("module_a");
  EXPECT_EQ(instances.size(), 0);
}

// Test 17: Get instances in module (empty)
TEST_F(MultiFileResolverTest, GetInstancesInModuleEmpty) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  auto instances = resolver.GetInstancesInModule("module_a");
  EXPECT_EQ(instances.size(), 0);
}

// Test 18: Get all instances (empty)
TEST_F(MultiFileResolverTest, GetAllInstancesEmpty) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  const auto& instances = resolver.GetAllInstances();
  EXPECT_EQ(instances.size(), 0);
}

// Test 19: Build dependency graph (empty)
TEST_F(MultiFileResolverTest, BuildDependencyGraphEmpty) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status1 = resolver.ResolveReferences();
  EXPECT_TRUE(status1.ok());
  
  absl::Status status2 = resolver.BuildDependencyGraph();
  EXPECT_TRUE(status2.ok());
  
  const auto& graph = resolver.GetDependencyGraph();
  auto modules = graph.GetAllModules();
  EXPECT_EQ(modules.size(), 0);
}

// Test 20: No circular dependencies (empty)
TEST_F(MultiFileResolverTest, NoCircularDependenciesEmpty) {
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status1 = resolver.ResolveReferences();
  EXPECT_TRUE(status1.ok());
  absl::Status status2 = resolver.BuildDependencyGraph();
  EXPECT_TRUE(status2.ok());
  
  EXPECT_FALSE(resolver.HasCircularDependencies());
  
  auto cycles = resolver.GetCircularDependencies();
  EXPECT_EQ(cycles.size(), 0);
}

// ============================================================================
// Category 3: Module Definition Resolution (10 tests)
// ============================================================================
// Note: These tests will require actual SystemVerilog parsing
// For now, we define the test structure and expectations

// Test 21: Single module definition
TEST_F(MultiFileResolverTest, SingleModuleDefinition) {
  // Parse a simple module
  ParseCode("module test_module; endmodule", "test.sv");
  
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  // Should find the module
  EXPECT_TRUE(resolver.HasModuleDefinition("test_module"));
  
  const auto* node = resolver.GetModuleDefinition("test_module");
  EXPECT_NE(node, nullptr);
  
  auto modules = resolver.GetAllModuleNames();
  EXPECT_EQ(modules.size(), 1);
  EXPECT_EQ(modules[0], "test_module");
}

// Test 22: Multiple module definitions
TEST_F(MultiFileResolverTest, MultipleModuleDefinitions) {
  // Parse multiple modules
  ParseCode("module mod_a; endmodule\nmodule mod_b; endmodule", "test.sv");
  
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  auto modules = resolver.GetAllModuleNames();
  EXPECT_EQ(modules.size(), 2);
  
  EXPECT_TRUE(resolver.HasModuleDefinition("mod_a"));
  EXPECT_TRUE(resolver.HasModuleDefinition("mod_b"));
}

// Test 23: Get all module names
TEST_F(MultiFileResolverTest, GetAllModuleNames) {
  // Parse three modules
  ParseCode("module module_a; endmodule", "a.sv");
  ParseCode("module module_b; endmodule", "b.sv");  
  ParseCode("module module_c; endmodule", "c.sv");
  
  MultiFileResolver resolver(symbol_table_.get());
  absl::Status status = resolver.ResolveReferences();
  EXPECT_TRUE(status.ok());
  
  auto modules = resolver.GetAllModuleNames();
  EXPECT_EQ(modules.size(), 3);
  
  // Verify all three are present
  EXPECT_TRUE(resolver.HasModuleDefinition("module_a"));
  EXPECT_TRUE(resolver.HasModuleDefinition("module_b"));
  EXPECT_TRUE(resolver.HasModuleDefinition("module_c"));
}

// Test 24: Module definition lookup
TEST_F(MultiFileResolverTest, ModuleDefinitionLookup) {
  // TODO: Parse module_a
  
  MultiFileResolver resolver(symbol_table_.get());
  // absl::Status status = resolver.ResolveReferences();
  // EXPECT_TRUE(status.ok());
  
  // EXPECT_TRUE(resolver.HasModuleDefinition("module_a"));
  // EXPECT_FALSE(resolver.HasModuleDefinition("module_z"));
}

// Test 25: Case sensitivity in module names
TEST_F(MultiFileResolverTest, ModuleNameCaseSensitivity) {
  // TODO: Parse "module MyModule; endmodule"
  
  MultiFileResolver resolver(symbol_table_.get());
  // absl::Status status = resolver.ResolveReferences();
  // EXPECT_TRUE(status.ok());
  
  // EXPECT_TRUE(resolver.HasModuleDefinition("MyModule"));
  // EXPECT_FALSE(resolver.HasModuleDefinition("mymodule"));
}

// Test 26: Module with parameters
TEST_F(MultiFileResolverTest, ModuleWithParameters) {
  // TODO: Parse "module param_mod #(parameter WIDTH=8); endmodule"
  
  MultiFileResolver resolver(symbol_table_.get());
  // absl::Status status = resolver.ResolveReferences();
  // EXPECT_TRUE(status.ok());
  
  // EXPECT_TRUE(resolver.HasModuleDefinition("param_mod"));
}

// Test 27: Module with ports
TEST_F(MultiFileResolverTest, ModuleWithPorts) {
  // TODO: Parse module with input/output ports
  
  MultiFileResolver resolver(symbol_table_.get());
  // absl::Status status = resolver.ResolveReferences();
  // EXPECT_TRUE(status.ok());
  
  // const auto* node = resolver.GetModuleDefinition("module_with_ports");
  // EXPECT_NE(node, nullptr);
}

// Test 28: Nested module (should not be visible at top level)
TEST_F(MultiFileResolverTest, NestedModuleNotVisible) {
  // TODO: Parse module with nested module definition
  
  MultiFileResolver resolver(symbol_table_.get());
  // absl::Status status = resolver.ResolveReferences();
  // EXPECT_TRUE(status.ok());
  
  // Nested modules should not be in top-level definitions
  // (SystemVerilog-2005 feature, rarely used)
}

// Test 29: Module redefinition (error)
TEST_F(MultiFileResolverTest, ModuleRedefinition) {
  // TODO: Parse same module name twice
  
  MultiFileResolver resolver(symbol_table_.get());
  // Resolution might fail or report warning
  // absl::Status status = resolver.ResolveReferences();
}

// Test 30: Module with generate blocks
TEST_F(MultiFileResolverTest, ModuleWithGenerateBlocks) {
  // TODO: Parse module with generate blocks
  
  MultiFileResolver resolver(symbol_table_.get());
  // absl::Status status = resolver.ResolveReferences();
  // EXPECT_TRUE(status.ok());
  
  // EXPECT_TRUE(resolver.HasModuleDefinition("gen_module"));
}

// ============================================================================
// End of Day 26 Tests
// ============================================================================
// Total: 30 tests defined
// Status: Test framework complete, ready for implementation
//
// Next steps (Days 27-28):
// 1. Implement MultiFileResolver::ResolveReferences()
// 2. Implement DependencyGraph methods
// 3. Add parsing integration for tests 21-30
// 4. Debug and fix any issues
// 5. Continue with more advanced tests

}  // namespace
}  // namespace analysis
}  // namespace verilog

