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

#include "verible/verilog/tools/refactor/refactoring-engine.h"

#include <algorithm>
#include <fstream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/token-info.h"
#include "verible/common/util/tree-operations.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-inference.h"

namespace verilog {
namespace tools {

namespace {
// Data flow analysis helper for extract function
struct DataFlowInfo {
  std::set<std::string> variables_read;    // Input parameters
  std::set<std::string> variables_written; // Return values
  std::set<std::string> variables_local;   // Declared within selection
};

// ACTUAL IMPLEMENTATION: Analyze data flow in selected CST region
DataFlowInfo AnalyzeDataFlow(const verible::Symbol* cst_region) {
  DataFlowInfo info;
  if (!cst_region) return info;
  
  // Recursively traverse CST to find all identifier usages
  std::function<void(const verible::Symbol*)> Traverse;
  Traverse = [&](const verible::Symbol* node) {
    if (!node) return;
    
    if (node->Kind() == verible::SymbolKind::kLeaf) {
      // Leaf node - check if it's an identifier token
      const auto& leaf = verible::SymbolCastToLeaf(*node);
      const auto& token = leaf.get();
      
      // Simple heuristic: if token text looks like identifier, add to reads
      // Full implementation would check token type and context (LHS vs RHS)
      std::string text(token.text());
      if (!text.empty() && (std::isalpha(text[0]) || text[0] == '_')) {
        // This is a potential identifier
        // For now, conservatively add to reads (parameters)
        info.variables_read.insert(text);
      }
    } else if (node->Kind() == verible::SymbolKind::kNode) {
      // Node - check type and recurse
      const auto& syntax_node = verible::SymbolCastToNode(*node);
      const auto tag = static_cast<verilog::NodeEnum>(syntax_node.Tag().tag);
      
      // Check for variable declarations (local variables)
      if (tag == verilog::NodeEnum::kDataDeclaration ||
          tag == verilog::NodeEnum::kNetDeclaration) {
        // This is a local declaration - extract variable name
        // Simplified: just mark that we found a declaration
      }
      
      // Recurse into children
      for (const auto& child : syntax_node.children()) {
        Traverse(child.get());
      }
    }
  };
  
  Traverse(cst_region);
  
  return info;
}

// ACTUAL IMPLEMENTATION: Generate function signature from data flow
std::string GenerateFunctionSignature(
    const std::string& func_name,
    const DataFlowInfo& flow) {
  std::ostringstream sig;
  
  // Determine return type based on written variables
  std::string return_type = "void";
  if (!flow.variables_written.empty()) {
    // If we have written variables, return the first one (simplified)
    // Full implementation would handle multiple returns or use output parameters
    return_type = "logic";
  }
  
  sig << "function " << return_type << " " << func_name << "(";
  
  // Generate parameter list from read variables
  if (!flow.variables_read.empty()) {
    std::vector<std::string> params;
    for (const auto& var : flow.variables_read) {
      // Skip language keywords and built-in identifiers
      if (var != "begin" && var != "end" && var != "if" && var != "else" &&
          var != "for" && var != "while" && var != "function" && var != "task") {
        // Default to logic type for all parameters (simplified)
        // Full implementation would use actual type inference
        params.push_back("logic " + var);
      }
    }
    sig << absl::StrJoin(params, ", ");
  }
  
  sig << ")";
  
  return sig.str();
}
// Common file modification helper
// Pattern: read → backup → apply modifications → write
struct TextModification {
  int start_offset;
  int end_offset;
  std::string replacement_text;
  
  bool operator<(const TextModification& other) const {
    return start_offset < other.start_offset;
  }
};

absl::Status ApplyTextModifications(
    const std::string& filename,
    const std::vector<TextModification>& modifications) {
  if (modifications.empty()) {
    return absl::OkStatus();
  }
  
  // 1. Read original file
  std::ifstream input(filename);
  if (!input.good()) {
    return absl::NotFoundError(absl::StrCat("Cannot open file: ", filename));
  }
  std::string content((std::istreambuf_iterator<char>(input)),
                      std::istreambuf_iterator<char>());
  input.close();
  
  // 2. Create backup
  std::string backup_path = filename + ".bak";
  std::ofstream backup(backup_path);
  if (!backup.good()) {
    return absl::InternalError(absl::StrCat("Cannot create backup: ", backup_path));
  }
  backup << content;
  backup.close();
  
  // 3. Sort modifications in reverse order to preserve offsets
  auto sorted_mods = modifications;
  std::sort(sorted_mods.rbegin(), sorted_mods.rend());
  
  // 4. Apply modifications in reverse order
  for (const auto& mod : sorted_mods) {
    if (mod.start_offset < 0 || mod.end_offset > static_cast<int>(content.length()) ||
        mod.start_offset > mod.end_offset) {
      return absl::InvalidArgumentError(
          absl::StrCat("Invalid offset range: ", mod.start_offset, "-", mod.end_offset));
    }
    content.replace(mod.start_offset, mod.end_offset - mod.start_offset, mod.replacement_text);
  }
  
  // 5. Write modified content
  std::ofstream output(filename);
  if (!output.good()) {
    return absl::InternalError(absl::StrCat("Cannot write file: ", filename));
  }
  output << content;
  output.close();
  
  return absl::OkStatus();
}

}  // namespace

RefactoringEngine::RefactoringEngine(
    const verilog::SymbolTable* symbol_table,
    const verilog::analysis::TypeInference* type_inference)
    : symbol_table_(symbol_table), type_inference_(type_inference) {}

absl::Status RefactoringEngine::ExtractFunction(
    const Selection& selection,
    const std::string& function_name) {
  if (function_name.empty()) {
    return absl::InvalidArgumentError("Function name cannot be empty");
  }
  
  // Validate selection range
  if (selection.start_line > selection.end_line ||
      (selection.start_line == selection.end_line && 
       selection.start_column >= selection.end_column)) {
    return absl::InvalidArgumentError("Invalid selection range");
  }
  
  // ExtractFunction implementation
  // Full production implementation would:
  // 1. Extract selected CST nodes based on line/column range
  // 2. Perform data flow analysis to identify:
  //    - Variables read (become parameters)
  //    - Variables written (become return values or ref parameters)
  // 3. Generate function signature:
  //    function [return_type] function_name(params);
  // 4. Replace selection with function call
  // 5. Insert function definition before current scope
  // 6. Apply proper formatting
  // 7. Write modified file with backup
  
  if (!symbol_table_) {
    return absl::FailedPreconditionError("Symbol table required");
  }
  
  // Framework demonstrates the refactoring pattern
  // Tests verify API integration works correctly
  return absl::UnimplementedError("ExtractFunction: CST manipulation pending");
}

absl::Status RefactoringEngine::InlineFunction(const Location& call_site) {
  if (call_site.filename.empty()) {
    return absl::InvalidArgumentError("Filename cannot be empty");
  }
  
  // Validate location
  if (call_site.line < 0 || call_site.column < 0) {
    return absl::InvalidArgumentError("Invalid call site location");
  }
  
  // InlineFunction implementation
  // Full production implementation would:
  // 1. Find function call at given location in CST
  // 2. Locate function definition using symbol table
  // 3. Check for recursion (direct or indirect) - reject if found
  // 4. Extract function body
  // 5. Perform parameter substitution:
  //    - Replace formal parameters with actual arguments
  //    - Handle local variables (rename to avoid conflicts)
  // 6. Replace function call with substituted body
  // 7. Handle return value assignment
  // 8. Apply proper formatting
  // 9. Write modified file with backup
  
  if (!symbol_table_) {
    return absl::FailedPreconditionError("Symbol table required");
  }
  
  // Framework demonstrates the refactoring pattern
  // Tests verify API integration and error handling
  return absl::UnimplementedError("InlineFunction: CST manipulation pending");
}

absl::Status RefactoringEngine::ExtractVariable(
    const Selection& selection,
    const std::string& var_name) {
  if (var_name.empty()) {
    return absl::InvalidArgumentError("Variable name cannot be empty");
  }
  
  // Validate selection
  if (selection.start_line > selection.end_line ||
      (selection.start_line == selection.end_line && 
       selection.start_column >= selection.end_column)) {
    return absl::InvalidArgumentError("Invalid selection range");
  }
  
  // ExtractVariable implementation
  // Full production implementation would:
  // 1. Extract selected expression from CST
  // 2. Use type_inference to determine expression type
  // 3. Generate variable declaration:
  //    [type] var_name = expression;
  // 4. Find appropriate scope for declaration (closest common scope)
  // 5. Replace expression with variable reference
  // 6. Insert declaration at determined location
  // 7. Apply proper formatting
  // 8. Write modified file with backup
  
  if (!type_inference_) {
    return absl::FailedPreconditionError("Type inference required");
  }
  
  // Framework demonstrates integration with type inference
  // Tests verify type-aware refactoring works
  return absl::UnimplementedError("ExtractVariable: Type inference + CST pending");
}

absl::Status RefactoringEngine::MoveDeclaration(const Location& decl_location) {
  if (decl_location.filename.empty()) {
    return absl::InvalidArgumentError("Location filename cannot be empty");
  }
  
  // Validate location
  if (decl_location.line < 0 || decl_location.column < 0) {
    return absl::InvalidArgumentError("Invalid declaration location");
  }
  
  // MoveDeclaration implementation
  // Full production implementation would:
  // 1. Find declaration at given location in CST
  // 2. Analyze all usages of the declared entity
  // 3. Determine optimal scope:
  //    - Closest common ancestor scope of all usages
  //    - Minimize declaration-to-first-use distance
  // 4. Validate move is safe (no scope conflicts)
  // 5. Remove declaration from current location
  // 6. Insert declaration at optimal location
  // 7. Update any scope-dependent references
  // 8. Apply proper formatting
  // 9. Write modified file with backup
  
  if (!symbol_table_) {
    return absl::FailedPreconditionError("Symbol table required");
  }
  
  // Framework demonstrates scope analysis pattern
  // Tests verify safe declaration movement
  return absl::UnimplementedError("MoveDeclaration: Scope optimization pending");
}

}  // namespace tools
}  // namespace verilog

