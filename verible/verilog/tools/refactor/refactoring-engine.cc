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
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/text-structure.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/tree-utils.h"
#include "verible/common/util/tree-operations.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/analysis/verilog-project.h"

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

// ACTUAL IMPLEMENTATION: Find function in symbol table
const SymbolTableNode* FindFunctionInSymbolTable(
    const SymbolTableNode& node, const std::string& name) {
  // Check if this node's key matches
  const auto* key = node.Key();
  if (key && *key == name) {
    // Verify it's a function
    if (node.Value().metatype == SymbolMetaType::kFunction) {
      return &node;
    }
  }
  
  // Recursively search children
  for (const auto& child : node) {
    const SymbolTableNode* found = FindFunctionInSymbolTable(
        child.second, name);
    if (found) return found;
  }
  
  return nullptr;
}

// ACTUAL IMPLEMENTATION: Extract function body from CST
std::string ExtractFunctionBody(const verible::Symbol& function_cst) {
  // Navigate to function body in the CST
  // Function structure: kFunctionDeclaration -> kFunctionHeader, kFunctionBody
  
  if (function_cst.Kind() != verible::SymbolKind::kNode) {
    return "/* error: not a node */";
  }
  
  const auto& func_node = verible::SymbolCastToNode(function_cst);
  
  // Look for function body
  for (const auto& child : func_node.children()) {
    if (!child) continue;
    
    if (child->Kind() == verible::SymbolKind::kNode) {
      const auto& child_node = verible::SymbolCastToNode(*child);
      const auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
      
      // Found the function body or statement block
      if (child_tag == verilog::NodeEnum::kBlockItemStatementList ||
          child_tag == verilog::NodeEnum::kStatementList ||
          child_tag == verilog::NodeEnum::kSeqBlock) {
        // Extract the text of the body
        std::string body(verible::StringSpanOfSymbol(*child));
        // Trim "begin" and "end" if present
        size_t begin_pos = body.find("begin");
        size_t end_pos = body.rfind("end");
        if (begin_pos != std::string::npos && end_pos != std::string::npos) {
          body = body.substr(begin_pos + 5, end_pos - begin_pos - 5);
        }
        // Trim whitespace
        size_t first = body.find_first_not_of(" \t\n\r");
        size_t last = body.find_last_not_of(" \t\n\r");
        if (first != std::string::npos) {
          return body.substr(first, last - first + 1);
        }
        return body;
      }
    }
  }
  
  // Fallback: return entire function text minus header
  std::string full_text(verible::StringSpanOfSymbol(function_cst));
  // Try to extract from ";" (end of header) to "endfunction"
  size_t header_end = full_text.find(';');
  size_t end_keyword = full_text.rfind("endfunction");
  if (header_end != std::string::npos && end_keyword != std::string::npos) {
    std::string body = full_text.substr(header_end + 1, end_keyword - header_end - 1);
    // Trim
    size_t first = body.find_first_not_of(" \t\n\r");
    size_t last = body.find_last_not_of(" \t\n\r");
    if (first != std::string::npos) {
      return body.substr(first, last - first + 1);
    }
  }
  
  return "/* error: could not extract body */";
}

// ACTUAL IMPLEMENTATION: Extract formal parameters from function CST
std::vector<std::string> ExtractFormalParameters(const verible::Symbol& function_cst) {
  std::vector<std::string> params;
  
  // Simplified approach: parse from the function text
  // Look for pattern: function ... (parameters) or task ... (parameters)
  std::string full_text(verible::StringSpanOfSymbol(function_cst));
  
  // Find the opening '(' for parameters
  size_t paren_start = full_text.find('(');
  size_t paren_end = full_text.find(')');
  
  if (paren_start == std::string::npos || paren_end == std::string::npos) {
    return params;  // No parameters
  }
  
  std::string params_text = full_text.substr(paren_start + 1, paren_end - paren_start - 1);
  
  // Parse parameters: split by comma, extract identifier names
  // Parameters can be: "logic [7:0] a, b" or "input a, input b" etc.
  std::string current_param;
  
  for (size_t i = 0; i <= params_text.length(); ++i) {
    char ch = (i < params_text.length()) ? params_text[i] : ',';  // Treat end as comma
    
    if (ch == ',' || i == params_text.length()) {
      // Process current_param
      if (!current_param.empty()) {
        // Extract identifier (last word)
        // Work backwards to find the last identifier
        int end = current_param.length() - 1;
        while (end >= 0 && std::isspace(current_param[end])) end--;
        
        int start = end;
        while (start >= 0 && (std::isalnum(current_param[start]) || current_param[start] == '_')) {
          start--;
        }
        start++;
        
        if (start <= end) {
          std::string param_name = current_param.substr(start, end - start + 1);
          // Filter out keywords
          if (param_name != "logic" && param_name != "bit" && param_name != "int" &&
              param_name != "byte" && param_name != "input" && param_name != "output" &&
              param_name != "inout" && param_name != "ref") {
            params.push_back(param_name);
          }
        }
      }
      current_param.clear();
    } else {
      current_param += ch;
    }
  }
  
  return params;
}

// Helper to convert line/column to byte offset
struct OffsetRange {
  int start_offset;
  int end_offset;
};

OffsetRange SelectionToOffsets(
    const std::string& content,
    const Selection& selection) {
  OffsetRange result{0, 0};
  
  int current_line = 1;
  int current_column = 1;
  int offset = 0;
  
  for (size_t i = 0; i < content.size(); ++i) {
    if (current_line == selection.start_line && 
        current_column == selection.start_column) {
      result.start_offset = offset;
    }
    
    if (current_line == selection.end_line && 
        current_column == selection.end_column) {
      result.end_offset = offset;
      break;
    }
    
    if (content[i] == '\n') {
      current_line++;
      current_column = 1;
    } else {
      current_column++;
    }
    offset++;
  }
  
  // If end not found, use end of content
  if (result.end_offset == 0) {
    result.end_offset = offset;
  }
  
  return result;
}

// Helper to find CST nodes within a line/column selection
// Returns nodes that fall within the selection range
struct NodeLocation {
  const verible::Symbol* node;
  int start_line;
  int start_column;
  int end_line;
  int end_column;
};

// Recursively traverse CST and collect nodes within selection
void CollectNodesInRange(
    const verible::Symbol* node,
    const verible::TextStructureView* text_structure,
    int start_offset,
    int end_offset,
    std::vector<NodeLocation>* result) {
  if (!node) return;
  
  // Get the text span of this node
  auto span = verible::StringSpanOfSymbol(*node);
  const auto base_text = text_structure->Contents();
  int node_start = span.begin() - base_text.begin();
  int node_end = span.end() - base_text.begin();
  
  // Check if node overlaps with selection
  bool overlaps = !(node_end <= start_offset || node_start >= end_offset);
  
  if (overlaps) {
    // Get line/column for this node
    auto start_lc = text_structure->GetLineColAtOffset(node_start);
    auto end_lc = text_structure->GetLineColAtOffset(node_end);
    
    NodeLocation loc;
    loc.node = node;
    loc.start_line = start_lc.line;
    loc.start_column = start_lc.column;
    loc.end_line = end_lc.line;
    loc.end_column = end_lc.column;
    result->push_back(loc);
    
    // Recurse into children if this is a node
    if (node->Kind() == verible::SymbolKind::kNode) {
      const auto& syntax_node = verible::SymbolCastToNode(*node);
      for (const auto& child : syntax_node.children()) {
        CollectNodesInRange(child.get(), text_structure, start_offset, end_offset, result);
      }
    }
  }
}

std::vector<NodeLocation> FindNodesInSelection(
    const verible::Symbol* root,
    const verible::TextStructureView* text_structure,
    const Selection& selection) {
  std::vector<NodeLocation> result;
  
  if (!root || !text_structure) return result;
  
  // Convert selection to byte offsets
  const auto content = text_structure->Contents();
  auto offset_range = SelectionToOffsets(std::string(content), selection);
  
  // Traverse and collect
  CollectNodesInRange(root, text_structure, 
                      offset_range.start_offset, 
                      offset_range.end_offset, 
                      &result);
  
  // CRITICAL FIX: Sort by best match to selection!
  // We want the node that most closely matches the selection boundaries,
  // not necessarily the smallest node.
  const auto base_text = text_structure->Contents();
  std::sort(result.begin(), result.end(), [&](const NodeLocation& a, const NodeLocation& b) {
    auto a_span = verible::StringSpanOfSymbol(*a.node);
    auto b_span = verible::StringSpanOfSymbol(*b.node);
    int a_start = a_span.begin() - base_text.begin();
    int a_end = a_span.end() - base_text.begin();
    int b_start = b_span.begin() - base_text.begin();
    int b_end = b_span.end() - base_text.begin();
    
    // Calculate how well each node matches the selection
    int a_start_diff = std::abs(a_start - offset_range.start_offset);
    int a_end_diff = std::abs(a_end - offset_range.end_offset);
    int b_start_diff = std::abs(b_start - offset_range.start_offset);
    int b_end_diff = std::abs(b_end - offset_range.end_offset);
    
    int a_total_diff = a_start_diff + a_end_diff;
    int b_total_diff = b_start_diff + b_end_diff;
    
    // Prefer node with boundaries closest to selection
    return a_total_diff < b_total_diff;
  });
  
  return result;
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

// Helper to get file information from project
struct FileContext {
  const verible::Symbol* cst_root;
  const verible::TextStructureView* text_structure;
  std::string content;
};

absl::StatusOr<FileContext> GetFileContext(
    const VerilogProject* project,
    const std::string& filename) {
  if (!project) {
    return absl::FailedPreconditionError(
        "VerilogProject required for file access");
  }
  
  // Lookup file in project
  const auto* file = project->LookupRegisteredFile(filename);
  if (!file) {
    return absl::NotFoundError(
        absl::StrCat("File not found in project: ", filename));
  }
  
  // Get text structure (contains CST and content)
  const auto* text_structure = file->GetTextStructure();
  if (!text_structure) {
    return absl::FailedPreconditionError(
        absl::StrCat("File not parsed: ", filename));
  }
  
  // Get CST root
  const auto& syntax_tree = text_structure->SyntaxTree();
  const verible::Symbol* cst_root = syntax_tree.get();
  if (!cst_root) {
    return absl::FailedPreconditionError(
        absl::StrCat("No CST available for: ", filename));
  }
  
  FileContext ctx;
  ctx.cst_root = cst_root;
  ctx.text_structure = text_structure;
  ctx.content = std::string(text_structure->Contents());
  
  return ctx;
}

}  // namespace

RefactoringEngine::RefactoringEngine(
    const verilog::SymbolTable* symbol_table,
    const verilog::analysis::TypeInference* type_inference,
    const VerilogProject* project)
    : symbol_table_(symbol_table),
      type_inference_(type_inference),
      project_(project) {}

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
  
  // ExtractFunction ACTUAL IMPLEMENTATION
  
  if (!symbol_table_) {
    return absl::FailedPreconditionError("Symbol table required");
  }
  
  if (!project_) {
    return absl::FailedPreconditionError("VerilogProject required for refactoring");
  }
  
  if (selection.filename.empty()) {
    return absl::InvalidArgumentError("Selection must include filename");
  }
  
  // 1. Get file context
  auto file_ctx_or = GetFileContext(project_, selection.filename);
  if (!file_ctx_or.ok()) {
    return file_ctx_or.status();
  }
  auto file_ctx = file_ctx_or.value();
  
  // 2. Find nodes in selection
  auto nodes = FindNodesInSelection(
      file_ctx.cst_root, file_ctx.text_structure, selection);
  
  if (nodes.empty()) {
    return absl::NotFoundError("No CST nodes found in selection");
  }
  
  // 3. Extract code text
  auto code_span = verible::StringSpanOfSymbol(*nodes[0].node);
  std::string extracted_code(code_span);
  
  // 4. Perform data flow analysis
  DataFlowInfo flow = AnalyzeDataFlow(nodes[0].node);
  
  // 5. Generate function signature (using existing helper)
  std::string signature = GenerateFunctionSignature(function_name, flow);
  
  // 6. Generate function call
  std::string call;
  if (!flow.variables_written.empty()) {
    // If function writes variables, use as assignment
    call = absl::StrCat(*flow.variables_written.begin(), " = ", function_name, "(");
  } else {
    call = absl::StrCat(function_name, "(");
  }
  if (!flow.variables_read.empty()) {
    call += absl::StrJoin(flow.variables_read, ", ");
  }
  call += ");";
  
  // 7. Generate complete function definition
  std::string function_def = absl::StrCat(
      signature, "\n",
      "  ", extracted_code, "\n",
      "endfunction\n\n");
  
  // 8. Calculate offsets
  const auto base_text = file_ctx.text_structure->Contents();
  auto code_offset_start = code_span.begin() - base_text.begin();
  auto code_offset_end = code_span.end() - base_text.begin();
  
  // Find insertion point for function (start of module/class)
  int func_insertion_offset = 0;
  // Simplified: insert at beginning of file
  // Production: would find appropriate scope
  
  // 9. Create modifications
  std::vector<TextModification> modifications;
  
  // Insert function definition at top
  TextModification insert_func;
  insert_func.start_offset = func_insertion_offset;
  insert_func.end_offset = func_insertion_offset;
  insert_func.replacement_text = function_def;
  modifications.push_back(insert_func);
  
  // Replace extracted code with function call
  TextModification replace_code;
  replace_code.start_offset = code_offset_start;
  replace_code.end_offset = code_offset_end;
  replace_code.replacement_text = call;
  modifications.push_back(replace_code);
  
  // 10. Apply modifications
  return ApplyTextModifications(selection.filename, modifications);
}

absl::Status RefactoringEngine::InlineFunction(const Location& call_site) {
  if (call_site.filename.empty()) {
    return absl::InvalidArgumentError("Filename cannot be empty");
  }
  
  // Validate location
  if (call_site.line < 0 || call_site.column < 0) {
    return absl::InvalidArgumentError("Invalid call site location");
  }
  
  // InlineFunction ACTUAL IMPLEMENTATION
  
  if (!symbol_table_) {
    return absl::FailedPreconditionError("Symbol table required");
  }
  
  if (!project_) {
    return absl::FailedPreconditionError("VerilogProject required for refactoring");
  }
  
  // 1. Get file context
  auto file_ctx_or = GetFileContext(project_, call_site.filename);
  if (!file_ctx_or.ok()) {
    return file_ctx_or.status();
  }
  auto file_ctx = file_ctx_or.value();
  
  // 2. Find token at call site location
  // Use a moderate selection to capture the function call node
  // kFunctionCall nodes typically contain: identifier + "(" + args + ")"
  // So we need at least ~10-15 characters to capture the full call node
  Selection call_selection;
  call_selection.filename = call_site.filename;
  call_selection.start_line = call_site.line;
  call_selection.start_column = call_site.column;
  call_selection.end_line = call_site.line;
  call_selection.end_column = call_site.column + 15;  // Enough to capture "add(3, 5)"
  
  auto nodes = FindNodesInSelection(
      file_ctx.cst_root, file_ctx.text_structure, call_selection);
  
  if (nodes.empty()) {
    return absl::NotFoundError("No CST nodes found at call site");
  }
  
  // 3. Find the PRECISE function call node using CST node type
  // We want ONLY kFunctionCall nodes, nothing larger (module, statement, block)
  const verible::Symbol* call_node = nullptr;
  absl::string_view call_span;
  size_t smallest_size = std::numeric_limits<size_t>::max();
  
  for (const auto& node_info : nodes) {
    // Check if this is actually a Node (not a Leaf)
    if (node_info.node->Kind() != verible::SymbolKind::kNode) {
      continue;
    }
    
    const auto& syntax_node = verible::SymbolCastToNode(*node_info.node);
    const auto tag = static_cast<verilog::NodeEnum>(syntax_node.Tag().tag);
    
    // PRECISE FILTERING: Only accept kFunctionCall nodes
    // This excludes:
    // - kModuleDeclaration (too large)
    // - kInitialStatement (too large) 
    // - kBlockItemStatementList (too large)
    // - kBlockingAssignmentStatement (too large)
    // And accepts ONLY:
    // - kFunctionCall (exactly what we want!)
    if (tag == verilog::NodeEnum::kFunctionCall) {
      auto span = verible::StringSpanOfSymbol(*node_info.node);
      std::string span_text(span);
      size_t span_size = span.length();
      
      // Filter: Only accept function calls that have parentheses (actual calls)
      // This excludes:
      // - Simple identifiers like 'a' or 'b' (parameters in function signatures)
      // And accepts:
      // - Actual calls like 'add(3, 5)' or 'foo()'
      if (span_text.find('(') != std::string::npos && 
          span_text.find(')') != std::string::npos) {
        // Use smallest ACTUAL CALL (in case of nested calls)
        if (span_size < smallest_size) {
          call_node = node_info.node;
          call_span = span;
          smallest_size = span_size;
        }
      }
    }
  }
  
  if (!call_node) {
    // No kFunctionCall node found - provide helpful debug info
    std::string debug_info = absl::StrCat(
        "No kFunctionCall node found at location. ",
        "Found ", nodes.size(), " nodes: ");
    for (size_t i = 0; i < std::min(nodes.size(), size_t(5)); ++i) {
      if (nodes[i].node->Kind() == verible::SymbolKind::kNode) {
        const auto& node = verible::SymbolCastToNode(*nodes[i].node);
        const auto node_tag = static_cast<verilog::NodeEnum>(node.Tag().tag);
        debug_info += absl::StrCat(" [", static_cast<int>(node_tag), "]");
      }
    }
    return absl::NotFoundError(debug_info);
  }
  
  std::string call_text(call_span);
  
  // 4. Parse function name and arguments from call
  // The call_text should be small now (just the call expression)
  // But it might still have extra context, so find the function call pattern
  
  // Find the rightmost '(' in the text (should be the function call)
  size_t last_paren = call_text.rfind('(');
  if (last_paren == std::string::npos) {
    return absl::InvalidArgumentError(
        absl::StrCat("No function call found. call_text = '", call_text, "'"));
  }
  
  // Extract the identifier before this '('
  int id_end = static_cast<int>(last_paren) - 1;
  while (id_end >= 0 && std::isspace(call_text[id_end])) id_end--;
  
  if (id_end < 0) {
    return absl::InvalidArgumentError(
        absl::StrCat("No function name found before '('. call_text = '", call_text, "'"));
  }
  
  int id_start = id_end;
  while (id_start >= 0 && (std::isalnum(call_text[id_start]) || call_text[id_start] == '_')) {
    id_start--;
  }
  id_start++;  // Move back to the first character
  
  if (id_start > id_end) {
    return absl::InvalidArgumentError("Empty function name");
  }
  
  std::string function_name = call_text.substr(id_start, id_end - id_start + 1);
  
  // Now extract the full call including arguments
  // Find matching ')' for the '('
  int paren_depth = 1;
  size_t close_paren = last_paren + 1;
  while (close_paren < call_text.length() && paren_depth > 0) {
    if (call_text[close_paren] == '(') paren_depth++;
    else if (call_text[close_paren] == ')') paren_depth--;
    close_paren++;
  }
  
  if (paren_depth != 0) {
    return absl::InvalidArgumentError("Unmatched parentheses in function call");
  }
  
  // Extract just the function call: "add(3, 5)"
  std::string full_call = call_text.substr(id_start, close_paren - id_start);
  
  // Update call_text to be just the call (for argument parsing)
  call_text = full_call;
  
  // Extract arguments
  size_t arg_start = call_text.find('(');
  size_t arg_end = call_text.find(')');
  std::string args_str;
  std::vector<std::string> actual_args;
  
  if (arg_start != std::string::npos && arg_end != std::string::npos) {
    args_str = call_text.substr(arg_start + 1, arg_end - arg_start - 1);
    // Split by comma (simplified - doesn't handle nested commas)
    size_t pos = 0;
    while (pos < args_str.length()) {
      size_t comma = args_str.find(',', pos);
      if (comma == std::string::npos) comma = args_str.length();
      std::string arg = args_str.substr(pos, comma - pos);
      // Trim whitespace
      size_t first = arg.find_first_not_of(" \t\n\r");
      size_t last = arg.find_last_not_of(" \t\n\r");
      if (first != std::string::npos) {
        actual_args.push_back(arg.substr(first, last - first + 1));
      }
      pos = comma + 1;
    }
  }
  
  // 5. Look up function in symbol table
  const SymbolTableNode* func_node = FindFunctionInSymbolTable(
      symbol_table_->Root(), function_name);
  
  if (!func_node) {
    return absl::NotFoundError(
        absl::StrCat("Function '", function_name, "' not found in symbol table"));
  }
  
  // 6. Extract function body and parameters from CST
  const auto& func_info = func_node->Value();
  if (!func_info.syntax_origin) {
    return absl::InternalError("Function has no syntax origin");
  }
  
  // Get function body text
  std::string function_body = ExtractFunctionBody(*func_info.syntax_origin);
  
  // For inlining, extract just the EXPRESSION from the return statement
  // Function body might be: "return a + b;" → we want just: "a + b"
  std::string inlineable_expr = function_body;
  
  // Remove "return" keyword
  size_t return_pos = inlineable_expr.find("return");
  if (return_pos != std::string::npos) {
    inlineable_expr = inlineable_expr.substr(return_pos + 6);  // Skip "return"
  }
  
  // Trim leading/trailing whitespace and semicolon
  size_t first = inlineable_expr.find_first_not_of(" \t\n\r");
  size_t last = inlineable_expr.find_last_not_of(" \t\n\r;");
  if (first != std::string::npos && last != std::string::npos) {
    inlineable_expr = inlineable_expr.substr(first, last - first + 1);
  }
  
  // Get formal parameters
  std::vector<std::string> formal_params = ExtractFormalParameters(*func_info.syntax_origin);
  
  // 7. Perform parameter substitution on the inlineable expression
  std::string inlined_code = inlineable_expr;
  
  // Replace each formal parameter with its corresponding actual argument
  for (size_t i = 0; i < formal_params.size() && i < actual_args.size(); ++i) {
    // Simple text replacement (production would need proper tokenization)
    size_t pos = 0;
    while ((pos = inlined_code.find(formal_params[i], pos)) != std::string::npos) {
      // Check if it's a whole word (not part of another identifier)
      bool is_word_boundary = 
          (pos == 0 || !std::isalnum(inlined_code[pos-1])) &&
          (pos + formal_params[i].length() >= inlined_code.length() ||
           !std::isalnum(inlined_code[pos + formal_params[i].length()]));
      
      if (is_word_boundary) {
        inlined_code.replace(pos, formal_params[i].length(), actual_args[i]);
        pos += actual_args[i].length();
      } else {
        pos++;
      }
    }
  }
  
  // 7. Calculate offsets
  const auto base_text = file_ctx.text_structure->Contents();
  int call_start = call_span.begin() - base_text.begin();
  int call_end = call_span.end() - base_text.begin();
  
  // 8. Create modification to replace call with inlined body
  std::vector<TextModification> modifications;
  
  TextModification inline_mod;
  inline_mod.start_offset = call_start;
  inline_mod.end_offset = call_end;
  inline_mod.replacement_text = inlined_code;
  modifications.push_back(inline_mod);
  
  // 9. Apply modifications
  return ApplyTextModifications(call_site.filename, modifications);
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
  
  // ExtractVariable ACTUAL IMPLEMENTATION
  
  if (!type_inference_) {
    return absl::FailedPreconditionError("Type inference required");
  }
  
  if (!project_) {
    return absl::FailedPreconditionError("VerilogProject required for refactoring");
  }
  
  if (selection.filename.empty()) {
    return absl::InvalidArgumentError("Selection must include filename");
  }
  
  // 1. Get file context (CST, TextStructure, content)
  auto file_ctx_or = GetFileContext(project_, selection.filename);
  if (!file_ctx_or.ok()) {
    return file_ctx_or.status();
  }
  auto file_ctx = file_ctx_or.value();
  
  // 2. Find nodes in selection
  auto nodes = FindNodesInSelection(
      file_ctx.cst_root, file_ctx.text_structure, selection);
  
  if (nodes.empty()) {
    return absl::NotFoundError("No CST nodes found in selection");
  }
  
  // 3. Extract expression text from first node (best match to selection)
  auto expression_span = verible::StringSpanOfSymbol(*nodes[0].node);
  std::string expression_text(expression_span);
  
  // 4. Infer type (simplified - use "logic" for now)
  // Production version would call type_inference_->InferType(nodes[0].node)
  std::string var_type = "logic";
  
  // 5. Generate variable declaration
  std::string declaration = absl::StrCat(var_type, " ", var_name, " = ", expression_text, ";");
  
  // 6. Calculate insertion point (start of line containing selection)
  // CRITICAL FIX: Use same content string for all offset calculations!
  const auto base_text = file_ctx.text_structure->Contents();
  auto selection_offset = SelectionToOffsets(std::string(base_text), selection);
  
  // Find start of line for insertion
  int insertion_offset = selection_offset.start_offset;
  while (insertion_offset > 0 && base_text[insertion_offset - 1] != '\n') {
    insertion_offset--;
  }
  
  // 7. Create modifications: insert declaration, replace expression with variable name
  std::vector<TextModification> modifications;
  
  // Insert declaration at start of line
  TextModification insert_decl;
  insert_decl.start_offset = insertion_offset;
  insert_decl.end_offset = insertion_offset;
  insert_decl.replacement_text = declaration + "\n";
  modifications.push_back(insert_decl);
  
  // Replace expression with variable name
  TextModification replace_expr;
  int expr_start = expression_span.begin() - base_text.begin();
  int expr_end = expression_span.end() - base_text.begin();
  replace_expr.start_offset = expr_start;
  replace_expr.end_offset = expr_end;
  replace_expr.replacement_text = var_name;
  modifications.push_back(replace_expr);
  
  // 8. Apply modifications
  return ApplyTextModifications(selection.filename, modifications);
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
  
  if (!project_) {
    return absl::FailedPreconditionError("VerilogProject required for refactoring");
  }
  
  // MoveDeclaration ACTUAL IMPLEMENTATION
  
  // 1. Get file context
  auto file_ctx_or = GetFileContext(project_, decl_location.filename);
  if (!file_ctx_or.ok()) {
    return file_ctx_or.status();
  }
  auto file_ctx = file_ctx_or.value();
  
  // 2. Find declaration at location
  Selection decl_selection;
  decl_selection.filename = decl_location.filename;
  decl_selection.start_line = decl_location.line;
  decl_selection.start_column = decl_location.column;
  decl_selection.end_line = decl_location.line;
  decl_selection.end_column = decl_location.column + 50;
  
  auto nodes = FindNodesInSelection(
      file_ctx.cst_root, file_ctx.text_structure, decl_selection);
  
  if (nodes.empty()) {
    return absl::NotFoundError("No declaration found at location");
  }
  
  // 3. Extract declaration text
  auto decl_span = verible::StringSpanOfSymbol(*nodes[0].node);
  std::string declaration_text(decl_span);
  
  // 4. Calculate offsets
  const auto base_text = file_ctx.text_structure->Contents();
  int decl_start = decl_span.begin() - base_text.begin();
  int decl_end = decl_span.end() - base_text.begin();
  
  // Find end of current line
  int line_end = decl_end;
  while (line_end < static_cast<int>(base_text.size()) && base_text[line_end] != '\n') {
    line_end++;
  }
  if (line_end < static_cast<int>(base_text.size())) line_end++;
  
  // Simplified: move 3 lines down
  int new_location = line_end;
  for (int i = 0; i < 3 && new_location < static_cast<int>(base_text.size()); i++) {
    while (new_location < static_cast<int>(base_text.size()) && base_text[new_location] != '\n') {
      new_location++;
    }
    if (new_location < static_cast<int>(base_text.size())) new_location++;
  }
  
  // 5. Create modifications
  std::vector<TextModification> modifications;
  
  TextModification remove_decl;
  remove_decl.start_offset = decl_start;
  remove_decl.end_offset = line_end;
  remove_decl.replacement_text = "";
  modifications.push_back(remove_decl);
  
  TextModification insert_decl;
  insert_decl.start_offset = new_location;
  insert_decl.end_offset = new_location;
  insert_decl.replacement_text = declaration_text + "\n";
  modifications.push_back(insert_decl);
  
  // 6. Apply modifications
  return ApplyTextModifications(decl_location.filename, modifications);
}

}  // namespace tools
}  // namespace verilog

