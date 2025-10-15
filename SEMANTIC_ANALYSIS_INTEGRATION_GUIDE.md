# Semantic Analysis Integration Guide

**Date:** 2025-10-15  
**Purpose:** Week 2 Day 3 - Practical guide for using and extending Verible's semantic analysis  
**Audience:** Tool builders, linter rule developers, IDE integrators

---

## 🎯 Overview

This guide shows you how to:
1. Use existing semantic analysis capabilities
2. Create new linter rules with semantic checks
3. Integrate with the symbol table
4. Extend LSP with new semantic features
5. Build tools on top of Verible's semantic infrastructure

---

## 📚 Prerequisites

### What You Need to Know

**Before reading this guide, familiarize yourself with:**
1. Verible's symbol table (see `EXISTING_SYMBOL_TABLE_GUIDE.md`)
2. Existing semantic features (see `EXISTING_SEMANTIC_ANALYSIS_SURVEY.md`)
3. Basic Verible architecture

**You should understand:**
- How Verible parses SystemVerilog (CST)
- What the symbol table contains
- How reference resolution works

---

## 🏗️ Architecture Recap

```
SystemVerilog Source
    ↓
VerilogAnalyzer (Parse)
    ↓
ConcreteSyntaxTree (CST)
    ↓
Symbol Table Builder
    ↓
Symbol Table (2,937 lines)
    ├─ Symbol Collection
    ├─ Scope Management
    ├─ Reference Resolution
    └─ Type Tracking
    ↓
Your Tool / Linter Rule / LSP Feature
```

---

## 📖 Part 1: Using the Symbol Table

### Example 1: Basic Symbol Lookup

**Use Case:** Find declaration of an identifier

```cpp
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

// Step 1: Create project and open files
verilog::VerilogProject project("/path/to/root", {/* include dirs */});
auto status = project.OpenTranslationUnit("module.sv");

// Step 2: Build symbol table
verilog::SymbolTable symbol_table(&project);
std::vector<absl::Status> build_statuses;
symbol_table.BuildSingleTranslationUnit("module.sv", &build_statuses);

// Step 3: Resolve references
std::vector<absl::Status> resolve_statuses;
symbol_table.Resolve(&resolve_statuses);

// Step 4: Look up a symbol
const verilog::SymbolTableNode* root = symbol_table.Root();
const verilog::SymbolTableNode* module = root->Find("my_module");

if (module) {
  std::cout << "Found module: " << module->Key() << std::endl;
  
  // Access children (ports, variables, etc.)
  for (const auto& [name, child] : module->Children()) {
    const verilog::SymbolInfo& info = child.Value();
    std::cout << "  Symbol: " << name 
              << " Type: " << info.metatype << std::endl;
  }
}
```

### Example 2: Finding All References to a Symbol

**Use Case:** Implement "find all references" feature

```cpp
// Given: identifier at cursor position
std::string_view identifier = "my_variable";

// Step 1: Find the declaration
const verilog::SymbolTableNode* decl = 
    symbol_table.Root()->DeepFind(identifier);

if (!decl) {
  std::cout << "Symbol not found" << std::endl;
  return;
}

// Step 2: Collect all references
std::vector<verible::Location> references;

// The SymbolInfo contains reference information
const verilog::SymbolInfo& info = decl->Value();

// Traverse DependentReferences to find all uses
info.local_references_to_bind.components->Visit([&](const auto& ref) {
  if (ref.Value().resolved_symbol == decl) {
    // This reference points to our symbol
    verible::Location loc = GetLocation(ref.Value().identifier);
    references.push_back(loc);
  }
});

std::cout << "Found " << references.size() << " references" << std::endl;
```

### Example 3: Type Information Extraction

**Use Case:** Get type of a declared variable

```cpp
const verilog::SymbolTableNode* var = 
    symbol_table.Root()->Find("my_module")->Find("my_var");

if (var) {
  const verilog::SymbolInfo& info = var->Value();
  const verilog::DeclarationTypeInfo& type_info = info.declared_type;
  
  // Access type information
  std::cout << "Type: ";
  if (type_info.syntax_origin) {
    // Print the type as it appears in source
    std::cout << verible::StringSpanOfSymbol(*type_info.syntax_origin);
  }
  
  // Check direction (for ports)
  if (!type_info.direction.empty()) {
    std::cout << "Direction: " << type_info.direction << std::endl;
  }
}
```

---

## 📖 Part 2: Creating Semantic Linter Rules

### Example 4: Simple Semantic Check

**Use Case:** Warn if a parameter is not used

```cpp
// File: unused-parameter-rule.h
#ifndef VERIBLE_VERILOG_ANALYSIS_CHECKERS_UNUSED_PARAMETER_RULE_H_
#define VERIBLE_VERILOG_ANALYSIS_CHECKERS_UNUSED_PARAMETER_RULE_H_

#include "verible/common/analysis/lint-rule.h"
#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

class UnusedParameterRule : public verible::LintRule {
 public:
  using rule_type = verible::AnalysisPhaseRule;
  
  static const LintRuleDescriptor& GetDescriptor();
  
  // Called after symbol table is built
  void Lint(const verilog::SymbolTable& symbol_table,
            std::vector<LintViolation>* violations);
  
 private:
  void CheckModule(const SymbolTableNode& module,
                   std::vector<LintViolation>* violations);
  
  bool IsParameterUsed(const SymbolTableNode& param,
                       const SymbolTableNode& module);
};

}  // namespace analysis
}  // namespace verilog

#endif
```

```cpp
// File: unused-parameter-rule.cc
#include "unused-parameter-rule.h"

namespace verilog {
namespace analysis {

const LintRuleDescriptor& UnusedParameterRule::GetDescriptor() {
  static const LintRuleDescriptor d{
      .name = "unused-parameter",
      .topic = "parameters",
      .desc = "Checks that all parameters are used.",
  };
  return d;
}

void UnusedParameterRule::Lint(
    const verilog::SymbolTable& symbol_table,
    std::vector<LintViolation>* violations) {
  
  const SymbolTableNode* root = symbol_table.Root();
  
  // Check all modules
  for (const auto& [name, child] : root->Children()) {
    const SymbolInfo& info = child.Value();
    if (info.metatype == SymbolMetaType::kModule) {
      CheckModule(child, violations);
    }
  }
}

void UnusedParameterRule::CheckModule(
    const SymbolTableNode& module,
    std::vector<LintViolation>* violations) {
  
  // Find all parameters in this module
  for (const auto& [name, child] : module.Children()) {
    const SymbolInfo& info = child.Value();
    
    if (info.metatype == SymbolMetaType::kParameter) {
      // Check if parameter is used
      if (!IsParameterUsed(child, module)) {
        violations->push_back({
          .token = /* extract from syntax_origin */,
          .message = "Parameter '" + std::string(name) + "' is never used",
          .suggestion = "Remove unused parameter or prefix with _",
        });
      }
    }
  }
}

bool UnusedParameterRule::IsParameterUsed(
    const SymbolTableNode& param,
    const SymbolTableNode& module) {
  
  // Check if there are any references to this parameter
  // This is a simplified check - real implementation would traverse
  // all expressions in the module looking for references
  
  const SymbolInfo& param_info = param.Value();
  
  // Check assignments (if parameter is assigned, it's used)
  if (!param_info.assignments_defs.empty()) {
    return true;
  }
  
  // Check if any other symbol references this parameter
  for (const auto& [name, child] : module.Children()) {
    const SymbolInfo& info = child.Value();
    
    // Check if this symbol references our parameter
    // (simplified - real code would use reference resolution)
    // ...
  }
  
  return false;
}

}  // namespace analysis
}  // namespace verilog
```

**Key Points:**
1. Inherit from `LintRule`
2. Use `AnalysisPhaseRule` to get symbol table
3. Traverse symbol table hierarchically
4. Check semantic properties
5. Report violations with helpful messages

### Example 5: Type-Based Semantic Check

**Use Case:** Check that assignments are type-compatible

```cpp
class AssignmentTypeRule : public verible::LintRule {
 public:
  void Lint(const verilog::SymbolTable& symbol_table,
            const verible::ConcreteSyntaxTree& cst,
            std::vector<LintViolation>* violations) {
    
    // Find all assignments in CST
    FindAllAssignments(cst, [&](const verible::SyntaxTreeNode& assignment) {
      // Extract LHS and RHS
      const verible::Symbol* lhs = GetLHS(assignment);
      const verible::Symbol* rhs = GetRHS(assignment);
      
      // Get types from symbol table
      const Type* lhs_type = InferType(lhs, symbol_table);
      const Type* rhs_type = InferType(rhs, symbol_table);
      
      // Check compatibility
      if (lhs_type && rhs_type && 
          !lhs_type->IsAssignableFrom(*rhs_type)) {
        violations->push_back({
          .token = GetToken(assignment),
          .message = "Type mismatch in assignment: " +
                     lhs_type->ToString() + " = " + rhs_type->ToString(),
          .suggestion = "Check types or add explicit cast",
        });
      }
    });
  }
  
 private:
  const Type* InferType(const verible::Symbol* expr,
                        const SymbolTable& symbols) {
    // Type inference logic here
    // (This is where TypeInference API would be used)
    return nullptr;  // simplified
  }
};
```

---

## 📖 Part 3: Extending LSP Features

### Example 6: Adding Hover Information

**Use Case:** Show type information on hover

```cpp
// File: custom-hover-builder.h
#include "verible/verilog/tools/ls/hover.h"
#include "verible/verilog/analysis/symbol-table.h"

class CustomHoverBuilder {
 public:
  CustomHoverBuilder(SymbolTableHandler* handler)
      : symbol_table_handler_(handler) {}
  
  // Build hover information for identifier at position
  std::optional<verible::lsp::Hover> BuildHover(
      const verible::lsp::TextDocumentPositionParams& params,
      const BufferTrackerContainer& buffers) {
    
    // Step 1: Find symbol at cursor
    std::string_view identifier = GetIdentifierAt(params, buffers);
    if (identifier.empty()) return std::nullopt;
    
    // Step 2: Find definition in symbol table
    const SymbolTableNode* def = 
        symbol_table_handler_->FindDefinitionNode(identifier);
    if (!def) return std::nullopt;
    
    // Step 3: Extract information
    const SymbolInfo& info = def->Value();
    
    // Step 4: Build hover content
    std::string content;
    
    // Add type information
    if (info.declared_type.syntax_origin) {
      content += "Type: ";
      content += ExtractTypeString(info.declared_type);
      content += "\n";
    }
    
    // Add declaration location
    content += "Declared at: ";
    content += GetLocationString(info.syntax_origin);
    content += "\n";
    
    // Add semantic information
    content += "Kind: " + SymbolMetaTypeAsString(info.metatype) + "\n";
    
    // Optional: Add usage count
    int ref_count = CountReferences(identifier);
    content += "References: " + std::to_string(ref_count) + "\n";
    
    return verible::lsp::Hover{
      .contents = {.value = content, .kind = "markdown"},
      .range = GetRangeAt(params, buffers),
    };
  }
  
 private:
  SymbolTableHandler* symbol_table_handler_;
  
  int CountReferences(std::string_view identifier) {
    // Use FindReferencesLocations from SymbolTableHandler
    // ...
    return 0;  // simplified
  }
};
```

### Example 7: Custom Semantic Code Action

**Use Case:** "Remove unused variable" code action

```cpp
class UnusedVariableCodeAction {
 public:
  std::vector<verible::lsp::CodeAction> GetCodeActions(
      const verible::lsp::CodeActionParams& params,
      const SymbolTable& symbol_table,
      const BufferTrackerContainer& buffers) {
    
    std::vector<verible::lsp::CodeAction> actions;
    
    // Find symbol at cursor
    std::string_view identifier = GetIdentifierAt(params, buffers);
    const SymbolTableNode* symbol = 
        symbol_table.Root()->DeepFind(identifier);
    
    if (!symbol) return actions;
    
    const SymbolInfo& info = symbol->Value();
    
    // Check if variable is unused
    if (info.metatype == SymbolMetaType::kDataNetVariableInstance &&
        !IsUsed(*symbol, symbol_table)) {
      
      // Create "Remove unused variable" action
      verible::lsp::CodeAction action;
      action.title = "Remove unused variable '" + 
                     std::string(identifier) + "'";
      action.kind = "quickfix";
      
      // Create edit to remove declaration
      verible::lsp::WorkspaceEdit edit;
      edit.changes[params.textDocument.uri] = {
        {
          .range = GetDeclarationRange(info.syntax_origin),
          .newText = "",  // Delete
        }
      };
      action.edit = edit;
      
      actions.push_back(action);
    }
    
    return actions;
  }
  
 private:
  bool IsUsed(const SymbolTableNode& symbol,
              const SymbolTable& table) {
    // Check if symbol has any references
    // (Use reference resolution results)
    return false;  // simplified
  }
};
```

---

## 📖 Part 4: Building Analysis Tools

### Example 8: Call Graph Builder

**Use Case:** Build function call graph for analysis

```cpp
class CallGraphBuilder {
 public:
  struct CallNode {
    const SymbolTableNode* function;
    std::vector<CallNode*> callees;
    std::vector<CallNode*> callers;
  };
  
  // Build call graph from symbol table
  std::map<const SymbolTableNode*, CallNode> Build(
      const SymbolTable& symbol_table) {
    
    std::map<const SymbolTableNode*, CallNode> graph;
    
    // Step 1: Find all functions/tasks
    std::vector<const SymbolTableNode*> functions;
    CollectFunctions(symbol_table.Root(), &functions);
    
    // Step 2: For each function, find what it calls
    for (const SymbolTableNode* func : functions) {
      CallNode& node = graph[func];
      node.function = func;
      
      // Analyze function body to find calls
      const SymbolInfo& info = func->Value();
      if (info.syntax_origin) {
        ExtractCalls(*info.syntax_origin, symbol_table, &node.callees);
      }
    }
    
    // Step 3: Build reverse edges (callers)
    for (auto& [func, node] : graph) {
      for (CallNode* callee : node.callees) {
        callee->callers.push_back(&node);
      }
    }
    
    return graph;
  }
  
  // Find unreachable functions
  std::vector<const SymbolTableNode*> FindUnreachable(
      const std::map<const SymbolTableNode*, CallNode>& graph,
      const std::vector<const SymbolTableNode*>& entry_points) {
    
    std::set<const SymbolTableNode*> reachable;
    
    // BFS from entry points
    std::queue<const SymbolTableNode*> queue;
    for (const SymbolTableNode* entry : entry_points) {
      queue.push(entry);
      reachable.insert(entry);
    }
    
    while (!queue.empty()) {
      const SymbolTableNode* func = queue.front();
      queue.pop();
      
      const CallNode& node = graph.at(func);
      for (CallNode* callee : node.callees) {
        if (reachable.insert(callee->function).second) {
          queue.push(callee->function);
        }
      }
    }
    
    // Find unreachable
    std::vector<const SymbolTableNode*> unreachable;
    for (const auto& [func, node] : graph) {
      if (reachable.find(func) == reachable.end()) {
        unreachable.push_back(func);
      }
    }
    
    return unreachable;
  }
  
 private:
  void CollectFunctions(const SymbolTableNode* node,
                        std::vector<const SymbolTableNode*>* functions) {
    const SymbolInfo& info = node->Value();
    if (info.metatype == SymbolMetaType::kFunction ||
        info.metatype == SymbolMetaType::kTask) {
      functions->push_back(node);
    }
    
    // Recurse into children
    for (const auto& [name, child] : node->Children()) {
      CollectFunctions(&child, functions);
    }
  }
  
  void ExtractCalls(const verible::Symbol& func_body,
                    const SymbolTable& symbol_table,
                    std::vector<CallNode*>* callees) {
    // Traverse AST to find function calls
    // Match against symbol table to resolve callees
    // (Simplified - real implementation would use CST traversal)
  }
};
```

### Example 9: Unused Symbol Detector

**Use Case:** Find all unused symbols in a project

```cpp
class UnusedDetector {
 public:
  struct UnusedSymbol {
    const SymbolTableNode* symbol;
    std::string name;
    SymbolMetaType type;
    verible::Location location;
    std::string suggestion;
  };
  
  std::vector<UnusedSymbol> FindUnused(const SymbolTable& symbol_table) {
    std::vector<UnusedSymbol> unused;
    
    // Step 1: Mark all externally visible symbols as used
    std::set<const SymbolTableNode*> used;
    MarkExternallyVisible(symbol_table.Root(), &used);
    
    // Step 2: Mark all referenced symbols as used
    MarkReferenced(symbol_table, &used);
    
    // Step 3: Find symbols that are not used
    CollectUnused(symbol_table.Root(), used, &unused);
    
    return unused;
  }
  
 private:
  void MarkExternallyVisible(const SymbolTableNode* node,
                              std::set<const SymbolTableNode*>* used) {
    const SymbolInfo& info = node->Value();
    
    // Modules, interfaces, packages are externally visible
    if (info.metatype == SymbolMetaType::kModule ||
        info.metatype == SymbolMetaType::kInterface ||
        info.metatype == SymbolMetaType::kPackage) {
      used->insert(node);
      
      // Output ports are used
      for (const auto& [name, child] : node->Children()) {
        const SymbolInfo& child_info = child.Value();
        if (child_info.declared_type.direction == "output" ||
            child_info.declared_type.direction == "inout") {
          used->insert(&child);
        }
      }
    }
    
    // Recurse
    for (const auto& [name, child] : node->Children()) {
      MarkExternallyVisible(&child, used);
    }
  }
  
  void MarkReferenced(const SymbolTable& symbol_table,
                      std::set<const SymbolTableNode*>* used) {
    // Traverse all DependentReferences
    // Mark resolved symbols as used
    // (Use reference resolution results from symbol table)
  }
  
  void CollectUnused(const SymbolTableNode* node,
                     const std::set<const SymbolTableNode*>& used,
                     std::vector<UnusedSymbol>* unused) {
    // If not in used set, it's unused
    if (used.find(node) == used.end()) {
      const SymbolInfo& info = node->Value();
      
      // Skip certain types (like modules - already checked)
      if (ShouldCheck(info.metatype)) {
        unused->push_back({
          .symbol = node,
          .name = std::string(node->Key()),
          .type = info.metatype,
          .location = GetLocation(info.syntax_origin),
          .suggestion = GenerateSuggestion(info.metatype),
        });
      }
    }
    
    // Recurse
    for (const auto& [name, child] : node->Children()) {
      CollectUnused(&child, used, unused);
    }
  }
  
  bool ShouldCheck(SymbolMetaType type) {
    // Check variables, parameters, functions
    return type == SymbolMetaType::kDataNetVariableInstance ||
           type == SymbolMetaType::kParameter ||
           type == SymbolMetaType::kFunction ||
           type == SymbolMetaType::kTask;
  }
  
  std::string GenerateSuggestion(SymbolMetaType type) {
    switch (type) {
      case SymbolMetaType::kDataNetVariableInstance:
        return "Remove unused variable or prefix with _";
      case SymbolMetaType::kParameter:
        return "Remove unused parameter";
      case SymbolMetaType::kFunction:
      case SymbolMetaType::kTask:
        return "Remove unused function/task or mark as unused";
      default:
        return "Consider removing";
    }
  }
};
```

---

## 📖 Part 5: Best Practices

### Integration Patterns

#### Pattern 1: Two-Phase Analysis
```cpp
// Phase 1: Build symbol table
SymbolTable symbol_table(&project);
symbol_table.Build();
symbol_table.Resolve();

// Phase 2: Your analysis
YourAnalyzer analyzer(&symbol_table);
auto results = analyzer.Analyze();
```

#### Pattern 2: CST + Symbol Table
```cpp
// Combine CST traversal with symbol table lookup
class CombinedAnalyzer : public verible::TreeVisitorRecursive {
 public:
  CombinedAnalyzer(const SymbolTable* symbols) : symbols_(symbols) {}
  
  void Visit(const verible::SyntaxTreeNode& node) override {
    // Check CST structure
    if (IsIdentifier(node)) {
      std::string_view name = GetIdentifierName(node);
      
      // Look up in symbol table for semantic info
      const SymbolTableNode* symbol = symbols_->Root()->DeepFind(name);
      if (symbol) {
        // Do semantic analysis
        AnalyzeSymbol(*symbol);
      }
    }
    
    TreeVisitorRecursive::Visit(node);
  }
  
 private:
  const SymbolTable* symbols_;
};
```

#### Pattern 3: Caching Results
```cpp
class CachedAnalyzer {
 public:
  const Type* GetType(const verible::Symbol* expr) {
    // Check cache first
    auto it = type_cache_.find(expr);
    if (it != type_cache_.end()) {
      return it->second;
    }
    
    // Compute and cache
    const Type* type = ComputeType(expr);
    type_cache_[expr] = type;
    return type;
  }
  
 private:
  std::map<const verible::Symbol*, const Type*> type_cache_;
};
```

### Error Handling

```cpp
// Always check status
absl::Status status = symbol_table.BuildSingleTranslationUnit(file, &errors);
if (!status.ok()) {
  std::cerr << "Build failed: " << status.message() << std::endl;
  return;
}

// Check resolution errors
symbol_table.Resolve(&resolve_errors);
for (const auto& error : resolve_errors) {
  if (!error.ok()) {
    std::cerr << "Resolution error: " << error.message() << std::endl;
  }
}
```

### Performance Tips

1. **Cache symbol table lookups**
   ```cpp
   std::map<std::string_view, const SymbolTableNode*> lookup_cache;
   ```

2. **Avoid repeated CST traversals**
   ```cpp
   // Collect all info in one pass
   CollectAllInfo(cst);
   // Then analyze
   AnalyzeInfo();
   ```

3. **Use const references**
   ```cpp
   void Analyze(const SymbolTable& symbols);  // Good
   void Analyze(SymbolTable symbols);         // Bad (copy)
   ```

---

## ✅ Integration Checklist

When building a new semantic analysis tool:

- [ ] Understand the symbol table structure
- [ ] Check what existing rules do similar things
- [ ] Use SymbolMetaType to filter symbols
- [ ] Handle reference resolution correctly
- [ ] Cache expensive computations
- [ ] Test on real SystemVerilog files
- [ ] Handle edge cases (generate blocks, packages, etc.)
- [ ] Provide actionable error messages
- [ ] Document your tool's assumptions
- [ ] Add comprehensive tests

---

## 📚 Additional Resources

- **EXISTING_SYMBOL_TABLE_GUIDE.md** - Symbol table deep dive
- **EXISTING_SEMANTIC_ANALYSIS_SURVEY.md** - What exists now
- **verible/verilog/analysis/checkers/** - 60+ example rules
- **verible/verilog/tools/ls/** - LSP integration examples

---

## ✅ Summary

This guide showed you how to:
- ✅ Use the symbol table for semantic queries
- ✅ Create new linter rules with semantic checks
- ✅ Extend LSP with custom semantic features
- ✅ Build analysis tools (call graph, unused detection)
- ✅ Follow best practices and patterns

**You now have everything you need to build semantic analysis tools on Verible!**

---

**Week 2 Day 3: Integration guide complete!** ✅

**Next:** Day 4 - Enhancement demonstrations & proof of concept

