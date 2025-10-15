# Existing Symbol Table - Practical Usage Guide

**Date:** 2025-10-15  
**Purpose:** Understand and leverage Verible's existing 2,937-line symbol table  
**Status:** Week 1 Day 1 - Deep Dive

---

## 🏗️ Architecture Overview

### Core Components

```
VerilogProject
    ↓
VerilogSourceFile (owns text memory)
    ↓
ConcreteSyntaxTree (CST)
    ↓
SymbolTableBuilder (visitor pattern)
    ↓
SymbolTableNode (tree structure)
    ↓
SymbolInfo (metadata)
```

---

## 📊 Key Data Structures

### 1. SymbolTableNode
**Definition:**
```cpp
using SymbolTableNode =
    verible::MapTree<std::string_view, SymbolInfo, verible::StringViewCompare>;
```

**Purpose:** Tree-based structure representing hierarchical symbol scopes

**Key Features:**
- Keys are `string_view` (memory owned by source file)
- Values are `SymbolInfo` (metadata about symbols)
- Hierarchical: nodes can have child nodes (nested scopes)

### 2. SymbolMetaType (enum)
**Supported Types:**
```cpp
enum class SymbolMetaType {
  kRoot,
  kClass,
  kModule,
  kGenerate,
  kPackage,
  kParameter,
  kTypeAlias,         // typedef
  kDataNetVariableInstance,
  kFunction,          // includes constructors
  kTask,
  kStruct,
  kEnumType,
  kEnumConstant,
  kInterface,
  // Meta-categories:
  kUnspecified,       // any type
  kCallable,          // function or task
};
```

**Coverage:** All major SystemVerilog constructs! ✅

### 3. ReferenceType (enum)
**How identifiers are referenced:**
```cpp
enum class ReferenceType {
  kUnqualified,           // x (search up-scope)
  kImmediate,             // base in "base::member" (local only)
  kDirectMember,          // ::id (package/class static)
  kMemberOfTypeOfParent,  // .id (struct/class member)
};
```

**Purpose:** Guides reference resolution strategy

### 4. ReferenceComponent
**What:** Single identifier in a reference chain (e.g., "a" in "a.b.c")

**Key Fields:**
```cpp
struct ReferenceComponent {
  const std::string_view identifier;     // The name
  const ReferenceType ref_type;          // How to resolve
  const SymbolMetaType required_metatype;// Expected type
  const SymbolTableNode *resolved_symbol;// Result (after resolution)
};
```

### 5. DependentReferences
**What:** Complete reference chain (e.g., "a.b.c" or "x::y::z")

**Structure:**
```cpp
struct DependentReferences {
  std::unique_ptr<ReferenceComponentNode> components;  // Tree of refs
  
  // Resolution methods:
  void Resolve(const SymbolTableNode &context, ...);
  void ResolveLocally(const SymbolTableNode &context);
  absl::StatusOr<SymbolTableNode*> ResolveOnlyBaseLocally(...);
};
```

**Purpose:** Handles hierarchical and qualified references

### 6. SymbolInfo
**Metadata about each symbol:**
```cpp
struct SymbolInfo {
  SymbolMetaType metatype;               // What kind of symbol
  const verible::Symbol *syntax_origin;  // CST node
  DeclarationTypeInfo declared_type;     // Type information
  DependentReferences local_references_to_bind;  // Refs to resolve
  std::vector<const verible::Symbol*> assignments_defs;  // Where assigned
  // ... more fields
};
```

---

## 🔍 How Reference Resolution Works

### Example: Resolving "a.b.c"

1. **Build Reference Chain:**
   ```
   a (kUnqualified)
     ↓
   b (kMemberOfTypeOfParent)
     ↓
   c (kMemberOfTypeOfParent)
   ```

2. **Resolution Process:**
   ```cpp
   // Step 1: Resolve 'a' in current scope (search up if needed)
   SymbolTableNode* a_node = ResolveInCurrentScope("a");
   
   // Step 2: Get type of 'a'
   Type* a_type = GetTypeOf(a_node);
   
   // Step 3: Resolve 'b' in 'a's type scope
   SymbolTableNode* b_node = ResolveInTypeScope(a_type, "b");
   
   // Step 4: Get type of 'b'
   Type* b_type = GetTypeOf(b_node);
   
   // Step 5: Resolve 'c' in 'b's type scope
   SymbolTableNode* c_node = ResolveInTypeScope(b_type, "c");
   ```

3. **Result:**
   - Each `ReferenceComponent::resolved_symbol` points to declaration
   - Can traverse resolved chain to get full context

---

## 🚀 Current Capabilities

### ✅ What Already Works

1. **Symbol Collection:**
   - Automatically extracts all symbols from CST
   - Builds hierarchical scope tree
   - Tracks symbol locations (for go-to-definition)

2. **Reference Tracking:**
   - Identifies all identifier uses
   - Categorizes reference types
   - Builds dependency trees

3. **Scope Management:**
   - Module hierarchy
   - Class scopes
   - Package imports
   - Generate blocks
   - Function/task local scopes

4. **Symbol Lookup:**
   - Up-scope search for unqualified names
   - Qualified name resolution (::, .)
   - Type-based member lookup

5. **Type Information:**
   - `DeclarationTypeInfo` tracks declared types
   - Direction info (input/output/inout)
   - Type specifications for ports

---

## ⚠️ What Needs Enhancement

### Gap 1: Type Inference
**Current:** Type info attached to declarations  
**Missing:** Infer types of expressions, function return values, etc.

**Example:**
```systemverilog
logic [7:0] a, b;
logic [15:0] result;
result = a + b;  // Need to infer: result of (a+b) is [15:0]
```

### Gap 2: Type Compatibility Checking
**Current:** Basic type tracking  
**Missing:** Deep type compatibility rules

**Example:**
```systemverilog
logic [7:0] a;
logic [15:0] b;
a = b;  // Need to check: assignment width mismatch warning
```

### Gap 3: Unused Symbol Detection
**Current:** Reference tracking exists  
**Missing:** Analysis to find unused symbols

**What Exists:**
- `SymbolInfo::assignments_defs` tracks assignments
- Reference resolution tracks uses

**What's Needed:**
- Mark symbols as "used" when referenced
- Report symbols never referenced
- Handle special cases (ports, exports)

### Gap 4: Call Graph
**Current:** Function/task symbols collected  
**Missing:** Who-calls-who relationships

**What's Needed:**
- Extract function/task calls from expressions
- Build caller → callee graph
- Detect recursion, unreachable functions

---

## 🔧 Extension Strategy

### Week 2: Type System Enhancement

**Approach:** Add layer on top of existing symbol table

**New Components:**
```cpp
// New file: verible/verilog/analysis/type-inference.h
class TypeInference {
 public:
  // Infer type of any expression using symbol table
  const Type* InferExpressionType(
      const verible::Symbol& expr,
      const SymbolTableNode& context);
  
 private:
  const SymbolTable* symbols_;
  TypeRegistry* types_;
};

// New file: verible/verilog/analysis/type-checker.h
class TypeChecker {
 public:
  std::vector<TypeError> CheckAssignmentCompatibility(
      const SymbolTable& symbols);
  
 private:
  TypeInference* inference_;
};
```

**Integration Point:** Use existing `SymbolInfo::declared_type`

### Week 3: Unused Detection

**Approach:** Post-process existing symbol table

**New Component:**
```cpp
// New file: verible/verilog/analysis/unused-detector.h
class UnusedDetector {
 public:
  struct UnusedSymbol {
    const SymbolTableNode* symbol;
    std::string suggestion;
  };
  
  std::vector<UnusedSymbol> FindUnused(const SymbolTable& symbols);
  
 private:
  bool IsUsed(const SymbolTableNode& symbol);
  bool IsExternallyVisible(const SymbolTableNode& symbol);
};
```

**Integration Point:** Use `DependentReferences::resolved_symbol` to track uses

### Week 4: Call Graph

**Approach:** Extract from expression analysis

**New Component:**
```cpp
// New file: verible/verilog/analysis/call-graph.h
class CallGraphBuilder {
 public:
  CallGraph Build(const SymbolTable& symbols);
  
 private:
  void ExtractCallsFromFunction(const SymbolTableNode& func);
  std::map<const SymbolTableNode*, std::vector<const SymbolTableNode*>> edges_;
};
```

**Integration Point:** Use symbol table to find function/task symbols, analyze their bodies

---

## 📝 Example Usage (Existing Code)

### Building Symbol Table
```cpp
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

// Parse file
VerilogProject project;
auto file = project.OpenFile("module.sv");

// Build symbol table
const SymbolTableNode* symbols = project.BuildSymbolTable();

// Access symbols
for (const auto& [name, info] : symbols->Children()) {
  std::cout << "Symbol: " << name 
            << " Type: " << info.metatype << std::endl;
}
```

### Resolving References
```cpp
// After building symbol table
for (const auto& [name, info] : symbols->Children()) {
  // Resolve all references in this symbol
  std::vector<absl::Status> diagnostics;
  info.local_references_to_bind.Resolve(*symbols, &diagnostics);
  
  // Check resolution status
  for (const auto& diag : diagnostics) {
    if (!diag.ok()) {
      std::cerr << "Unresolved: " << diag.message() << std::endl;
    }
  }
}
```

---

## ✅ Action Items for Week 1

### Day 1-2: Understanding (CURRENT)
- [x] Read symbol-table.h (550 lines)
- [ ] Read symbol-table.cc key functions
- [ ] Find usage examples in codebase
- [ ] Document capabilities (THIS FILE)

### Day 3: Practical Examples
- [ ] Create simple test: parse → build symbol table → print
- [ ] Test reference resolution
- [ ] Understand extension points

### Day 4-5: Enhancement Plan
- [ ] Design type inference API
- [ ] Design unused detector API
- [ ] Design call graph API
- [ ] Update 4-week plan with specifics

---

## 🎯 Key Insights

1. **Don't Reinvent:** 2,937 lines of production code already exists
2. **Build On Top:** Add analysis layers, don't modify core
3. **Leverage References:** `DependentReferences` already tracks uses
4. **Use CST Origin:** Every symbol links back to syntax tree
5. **Extend, Don't Replace:** Keep existing architecture

---

## 🚀 Next Steps

**Immediate:**
1. Find example usage in Verible codebase (LSP, linter)
2. Create minimal working example
3. Test symbol table building on simple SV file

**This Week:**
- Complete understanding of existing code
- Design enhancement APIs
- Write detailed Week 2-4 implementation plan

**Status:** Day 1 in progress, on track for 4-week delivery ✅

