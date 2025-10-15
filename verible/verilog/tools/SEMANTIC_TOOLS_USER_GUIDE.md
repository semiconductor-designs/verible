# Verible Semantic Analysis Tools - User Guide 📚

**Version**: Phase 5 - v3.6.0-beta
**Status**: Production-ready beta tools for SystemVerilog analysis

---

## 🎯 Overview

Verible provides 5 powerful semantic analysis tools for SystemVerilog code:

1. **Symbol Renamer** - Safe, scope-aware renaming
2. **Dead Code Eliminator** - Find and remove unused code
3. **Complexity Analyzer** - Measure code complexity metrics
4. **VeriPG Validator** - Validate VeriPG requirements
5. **Refactoring Engine** - Automated code transformations

All tools:
- ✅ Work on real SystemVerilog code
- ✅ Preserve syntax correctness
- ✅ Provide detailed reports
- ✅ Support batch operations

---

## 🛠️ Tool 1: Symbol Renamer

### What It Does
Safely renames symbols (functions, tasks, variables) across their entire scope, finding all references automatically.

### When to Use
- Refactoring code for better naming
- Following new naming conventions
- Making code more readable

### Example Usage

```systemverilog
// Before
module test;
  logic tmp;
  function void f();
    tmp = 1;
  endfunction
endmodule

// Rename "tmp" → "counter"
// After
module test;
  logic counter;
  function void f();
    counter = 1;
  endfunction
endmodule
```

### API Usage

```cpp
#include "verible/verilog/tools/rename/symbol-renamer.h"

// Parse file and build symbol table
VerilogProject project(".", {});
project.OpenTranslationUnit("my_file.sv");
SymbolTable symbol_table(&project);
symbol_table.Build();

// Create renamer
SymbolRenamer renamer(&symbol_table);

// Find all references to a symbol
auto refs = renamer.FindReferences("old_name");
std::cout << "Found " << refs.size() << " references\n";

// Validate rename is safe
auto status = renamer.ValidateRename("old_name", "new_name");
if (!status.ok()) {
  std::cerr << "Rename not safe: " << status.message() << "\n";
  return;
}

// Perform rename
status = renamer.Rename("old_name", "new_name");
if (status.ok()) {
  std::cout << "Rename successful!\n";
}
```

### Limitations
- Renames within scope only (doesn't cross module boundaries)
- Requires valid syntax (won't work on broken code)

---

## 🧹 Tool 2: Dead Code Eliminator

### What It Does
Finds functions, tasks, and variables that are never used, helping clean up codebases.

### When to Use
- Code cleanup after refactoring
- Finding forgotten test code
- Reducing codebase size
- Improving maintainability

### Example Usage

```systemverilog
// Input code
module test;
  initial begin
    used_function();
  end
  
  function void used_function();
    // Called from initial
  endfunction
  
  function void unused_function();
    // NEVER called - dead code!
  endfunction
endmodule
```

### API Usage

```cpp
#include "verible/verilog/tools/deadcode/dead-code-eliminator.h"
#include "verible/verilog/analysis/call-graph.h"

// Build call graph
CallGraph call_graph(&symbol_table);
call_graph.Build();

// Create eliminator
DeadCodeEliminator eliminator(&call_graph, &symbol_table);

// Find dead code
auto report = eliminator.FindDeadCode();

std::cout << "Dead code found:\n";
std::cout << "  Functions: " << report.dead_functions.size() << "\n";
std::cout << "  Tasks: " << report.dead_tasks.size() << "\n";
std::cout << "  Variables: " << report.dead_variables.size() << "\n";

// Print details
for (const auto& func : report.dead_functions) {
  std::cout << "  - " << func << "\n";
}

// Optional: Actually remove the dead code
auto status = eliminator.Eliminate();
if (status.ok()) {
  std::cout << "Dead code removed!\n";
}
```

### Report Format

```cpp
struct DeadCodeReport {
  std::set<std::string> dead_functions;
  std::set<std::string> dead_tasks;
  std::set<std::string> dead_variables;
  int total_dead_count;
  std::string summary;
};
```

### Limitations
- Conservative: Won't remove code if uncertain
- No false positives (tested extensively)
- Doesn't detect dead code in external modules

---

## 📊 Tool 3: Complexity Analyzer

### What It Does
Calculates code complexity metrics (cyclomatic complexity, LOC, fan-in/out) to identify complex functions that need refactoring.

### When to Use
- Code review (flag complex functions)
- Technical debt tracking
- Identifying refactoring candidates
- Setting complexity budgets

### Example Usage

```systemverilog
// Example function
function automatic logic [7:0] complex_logic(logic [7:0] a, b, c);
  if (a > b) begin
    if (b > c) begin
      return a;
    end else begin
      return c;
    end
  end else begin
    return b;
  end
endfunction
// Cyclomatic Complexity: 3
// Lines of Code: 9
```

### API Usage

```cpp
#include "verible/verilog/tools/complexity/complexity-analyzer.h"

CallGraph call_graph(&symbol_table);
call_graph.Build();

ComplexityAnalyzer analyzer(&call_graph, &symbol_table);
auto report = analyzer.Analyze();

// Per-function metrics
for (const auto& [name, func] : report.per_function) {
  std::cout << "Function: " << name << "\n";
  std::cout << "  Cyclomatic Complexity: " << func.cyclomatic_complexity << "\n";
  std::cout << "  Function Size (LOC): " << func.function_size << "\n";
  std::cout << "  Fan-in: " << func.fan_in << "\n";
  std::cout << "  Fan-out: " << func.fan_out << "\n";
  std::cout << "  Call Depth: " << func.call_depth << "\n";
}

// Summary statistics
std::cout << "\nSummary:\n";
std::cout << "  Total Functions: " << report.summary.total_functions << "\n";
std::cout << "  Average Complexity: " << report.summary.average_complexity << "\n";
std::cout << "  Max Complexity: " << report.summary.max_complexity << "\n";
```

### Metrics Explained

**Cyclomatic Complexity (CC)**:
- Number of decision points + 1
- CC 1-5: Simple, easy to maintain
- CC 6-10: Moderate complexity
- CC 11+: High complexity, consider refactoring

**Function Size (LOC)**:
- Lines of code in function body
- < 50: Good
- 50-100: Acceptable
- \> 100: Consider breaking up

**Fan-in / Fan-out**:
- Fan-in: How many functions call this one
- Fan-out: How many functions this one calls
- High fan-in: Central function, test well
- High fan-out: Complex dependencies

**Call Depth**:
- Maximum call chain length from this function
- High depth: Hard to trace execution

---

## ✅ Tool 4: VeriPG Validator

### What It Does
Validates SystemVerilog code against VeriPG requirements and best practices.

### When to Use
- Pre-commit checks
- CI/CD validation
- Ensuring code quality standards
- VeriPG compliance

### Example Usage

```cpp
#include "verible/verilog/tools/validator/veripg-validator.h"

VeriPGValidator validator(&symbol_table);

// Run all validations
auto report = validator.Validate();

if (report.is_valid) {
  std::cout << "✅ All validations passed!\n";
} else {
  std::cout << "❌ Validation failures:\n";
  for (const auto& violation : report.violations) {
    std::cout << "  " << violation.file << ":" << violation.line 
              << " - " << violation.message << "\n";
  }
}

// Run specific validations
auto type_report = validator.ValidateTypes();
auto naming_report = validator.ValidateNamingConventions();
auto structure_report = validator.ValidateModuleStructure();
```

### Validation Categories

1. **Type Validation**:
   - Correct type usage
   - No implicit conversions
   - Width mismatches

2. **Naming Conventions**:
   - Function names: snake_case
   - Module names: PascalCase
   - Constants: UPPER_CASE

3. **Module Structure**:
   - Proper port declarations
   - No dangling signals
   - Correct instantiation

---

## 🔧 Tool 5: Refactoring Engine

### What It Does
Automated code transformations: extract variables/functions, inline code, move declarations.

### When to Use
- Cleaning up messy code
- Breaking up large functions
- Improving readability
- Reducing duplication

### Operations

#### 1. Extract Variable

```systemverilog
// Before
result = (a + b) * (c + d);

// After
logic temp_sum1 = a + b;
logic temp_sum2 = c + d;
result = temp_sum1 * temp_sum2;
```

**API**:
```cpp
RefactoringEngine engine(&symbol_table, &type_inference, &project);

Selection sel;
sel.filename = "test.sv";
sel.start_line = 5;
sel.start_column = 10;
sel.end_line = 5;
sel.end_column = 20;

auto status = engine.ExtractVariable(sel, "temp_sum");
```

#### 2. Extract Function

```systemverilog
// Before
initial begin
  a = 1;
  b = 2;
  c = a + b;
end

// After
initial begin
  initialize_values();
end

function void initialize_values();
  a = 1;
  b = 2;
  c = a + b;
endfunction
```

**API**:
```cpp
Selection sel = {...};  // Select the code block
auto status = engine.ExtractFunction(sel, "initialize_values");
```

#### 3. Inline Function

```systemverilog
// Before
function int add(int a, b);
  return a + b;
endfunction
result = add(5, 10);

// After  
result = 5 + 10;
```

**API**:
```cpp
Location loc;
loc.filename = "test.sv";
loc.line = 10;  // Line with function call
loc.column = 5;

auto status = engine.InlineFunction(loc);
```

#### 4. Move Declaration

```systemverilog
// Before
logic a;
logic b;
logic c;

// After (move b closer to usage)
logic a;
logic c;
logic b;
```

**API**:
```cpp
Location loc = {...};  // Location of declaration
auto status = engine.MoveDeclaration(loc);
```

### Safety Features

All refactoring operations:
- ✅ Validate syntax before/after
- ✅ Create backup files (`.bak`)
- ✅ Return errors instead of corrupting code
- ✅ Preserve semantic meaning

---

## 🚀 Best Practices

### 1. Always Check Status

```cpp
auto status = tool.Operation();
if (!status.ok()) {
  std::cerr << "Error: " << status.message() << "\n";
  // Handle error
}
```

### 2. Build Symbol Table First

```cpp
// Always do this first
SymbolTable symbol_table(&project);
std::vector<absl::Status> diagnostics;
symbol_table.Build(&diagnostics);

if (!diagnostics.empty()) {
  // Handle build errors
}
```

### 3. Use Dry-Run for Refactoring

```cpp
// Check what would change before actually doing it
auto preview = engine.PreviewRefactoring(operation);
std::cout << "Would change " << preview.affected_files.size() << " files\n";
```

### 4. Validate Before Committing

```cpp
// Always validate after modifications
VeriPGValidator validator(&symbol_table);
auto report = validator.Validate();
if (!report.is_valid) {
  // Revert or fix issues
}
```

---

## ⚠️ Known Limitations

### All Tools
- Require valid syntax (won't work on broken code)
- Work on parsed files only (need VerilogProject)
- Single-file modifications (no cross-file refactoring yet)

### Symbol Renamer
- Scope-local only (doesn't cross module boundaries)
- Doesn't handle macros

### Dead Code Eliminator
- Conservative (no false positives, but may miss some dead code)
- Doesn't detect unused external module ports

### Complexity Analyzer
- Cyclomatic complexity for procedural code only
- Doesn't measure RTL complexity (gate count, etc.)

### Refactoring Engine
- Basic operations only (no advanced transformations)
- May need manual cleanup for complex cases
- Requires `VerilogProject` for file access

---

## 🎓 Tutorials

### Tutorial 1: Clean Up a Module (15 minutes)

1. **Find dead code**:
   ```cpp
   DeadCodeEliminator eliminator(&call_graph, &symbol_table);
   auto dead_code = eliminator.FindDeadCode();
   ```

2. **Check complexity**:
   ```cpp
   ComplexityAnalyzer analyzer(&call_graph, &symbol_table);
   auto report = analyzer.Analyze();
   // Flag functions with CC > 10
   ```

3. **Refactor complex functions**:
   ```cpp
   RefactoringEngine engine(&symbol_table, &type_inference, &project);
   // Extract variables/functions to simplify
   ```

4. **Validate result**:
   ```cpp
   VeriPGValidator validator(&symbol_table);
   auto valid = validator.Validate();
   ```

### Tutorial 2: Rename for Consistency (10 minutes)

1. **Check current naming**:
   ```cpp
   // Find all symbols
   auto symbols = symbol_table.GetAllSymbols();
   ```

2. **Rename to convention**:
   ```cpp
   SymbolRenamer renamer(&symbol_table);
   renamer.Rename("oldName", "new_name");  // snake_case
   ```

3. **Validate**:
   ```cpp
   VeriPGValidator validator(&symbol_table);
   auto naming_ok = validator.ValidateNamingConventions();
   ```

---

## 📞 Support

### Reporting Issues
- File bugs on GitHub: https://github.com/chipsalliance/verible
- Include: Verible version, input code, error message

### Getting Help
- Documentation: https://chipsalliance.github.io/verible/
- Discussions: GitHub Discussions
- Stack Overflow: Tag `verible`

---

## 🎯 Summary

Verible's semantic tools provide:
- ✅ **Safe refactoring** with syntax preservation
- ✅ **Dead code detection** for cleaner codebases
- ✅ **Complexity metrics** for better code quality
- ✅ **Automated validation** for VeriPG compliance
- ✅ **Production-ready** with comprehensive testing

**Start using them today to improve your SystemVerilog code quality!** 🚀

