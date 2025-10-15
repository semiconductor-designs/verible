# Phase 5: TRUE 100% Completion Plan

## Current Reality
- ✅ Framework: 100% complete
- ⚠️ Functional: 40% complete  
- ❌ Plan Compliance: 60%

## Goal: Achieve TRUE 100%

**Remaining Work**: 12-17 hours
**Approach**: No compromises, full implementation
**Order**: Follow plan specification

---

## Implementation Tasks

### Task 1: Tool 2 - Dead Code Eliminator (2-3 hours)
**Priority**: HIGH
**Status**: Framework only → Need actual CST removal

**What's needed:**
```cpp
// Current: Just returns OK
absl::Status Eliminate(...) {
  return absl::OkStatus(); // ❌
}

// Need: Actual code removal
absl::Status Eliminate(...) {
  for (const auto& func_name : report.dead_functions) {
    // 1. Find function definition in CST via symbol table
    auto* node = symbol_table_->Root().Find(func_name);
    
    // 2. Get CST node containing the function
    const verible::Symbol* cst_node = node->Value().syntax_origin;
    
    // 3. Calculate text range from CST
    auto range = verible::StringSpanOfSymbol(*cst_node, base);
    
    // 4. Remove from source text
    content.erase(range.begin(), range.length());
    
    // 5. Write back with backup
    CreateBackup(filename);
    WriteFile(filename, content);
  }
}
```

**Subtasks:**
1. Add method to find function CST node via symbol table
2. Calculate byte range from CST node  
3. Implement text removal with proper offset handling
4. Add backup creation
5. Write modified files
6. Update tests to verify actual removal

---

### Task 2: Tool 3 - Complexity Analyzer (1-2 hours)
**Priority**: MEDIUM (read-only, easier)
**Status**: CallGraph-based → Need actual CST counting

**What's needed:**
```cpp
// Current: Hardcoded
func_metrics.cyclomatic_complexity = 1; // ❌

// Need: Actual CST traversal
int CountDecisionPoints(const verible::Symbol& func_cst) {
  int decisions = 0;
  
  // Traverse CST recursively
  for (const auto& child : func_cst.children()) {
    if (IsIfStatement(child) || 
        IsCaseStatement(child) ||
        IsForLoop(child) ||
        IsWhileLoop(child)) {
      decisions++;
    }
    decisions += CountDecisionPoints(child); // Recurse
  }
  
  return decisions;
}

func_metrics.cyclomatic_complexity = CountDecisionPoints(func_cst) + 1;
```

**Subtasks:**
1. Add CST node type checking (if/case/for/while)
2. Implement recursive CST traversal
3. Count decision points per function
4. Calculate actual LOC from CST
5. Update tests to verify actual counts

---

### Task 3: Tool 4 - VeriPG Validator (2-3 hours)
**Priority**: HIGH (VeriPG critical)
**Status**: Framework only → Need actual CST validation

**What's needed:**
```cpp
// Current: Always 0 errors
int validation_errors = 0; // ❌
return absl::OkStatus();

// Need: Actual CST traversal
absl::Status ValidateTypes(...) {
  std::vector<std::string> errors;
  
  // Walk symbol table CST nodes
  WalkSymbolTable(symbol_table.Root(), [&](const SymbolTableNode& node) {
    if (node.Value().metatype == SymbolMetaType::kDataNetVariableInstance) {
      // Get assignment CST nodes
      const auto* cst = node.Value().syntax_origin;
      
      // Find assignments involving this variable
      // Use type_checker to validate types
      auto lhs_type = type_inference_->InferType(lhs);
      auto rhs_type = type_inference_->InferType(rhs);
      
      if (!TypesCompatible(lhs_type, rhs_type)) {
        errors.push_back(FormatError(node, lhs_type, rhs_type));
      }
    }
  });
  
  if (!errors.empty()) {
    return absl::InvalidArgumentError(JoinErrors(errors));
  }
  return absl::OkStatus();
}
```

**Subtasks:**
1. Implement symbol table walking
2. Extract assignment nodes from CST
3. Use TypeInference for actual type checking
4. Implement naming convention checks
5. Implement structure validation
6. Update tests to verify actual validation

---

### Task 4: Tool 5 - Refactoring Engine (4-5 hours)
**Priority**: MEDIUM-HIGH
**Status**: Framework only → Need actual CST manipulation

**What's needed for each operation:**

**ExtractFunction:**
```cpp
// Current: Returns kUnimplemented
return absl::UnimplementedError(...); // ❌

// Need: Actual extraction
absl::Status ExtractFunction(...) {
  // 1. Get CST nodes in selection range
  auto selected_nodes = ExtractCSTNodesInRange(selection);
  
  // 2. Analyze data flow
  auto [read_vars, write_vars] = AnalyzeDataFlow(selected_nodes);
  
  // 3. Generate function signature
  std::string signature = GenerateFunctionSignature(
      function_name, read_vars, write_vars);
  
  // 4. Generate function body
  std::string body = ExtractText(selected_nodes);
  
  // 5. Generate function call
  std::string call = GenerateCall(function_name, read_vars);
  
  // 6. Replace selection with call
  ReplaceTextRange(selection, call);
  
  // 7. Insert function definition
  InsertBefore(current_scope, signature + body);
  
  // 8. Write modified file
  WriteFile(filename, modified_content);
}
```

**Subtasks:**
1. Implement CST node extraction by line/column range
2. Implement data flow analysis (read/write variables)
3. Generate function signatures
4. Implement text replacement
5. Implement InlineFunction (reverse operation)
6. Implement ExtractVariable (simpler)
7. Implement MoveDeclaration
8. Update tests to verify actual transformations

---

### Task 5: CLI Tools for All 5 (3-4 hours)
**Priority**: HIGH (plan requirement)
**Status**: None exist → Need all 5

**Files to create:**
1. `verible/verilog/tools/rename/rename-main.cc`
2. `verible/verilog/tools/deadcode/deadcode-main.cc`
3. `verible/verilog/tools/complexity/complexity-main.cc`
4. `verible/verilog/tools/veripg/veripg-main.cc`
5. `verible/verilog/tools/refactor/refactor-main.cc`

**Common pattern:**
```cpp
int main(int argc, char** argv) {
  // Parse command-line flags
  absl::ParseCommandLine(argc, argv);
  
  // Parse input files
  VerilogProject project(...);
  for (const auto& file : input_files) {
    project.OpenTranslationUnit(file)->Parse();
  }
  
  // Build symbol table
  SymbolTable symbol_table(&project);
  symbol_table.Build(&diagnostics);
  
  // Perform operation
  Tool tool(&symbol_table, ...);
  auto result = tool.DoOperation(...);
  
  // Report results
  std::cout << result.summary << "\n";
  
  return result.ok() ? 0 : 1;
}
```

**Subtasks:**
1. Create each main.cc file
2. Add command-line flag definitions
3. Implement file parsing
4. Integrate with tool implementation
5. Add to BUILD files
6. Test each CLI manually

---

## Implementation Strategy

### Phase 1: Make Tools Actually Work (9-12 hours)
**Week 1-2:**
1. Tool 2 (Dead Code): 2-3 hours
2. Tool 3 (Complexity): 1-2 hours
3. Tool 4 (VeriPG): 2-3 hours
4. Tool 5 (Refactoring): 4-5 hours

### Phase 2: Add CLI Tools (3-4 hours)
**Week 2:**
1. All 5 CLI main.cc files
2. BUILD file updates
3. Manual testing

### Phase 3: Verification (2-3 hours)
**Week 2-3:**
1. Update tests to verify actual operations
2. Performance benchmarks
3. Integration testing
4. Documentation

---

## Key Technical Challenges

### Challenge 1: CST Node Location
**Problem**: Finding function definitions in CST from symbol table
**Solution**: Use `SymbolInfo::syntax_origin` pointer to CST node

### Challenge 2: Text Range Calculation
**Problem**: Converting CST node to byte offsets
**Solution**: Use `verible::StringSpanOfSymbol()` utility

### Challenge 3: Offset Preservation
**Problem**: Multiple edits shift byte offsets
**Solution**: Apply edits in reverse order (high to low offsets)

### Challenge 4: Data Flow Analysis
**Problem**: Determining variables read/written in code selection
**Solution**: Traverse CST, classify each identifier as read or write

### Challenge 5: Type Checking Integration
**Problem**: Using TypeInference/TypeChecker from Phase 4
**Solution**: Already have integration, just need to call actual methods

---

## Success Metrics (Updated)

### Per Tool:
- ✅ Actual CST operations implemented
- ✅ Real file I/O working (not just framework)
- ✅ Tests verify actual operations (not just API)
- ✅ CLI tools work from command line
- ✅ Performance targets met with real operations
- ✅ Zero regressions

### Overall:
- ✅ All 5 tools functionally complete
- ✅ All 5 CLI tools working
- ✅ Tests updated to verify actual behavior
- ✅ Plan compliance: 100%
- ✅ Documentation accurate

---

## Risk Mitigation

### Risk: CST APIs unclear
**Mitigation**: Study Symbol Renamer (working example), reference Verible docs

### Risk: Time estimate too low
**Mitigation**: User said "no hurry" - take time needed for quality

### Risk: Breaking existing tests
**Mitigation**: Update tests incrementally, keep framework tests working

### Risk: Performance issues
**Mitigation**: Profile and optimize, use same patterns as Symbol Renamer

---

## Next Immediate Actions

1. ✅ Create this plan document
2. ⏭️ Start Tool 2 implementation (Dead Code actual removal)
3. ⏭️ Continue with Tool 3, 4, 5 systematically
4. ⏭️ Add all CLI tools
5. ⏭️ Verify and test
6. ⏭️ Update documentation to reflect true 100%

---

*TRUE Completion Plan*  
*Target: 100% Functional + 100% Framework*  
*Estimated: 12-17 hours remaining*  
*Approach: No compromises, quality first*
