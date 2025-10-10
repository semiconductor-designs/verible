# Verible Expression Metadata - Implementation Checklist

**Track progress as you implement each phase**

---

## Phase 1: Binary Expressions (Days 1-4)

### Day 1-2: Helper Functions & Infrastructure

- [ ] **Create helper function: `ExtractIdentifierFromExpression()`**
  - File: `verible/verilog/CST/identifier.cc`
  - Add function declaration to `identifier.h`
  - Handle `kReference` nodes
  - Handle direct identifier leaves
  - Return empty string for complex expressions
  - Test with simple cases

- [ ] **Create helper function: `MapOperatorToOperation()`**
  - File: `verible/verilog/CST/verilog-tree-json.cc`
  - Create mapping table for 24 binary operators
  - Arithmetic: `+`, `-`, `*`, `/`, `%`, `**`
  - Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`, `===`, `!==`
  - Logical: `&&`, `||`
  - Bitwise: `&`, `|`, `^`, `~^`, `^~`
  - Shift: `<<`, `>>`, `<<<`, `>>>`
  - Test all mappings

- [ ] **Create helper function: `ClassifyOperandType()`**
  - File: `verible/verilog/CST/verilog-tree-json.cc`
  - Return "reference" for variables
  - Return "literal" for numbers/strings
  - Return "expression" for nested operations
  - Test classification logic

### Day 2-3: Binary Expression Metadata

- [ ] **Implement `AddBinaryExpressionMetadata()`**
  - Extract operator from `node[1]`
  - Call `MapOperatorToOperation()`
  - Create metadata JSON object
  - Extract left operand (`node[0]`)
  - Extract right operand (`node[2]`)
  - Handle associative operators (multiple operands)
  - Add `expression_text` for nested expressions

- [ ] **Integrate into `Visit()` method**
  - Check if `node.Tag().tag == NodeEnum::kBinaryExpression`
  - Call `AddBinaryExpressionMetadata(node, *value_)`
  - Preserve existing `children` array

- [ ] **Update BUILD file dependencies**
  - Add `:identifier` to `verilog-tree-json` deps if needed

### Day 3-4: Testing

- [ ] **Create test file: `verilog-tree-json-metadata_test.cc`**
  - Test setup with Google Test framework

- [ ] **Write Unit Tests for Binary Expressions**
  - [ ] Test: Simple addition `a + b`
  - [ ] Test: Subtraction `a - b`
  - [ ] Test: Multiplication `a * b`
  - [ ] Test: Comparison `counter == 10`
  - [ ] Test: Logical AND `enable && valid`
  - [ ] Test: Bitwise OR `flags | mask`
  - [ ] Test: Binary with literal `counter + 1`
  - [ ] Test: Associative `a + b + c`
  - [ ] Test: Nested expression `(a + b) * c`
  - [ ] Test: All comparison operators

- [ ] **Add test target to BUILD file**
  - Create `cc_test` target
  - Link all dependencies

- [ ] **Run tests:** `bazel test //verible/verilog/CST:verilog-tree-json-metadata_test`

- [ ] **Verify all tests pass**

---

## Phase 2: Unary & Ternary Expressions (Days 5-7)

### Day 5: Unary Expressions

- [ ] **Update `MapOperatorToOperation()` for unary operators**
  - Add unary mappings: `~`, `!`, `-` (unary), `+` (unary)
  - Add reduction operators: `&`, `|`, `^`, `~&`, `~|`, `~^`, `^~`

- [ ] **Implement `AddUnaryExpressionMetadata()`**
  - Extract operator from `node[0]`
  - Extract operand from `node[1]`
  - Create metadata with single operand
  - Set operand role to "operand"

- [ ] **Integrate into `Visit()` method**
  - Check for `NodeEnum::kUnaryPrefixExpression`
  - Call `AddUnaryExpressionMetadata()`

- [ ] **Write Unit Tests for Unary Expressions**
  - [ ] Test: Bitwise NOT `~enable`
  - [ ] Test: Logical NOT `!valid`
  - [ ] Test: Negation `-counter`
  - [ ] Test: Reduction AND `&data_bus`
  - [ ] Test: Reduction OR `|flags`
  - [ ] Test: Reduction XOR `^parity`

- [ ] **Run tests and verify**

### Day 6-7: Ternary Expressions

- [ ] **Implement `AddTernaryExpressionMetadata()`**
  - Extract condition from `node[0]`
  - Extract true case from `node[2]`
  - Extract false case from `node[4]`
  - Set operation to "ternary"
  - Set operator to "?:"
  - Set roles: "condition", "true_value", "false_value"

- [ ] **Integrate into `Visit()` method**
  - Check for `NodeEnum::kConditionExpression`
  - Call `AddTernaryExpressionMetadata()`

- [ ] **Write Unit Tests for Ternary Expressions**
  - [ ] Test: Simple mux `sel ? a : b`
  - [ ] Test: With literal `sel ? a : 0`
  - [ ] Test: With nested expression `sel ? (a + b) : c`
  - [ ] Test: Nested ternary `enable ? (sel ? a : b) : c`

- [ ] **Run all tests (Phase 1 + Phase 2)**

- [ ] **Integration test with all three types**

---

## Phase 3: Function Calls (Days 8-10) [OPTIONAL]

### Day 8-9: Function Call Implementation

- [ ] **Study `GetFunctionCallName()` utility**
  - File: `verible/verilog/CST/functions.cc`
  - Understand function name extraction

- [ ] **Implement `AddFunctionCallMetadata()`**
  - Extract function name
  - Extract arguments from `kParenGroup`
  - Handle positional arguments
  - Set roles: "arg0", "arg1", "arg2", ...
  - Set operation to "function_call"

- [ ] **Integrate into `Visit()` method**
  - Check for `NodeEnum::kFunctionCall`
  - Call `AddFunctionCallMetadata()`

### Day 10: Testing

- [ ] **Write Unit Tests for Function Calls**
  - [ ] Test: System function `$clog2(counter)`
  - [ ] Test: User function `my_func(a, b)`
  - [ ] Test: Package function `pkg::calc(x, y, z)`
  - [ ] Test: Nested arguments `func(a + b, c)`

- [ ] **Run all tests**

---

## Phase 4: Testing & Documentation (Days 11-15)

### Day 11-12: Comprehensive Integration Testing

- [ ] **Create integration test file: `test_metadata_integration.sv`**
  - Include all binary operators (24 cases)
  - Include all unary operators (14 cases)
  - Include ternary expressions (5 cases)
  - Include nested expressions (10 cases)
  - Include function calls if implemented (5 cases)

- [ ] **Create validation script: `validate_metadata.py`**
  - Parse JSON output
  - Find all expression nodes
  - Validate metadata structure
  - Check all required fields
  - Verify operand roles
  - Print summary report

- [ ] **Run integration test**
  - Build Verible: `bazel build //verible/verilog/tools/syntax:verible-verilog-syntax --macos_minimum_os=10.15`
  - Generate JSON: `verible-verilog-syntax --export_json test_metadata_integration.sv > output.json`
  - Validate: `python3 validate_metadata.py output.json`

- [ ] **Fix any issues found**

### Day 13: VeriPG Integration

- [ ] **Build production binary**
  - `bazel build //verible/verilog/tools/syntax:verible-verilog-syntax --macos_minimum_os=10.15 -c opt`

- [ ] **Deploy to VeriPG**
  - Copy binary to `VeriPG/tools/verible/bin/`
  - Verify binary version

- [ ] **Update VeriPG code (if time allows)**
  - Simplify expression parsing using metadata
  - Add metadata-based parameter extraction
  - Keep fallback to text field

- [ ] **Run VeriPG tests**
  - `cd VeriPG && pytest tests/`
  - Verify all tests pass
  - Check parameter extraction test

- [ ] **Measure improvements**
  - Lines of code reduced
  - Performance improvement
  - Test coverage

### Day 14: Documentation

- [ ] **Update Verible README**
  - Add section on metadata field
  - Include example JSON output

- [ ] **Create JSON format documentation**
  - File: `doc/verible_json_metadata.md`
  - Schema definition
  - Examples for each expression type
  - Backward compatibility notes

- [ ] **Update release notes**
  - Enhancement description
  - Breaking changes: None
  - Migration guide: Not needed (backward compatible)

- [ ] **Create contribution guide (if upstreaming)**
  - Rationale for changes
  - Use cases
  - Test coverage

### Day 15: Final Testing & Cleanup

- [ ] **Run full Verible test suite**
  - `bazel test //verible/verilog/...`
  - Ensure no regressions

- [ ] **Performance benchmark**
  - Test on large files (1000+ expressions)
  - Measure JSON generation time
  - Verify overhead <5%

- [ ] **Code review checklist**
  - [ ] All functions documented
  - [ ] No memory leaks
  - [ ] Error handling for edge cases
  - [ ] Consistent coding style
  - [ ] All tests passing

- [ ] **Create summary report**
  - Features implemented
  - Test coverage achieved
  - Performance metrics
  - VeriPG integration results

---

## Post-Implementation

### Repository & Version Control

- [ ] **Commit changes to feature branch**
  - Atomic commits per phase
  - Clear commit messages

- [ ] **Merge to fork main branch**
  - Branch: `semiconductor-designs/verible:master`
  - Create PR with full description

- [ ] **Tag release**
  - Version: `v0.0-XXXX-metadata-enhancement`

### Upstream Contribution (Optional)

- [ ] **Prepare contribution PR for chipsalliance/verible**
  - Clean commit history
  - Comprehensive PR description
  - Link to enhancement request
  - Include all tests and documentation

- [ ] **Submit PR**
  - Wait for maintainer feedback
  - Address review comments

### VeriPG Finalization

- [ ] **Fully integrate metadata in VeriPG**
  - Remove old expression parsing code
  - Use metadata-first approach
  - Keep text fallback for safety

- [ ] **Update VeriPG documentation**
  - Note dependency on enhanced Verible
  - Document metadata usage

- [ ] **Performance report**
  - Before/after comparison
  - Code complexity metrics

---

## Success Verification

### Functional Verification

- [ ] ✅ All binary operators produce correct metadata
- [ ] ✅ All unary operators produce correct metadata
- [ ] ✅ Ternary expressions produce correct metadata
- [ ] ✅ Function calls produce correct metadata (if implemented)
- [ ] ✅ Nested expressions handled correctly
- [ ] ✅ Literals identified correctly
- [ ] ✅ References extracted correctly
- [ ] ✅ Edge cases handled gracefully

### Test Coverage

- [ ] ✅ 25+ unit tests passing
- [ ] ✅ Integration test passing
- [ ] ✅ No regressions in existing tests
- [ ] ✅ VeriPG tests passing

### Quality Metrics

- [ ] ✅ Code coverage >90% for new code
- [ ] ✅ Performance overhead <5%
- [ ] ✅ Zero memory leaks
- [ ] ✅ Backward compatible (100%)

### Documentation

- [ ] ✅ README updated
- [ ] ✅ JSON format documented
- [ ] ✅ Examples provided
- [ ] ✅ Release notes written

---

## Rollback Plan (If Needed)

If critical issues are discovered:

1. **Immediate Rollback**
   - Revert to previous Verible binary in VeriPG
   - File: `VeriPG/tools/verible/bin/verible-verilog-syntax`

2. **Branch Revert**
   - Don't merge feature branch
   - Fix issues in feature branch
   - Re-test before retry

3. **Gradual Deployment**
   - Keep metadata as "experimental" flag
   - Add command-line option: `--export_json_metadata`
   - Default to off until validated

---

**Implementation Start Date:** _________________

**Implementation End Date:** _________________

**Implemented By:** _________________

**Status:** ⬜ Not Started | ⬜ In Progress | ⬜ Complete

---

*Track your progress by checking off items as you complete them!*

