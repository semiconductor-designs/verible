# UVM Test Fixtures

This directory contains test fixtures for UVM (Universal Verification Methodology) parsing support in Verible.

## Directory Structure

```
uvm/
├── macros/           # UVM macro test cases
├── constraints/      # Extern constraint test cases
├── type_params/      # Type parameter test cases
├── dist_constraints/ # Distribution constraint test cases
├── macro_in_macro/   # Complex nested macros
├── integration/      # Full UVM components
└── opentitan/        # Real-world examples from OpenTitan (to be added)
```

## Test Fixtures

### 1. UVM Macros (`macros/`)

**File**: `test_uvm_object_utils.sv`

Tests the most common UVM pattern: object registration macros with field automation.

**Features tested**:
- `uvm_object_utils_begin` / `uvm_object_utils_end`
- Nested `uvm_field_*` macros
- Class name as macro argument

**Current status**: Expected to fail (parser doesn't support UVM macros yet)

### 2. Extern Constraints (`constraints/`)

**File**: `test_extern_constraint.sv`

Tests out-of-body constraint definitions with advanced operators.

**Features tested**:
- `extern constraint` declaration
- `constraint ClassName::name { }` definition
- `soft` modifier
- `dist` operator with `:=` and `:/` weights
- `->` implication operator
- `inside` operator with ranges

**Current status**: Expected to fail (parser doesn't support extern constraints yet)

### 3. Type Parameters (`type_params/`)

**File**: `test_type_params.sv`

Tests parameterized classes with type parameters (similar to C++ templates).

**Features tested**:
- `#(type T = default_type)` syntax
- Type parameters in inheritance
- Multiple type parameters
- Mixed value and type parameters

**Current status**: Expected to fail (parser doesn't support type parameters yet)

### 4. Distribution Constraints (`dist_constraints/`)

**File**: `test_distribution.sv`

Tests distribution constraints with weight operators.

**Features tested**:
- `dist { value := weight }` syntax
- Range distributions `[low:high] := weight`
- Per-value (`:=`) vs per-range (`:/`) weights
- `inside` operator
- Implication (`->`) and bidirectional implication (`<->`)
- `solve...before` ordering

**Current status**: Expected to fail (parser doesn't support dist operator yet)

### 5. Complex Macros (`macro_in_macro/`)

**File**: `test_macro_in_macro.sv`

Tests advanced macro patterns with nesting and code blocks.

**Features tested**:
- Code blocks as macro arguments
- Macro calls inside macro arguments
- Triple-level nesting
- `fork`/`join` inside macros
- UVM macros inside custom macros

**Current status**: Expected to fail (parser doesn't support complex macro nesting yet)

## Testing Strategy

### Phase 1: Infrastructure (Current)

Create test fixtures and verify they fail as expected (TDD Red phase).

### Phase 2-6: Implementation

Implement grammar and parser enhancements, make tests pass (TDD Green phase).

### Phase 7: Kythe Integration

Add Kythe fact extraction for UVM constructs.

### Phase 8: Integration

Validate on real OpenTitan UVM files (89 files).

## Test Execution

These fixtures will be used by C++ unit tests:

```cpp
// Example test structure
TEST(UVMParser, ObjectUtilsMacro) {
  const char* kTestFile = "testdata/uvm/macros/test_uvm_object_utils.sv";
  VerilogAnalyzer analyzer(kTestFile, "");
  EXPECT_OK(analyzer.Analyze());
  const auto& parse_tree = analyzer.SyntaxTree();
  EXPECT_NE(parse_tree, nullptr);
}
```

## Expected Timeline

- **Weeks 1-2**: Fixtures created (current)
- **Weeks 3-10**: UVM macros support
- **Weeks 11-16**: Extern constraints support
- **Weeks 17-22**: Type parameters support
- **Weeks 23-26**: Distribution constraints support
- **Weeks 27-30**: Complex macros support
- **Weeks 31-40**: Integration and testing

## Success Criteria

- All fixtures parse without errors
- CST structure matches expected patterns
- No regressions in existing tests
- Performance: <5 minutes for all fixtures
- Memory: <500 MB peak

## References

- IEEE 1800.2-2017: UVM Standard
- OpenTitan UVM testbenches: Real-world validation corpus
- VeriPG Enhancement Request: Motivation and requirements

