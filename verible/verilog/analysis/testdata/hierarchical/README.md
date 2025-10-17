# Hierarchical Type Checker Test Data

This directory contains comprehensive test cases for the `HierarchicalTypeChecker` component, which validates type hierarchies, inheritance, and cross-module type compatibility in SystemVerilog code.

## Directory Structure

### `basic/`
Basic hierarchical validation scenarios:
- **`simple_hierarchy.sv`**: Simple module hierarchy with parent-child relationships
- **`multi_level.sv`**: Multi-level module instantiation (3+ levels deep)
- **`cross_file_types.sv`**: Type references across multiple files

### `inheritance/`
Class and interface inheritance scenarios:
- **`class_extends.sv`**: Basic class inheritance (extends keyword)
- **`multiple_inheritance.sv`**: Multiple base class scenarios
- **`interface_inheritance.sv`**: Interface extends interface
- **`virtual_methods.sv`**: Virtual method overrides and polymorphism

### `types/`
Type compatibility and resolution:
- **`type_compatibility.sv`**: Cross-module type matching
- **`struct_hierarchy.sv`**: Struct type checking across modules
- **`enum_hierarchy.sv`**: Enum type compatibility
- **`typedef_hierarchy.sv`**: Typedef resolution in hierarchies

### `errors/`
Error detection scenarios:
- **`inheritance_error.sv`**: Circular inheritance detection
- **`type_mismatch.sv`**: Incompatible type errors
- **`missing_base.sv`**: Missing base class/interface errors
- **`override_error.sv`**: Invalid method override errors

### `advanced/`
Complex scenarios:
- **`parametric_inheritance.sv`**: Parameterized class inheritance
- **`mixed_hierarchy.sv`**: Mixed module/class/interface hierarchies

## Test Coverage

### Type Hierarchy Building
- ✅ Module instantiation trees
- ✅ Class inheritance chains
- ✅ Interface inheritance
- ✅ Cross-file type references

### Inheritance Validation
- ✅ Valid extends relationships
- ✅ Circular inheritance detection
- ✅ Missing base class detection
- ✅ Virtual method overrides
- ✅ Method signature compatibility

### Type Compatibility
- ✅ Struct field matching
- ✅ Enum value compatibility
- ✅ Typedef resolution
- ✅ Packed/unpacked compatibility
- ✅ Parametric type matching

### Error Detection
- ✅ Circular inheritance
- ✅ Type mismatches
- ✅ Missing declarations
- ✅ Invalid overrides
- ✅ Access violations

## Expected Behavior

### Valid Test Cases
Files in `basic/`, `inheritance/`, `types/`, and most of `advanced/` should:
- Parse successfully
- Build valid type hierarchies
- Pass inheritance validation
- Show no errors (or only warnings where appropriate)

### Error Test Cases
Files in `errors/` should:
- Parse successfully
- Detect specific error conditions
- Report clear error messages with locations
- Not crash or hang

## Usage in Tests

Each test file is designed to be:
1. Parsed with `VerilogAnalyzer`
2. Built into `SymbolTable`
3. Validated with `HierarchicalTypeChecker`
4. Checked for expected errors/warnings

Example test pattern:
```cpp
TEST_F(HierarchicalTypeCheckerTest, SimpleClassExtends) {
  const auto result = ParseCode(R"(
    class BaseClass;
      int value;
    endclass
    
    class DerivedClass extends BaseClass;
      int extra;
    endclass
  )");
  
  HierarchicalTypeChecker checker(result.symbol_table, result.project);
  checker.ValidateHierarchy();
  
  EXPECT_TRUE(checker.GetErrors().empty());
  EXPECT_EQ(checker.GetTypeHierarchy().size(), 2);
}
```

## Test Statistics

- **Total test files**: 15-18
- **Test categories**: 5
- **Expected tests**: 25-30
- **Target pass rate**: 100%

## Maintenance

When adding new test files:
1. Place in appropriate category directory
2. Update this README
3. Add corresponding test case in `hierarchical-type-checker_test.cc`
4. Document expected behavior
5. Ensure file parses correctly

## Related Components

This test data is used by:
- `HierarchicalTypeChecker` (Week 9)
- `SemanticAnalyzer` (Phase 2 integration)
- May be referenced by future Phase 3 components

---

**Created**: Week 9 Day 41  
**Purpose**: Comprehensive hierarchical type checking validation  
**Target**: 100% test coverage of inheritance and type compatibility

