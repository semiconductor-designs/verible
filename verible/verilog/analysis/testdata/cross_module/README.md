# Cross-Module Test Data

Test data for Phase 2: Cross-Module Analysis

## Directory Structure

### simple/
Basic cross-file references:
- `module_a.sv` - Top module instantiates module_b
- `module_b.sv` - Middle module (leaf)
- `module_c.sv` - Alternative leaf module

**Tests**: Simple instantiation, basic symbol resolution

### hierarchical/
Multi-level module hierarchy:
- `top.sv` - Top level (instantiates mid_level)
- `mid_level.sv` - Middle level (instantiates leaf x2)
- `leaf.sv` - Leaf module

**Tests**: 3-level hierarchy, multiple instances, hierarchical type checking

### circular/
Circular dependency detection:
- `circular_a.sv` - Instantiates circular_b
- `circular_b.sv` - Instantiates circular_a (creates cycle)

**Tests**: Circular dependency detection, error reporting

### missing/
Missing module detection:
- `parent_with_missing.sv` - Instantiates non-existent module

**Tests**: Missing module detection, error handling

## Test Scenarios

1. **Valid Cross-File References** (simple/)
   - Resolve module_b from module_a
   - Build dependency graph
   - Verify symbol table entries

2. **Hierarchical Resolution** (hierarchical/)
   - Resolve 3-level hierarchy
   - Track multiple instances of same module
   - Validate port connections through hierarchy

3. **Error Detection** (circular/, missing/)
   - Detect circular dependencies
   - Detect missing modules
   - Generate appropriate error messages

## Usage

These test files are used by `multi-file-resolver_test.cc` to validate
cross-module symbol resolution and dependency analysis.

