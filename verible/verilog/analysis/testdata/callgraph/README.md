# CallGraphEnhancer Test Data

This directory contains SystemVerilog test files for validating the `CallGraphEnhancer` component.

## Test Categories

### Call Graph Construction
- `empty_module.sv` - Module with no functions
- `single_function.sv` - One function, no calls
- `simple_call.sv` - Function A calls Function B
- `chained_calls.sv` - A -> B -> C
- `multiple_calls.sv` - A calls B and C
- `task_calls.sv` - Task call graph

### Recursion Detection
- `direct_recursion.sv` - f() calls f()
- `indirect_recursion.sv` - f() -> g() -> f()
- `long_cycle.sv` - f() -> g() -> h() -> f()
- `multiple_cycles.sv` - Multiple independent cycles
- `no_recursion.sv` - Acyclic graph

### Call Depth Analysis
- `linear_depth.sv` - A -> B -> C (depth = 2)
- `branching_depth.sv` - Multiple paths, different depths
- `max_depth.sv` - Verify max depth computation

### Entry Points and Unreachable
- `entry_points.sv` - Multiple entry points
- `unreachable_function.sv` - Function never called
- `all_reachable.sv` - All functions reachable

### Edge Cases
- `self_call.sv` - Function calls itself
- `mutual_recursion.sv` - A calls B, B calls A
- `large_callgraph.sv` - Many functions

## Expected Behavior

### Call Graph Construction
- Extract all function and task definitions
- Find all call sites (function calls)
- Build caller/callee relationships
- Create edges between nodes

### Recursion Detection
- Detect direct recursion (f() calls f())
- Detect indirect recursion (f() -> g() -> f())
- Identify all nodes in recursion cycles
- Mark cycles with kRecursive type

### Call Depth Analysis
- Entry points have depth 0
- Depth = longest path from any entry point
- Max depth = maximum of all node depths
- Avg depth = average of all node depths

### Entry Point Identification
- Functions with no callers
- Excluding DPI functions (may be called externally)
- Top-level functions in design

### Unreachable Function Detection
- Functions with no callers
- Not entry points
- Not DPI functions
- Should be flagged as unreachable

## Integration with SymbolTable

Tests rely on SymbolTable to provide:
- Function definitions (kFunction metatype)
- Task definitions (kTask metatype)
- Syntax origins for all definitions
- File origins for source location

