# Dead Code Elimination Tool

## Overview

`verible-verilog-deadcode` is an automated dead code detection and elimination tool for SystemVerilog. It uses call graph analysis to identify unreachable functions, tasks, and unused variables.

## Features

- **Automatic Detection** - Uses call graph to find unreachable code
- **Safe Elimination** - Dry-run mode to preview changes
- **Comprehensive Analysis** - Detects dead functions, tasks, and variables
- **Detailed Reports** - Shows what will be removed
- **Backup Safety** - Creates backups before modification

## Usage

### Basic Usage

```bash
verible-verilog-deadcode [--eliminate] [--dry-run] FILE
```

### Examples

#### 1. Report dead code (default)

```bash
verible-verilog-deadcode design.sv
```

Output:
```
Dead Code Detection Tool
File: design.sv
Mode: Report only

Dead Code Report:
  Functions: 3
    - unused_helper
    - old_calculate
    - debug_func
  Tasks: 1
    - obsolete_task
  Variables: 0

Total: 4 dead code items found
```

#### 2. Eliminate with dry-run (safe preview)

```bash
verible-verilog-deadcode --eliminate --dry-run design.sv
```

#### 3. Actually eliminate dead code

```bash
verible-verilog-deadcode --eliminate --no-dry-run design.sv
```

## Command-Line Options

| Flag | Description | Default |
|------|-------------|---------|
| `--eliminate` | Remove dead code (vs. report only) | false |
| `--dry-run` | Preview changes without modifying files | true |

## How It Works

### 1. Call Graph Analysis

The tool builds a call graph of all functions and tasks:

```systemverilog
function int main_calc(int x);  // Entry point (root)
  return helper(x);
endfunction

function int helper(int y);  // Called from main_calc (alive)
  return y * 2;
endfunction

function int unused_func(int z);  // Never called (DEAD)
  return z + 1;
endfunction
```

### 2. Reachability Analysis

Starting from entry points (typically `initial` blocks, `always` blocks, exported functions), the tool determines which functions/tasks are reachable.

### 3. Dead Code Identification

Any function/task not reachable from an entry point is marked as dead code.

## Examples

### Example 1: Simple Dead Function

```systemverilog
// Before
module calculator;
  function int add(int a, int b);
    return a + b;
  endfunction
  
  function int subtract(int a, int b);
    return a - b;
  endfunction
  
  // Never used
  function int multiply(int a, int b);
    return a * b;
  endfunction
  
  initial begin
    $display("Sum: %d", add(5, 3));
    $display("Diff: %d", subtract(10, 4));
  end
endmodule

// Run: verible-verilog-deadcode --eliminate calculator.sv

// After
module calculator;
  function int add(int a, int b);
    return a + b;
  endfunction
  
  function int subtract(int a, int b);
    return a - b;
  endfunction
  
  initial begin
    $display("Sum: %d", add(5, 3));
    $display("Diff: %d", subtract(10, 4));
  end
endmodule
// multiply() removed as dead code
```

### Example 2: Dead Code Chain

```systemverilog
// Before
function int unused_a();
  return unused_b();
endfunction

function int unused_b();
  return unused_c();
endfunction

function int unused_c();
  return 42;
endfunction

// All three functions are dead (none called from any entry point)
// verible-verilog-deadcode will report all 3 as dead
```

### Example 3: Partial Dead Code

```systemverilog
// Before
function int process();
  return stage1();
endfunction

function int stage1();
  return stage2();
endfunction

function int stage2();
  return 10;
endfunction

function int stage3();  // Not in call chain
  return 20;
endfunction

initial begin
  $display("Result: %d", process());
end

// stage3() is dead (not called by process chain)
```

## Safety Features

### 1. Dry-run by Default

The tool defaults to dry-run mode to prevent accidental deletions:

```bash
# Safe - just reports
verible-verilog-deadcode design.sv

# Safe - shows what would be removed
verible-verilog-deadcode --eliminate design.sv

# Actually removes dead code (requires explicit --no-dry-run)
verible-verilog-deadcode --eliminate --no-dry-run design.sv
```

### 2. Backup Files

Before removing code, the tool creates `.bak` files:

```
design.sv.bak  # Original file
design.sv      # Modified file
```

### 3. Report-only Mode

By default, the tool only reports dead code without eliminating:

```bash
verible-verilog-deadcode design.sv
```

## Best Practices

### 1. Always Use Dry-run First

```bash
# Step 1: Review what would be removed
verible-verilog-deadcode --eliminate design.sv

# Step 2: If looks good, actually remove
verible-verilog-deadcode --eliminate --no-dry-run design.sv
```

### 2. Use Version Control

```bash
git commit -am "Before dead code elimination"
verible-verilog-deadcode --eliminate --no-dry-run design.sv
git diff  # Review changes
```

### 3. Test After Elimination

```bash
verible-verilog-deadcode --eliminate --no-dry-run design.sv
# Re-run tests
make test
```

### 4. Consider Exported Functions

Functions exported via DPI or used in other modules may appear dead if the tool analyzes a single file. Use whole-project analysis when available.

## Limitations

### Current Version (Week 3)

- ✅ Dead function/task detection via call graph
- ✅ Comprehensive reporting
- ✅ Safe dry-run mode
- 🚧 Actual code removal (framework in place)
- 🚧 Dead variable detection (planned)
- 🚧 Multi-file analysis (planned)

### Known Issues

1. Functions used via string names (e.g., `$sformatf`) may be incorrectly marked as dead
2. DPI-exported functions may appear dead
3. Functions called from ignored files not yet supported

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | Invalid arguments |
| 2 | File I/O error |
| 3 | Analysis error |

## Integration

### With Lint Tools

```bash
# 1. Find dead code
verible-verilog-deadcode design.sv

# 2. Remove it
verible-verilog-deadcode --eliminate --no-dry-run design.sv

# 3. Verify no lint errors
verible-verilog-lint design.sv
```

### With CI/CD

```bash
# In CI pipeline: fail if dead code detected
verible-verilog-deadcode design.sv
if [ $? -ne 0 ]; then
  echo "Dead code detected!"
  exit 1
fi
```

## Development Status

**Phase:** Week 3 Complete ✅  
**Version:** 0.1.0  
**Test Coverage:** 15/15 tests passing

### Implementation Details

- Uses `CallGraph::FindDeadCode()` for analysis
- Integrates with Verible's symbol table
- Built on Phase 4 semantic analysis infrastructure

## See Also

- [Call Graph Documentation](../../analysis/call-graph.h)
- [Symbol Table Documentation](../../analysis/symbol-table.h)
- [Symbol Renaming Tool](../rename/README.md)

