# Refactoring Tools

## Overview

`verible-verilog-refactor` provides automated code transformations for SystemVerilog including function extraction, inlining, variable extraction, and declaration optimization.

## Features

- **Extract Function** - Convert code selection into reusable function
- **Inline Function** - Replace function call with its body
- **Extract Variable** - Create named variable from expression
- **Move Declaration** - Relocate declarations to optimal scope

## Usage

### Extract Function
```bash
verible-verilog-refactor --operation=extract-function \
  --name=helper_func --start-line=10 --end-line=15 design.sv
```

### Inline Function
```bash
verible-verilog-refactor --operation=inline-function \
  --start-line=20 design.sv
```

### Extract Variable
```bash
verible-verilog-refactor --operation=extract-variable \
  --name=temp_result --start-line=30 design.sv
```

### Move Declaration
```bash
verible-verilog-refactor --operation=move-declaration \
  --start-line=5 design.sv
```

## Development Status

**Version:** 0.1.0  
**Test Coverage:** 20/20 tests passing

Framework complete. Full implementation in progress.

## See Also

- [Symbol Table](../../analysis/symbol-table.h)
- [Type Inference](../../analysis/type-inference.h)

