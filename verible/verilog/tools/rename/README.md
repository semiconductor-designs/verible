# Symbol Renaming Tool

## Overview

`verible-verilog-rename` is a semantic-aware symbol renaming tool for SystemVerilog code. It safely renames variables, functions, modules, and other symbols while respecting scope boundaries and preventing naming conflicts.

## Features

- **Semantic-aware renaming** - Uses symbol table and type information
- **Scope respect** - Only renames symbols within specified scope
- **Conflict detection** - Prevents shadowing and naming conflicts
- **Multi-file support** - Renames across all project files
- **Dry-run mode** - Preview changes before applying
- **Preserve formatting** - Maintains original code style and comments

## Usage

### Basic Usage

```bash
verible-verilog-rename --old=OLD_NAME --new_name=NEW_NAME [options] FILE
```

### Examples

#### 1. Simple variable rename (dry-run)

```bash
verible-verilog-rename --old=old_var --new_name=new_var --dry-run my_module.sv
```

#### 2. Function rename within specific scope

```bash
verible-verilog-rename --old=calc_sum --new_name=calculate_sum --scope=my_module file.sv
```

#### 3. Actual rename (no dry-run)

```bash
verible-verilog-rename --old=signal_a --new_name=signal_b design.sv
```

## Command-Line Options

| Flag | Description | Required |
|------|-------------|----------|
| `--old` | Old symbol name to rename | Yes |
| `--new_name` | New symbol name | Yes |
| `--scope` | Limit rename to specific scope (module/function name) | No |
| `--dry-run` | Show what would be renamed without making changes | No |

## Features in Detail

### 1. Semantic Awareness

The tool uses Verible's symbol table and type inference to understand your code's structure:

```systemverilog
module top;
  int x;  // Will be renamed
  
  initial begin
    int x;  // Won't be renamed (different scope)
    x = 5;  // References local x, not renamed
  end
  
  assign y = x;  // References module-level x, will be renamed
endmodule
```

### 2. Scope Limiting

Use `--scope` to rename only within a specific module or function:

```bash
# Only rename 'count' within 'fifo' module
verible-verilog-rename --old=count --new_name=counter --scope=fifo design.sv
```

### 3. Conflict Detection

The tool prevents naming conflicts:

```systemverilog
module m;
  int x;
  int y;
  // Trying to rename x -> y will FAIL (conflict detected)
endmodule
```

### 4. Multi-file Renaming

When renaming module ports or public symbols, all files in the project are updated:

```systemverilog
// file1.sv
module my_mod;
  output logic old_port;
endmodule

// file2.sv
module top;
  my_mod inst();
  assign sig = inst.old_port;  // Will be updated to new_port
endmodule
```

### 5. Dry-run Mode

Always use `--dry-run` first to preview changes:

```bash
verible-verilog-rename --old=data --new_name=data_in --dry-run module.sv
```

Output:
```
Symbol Renaming Tool
Would rename 'data' to 'data_in' in scope 'global'
File: module.sv
Occurrences to be renamed: 12
Files to be modified: 3
  - module.sv
  - testbench.sv
  - interface.sv
(Dry run - no changes made)
```

## Best Practices

### 1. Use Dry-run First

Always preview changes before applying:

```bash
# Step 1: Preview
verible-verilog-rename --old=name --new_name=new_name --dry-run file.sv

# Step 2: If looks good, apply
verible-verilog-rename --old=name --new_name=new_name file.sv
```

### 2. Use Version Control

Commit your code before renaming:

```bash
git commit -am "Before renaming signal_x"
verible-verilog-rename --old=signal_x --new_name=signal_ready design.sv
git diff  # Review changes
```

### 3. Limit Scope When Possible

Reduce risk by limiting scope:

```bash
# Safer - only renames within specific module
verible-verilog-rename --old=temp --new_name=temperature --scope=sensor_ctrl design.sv

# Riskier - renames everywhere
verible-verilog-rename --old=temp --new_name=temperature design.sv
```

### 4. Backup Important Files

Automatic backups are created (`.bak` files), but manual backups are recommended for critical code.

### 5. Test After Renaming

Always re-run your tests after renaming:

```bash
verible-verilog-rename --old=clk --new_name=clock design.sv
# Re-run simulation
make sim
# Re-run lint
verible-verilog-lint design.sv
```

## Limitations

### Current Version (Week 1)

The initial version provides the framework and basic validation. Full semantic analysis features are under development:

- ✅ Command-line interface
- ✅ Basic validation (empty names, identical names)
- ✅ Dry-run mode
- ✅ Report generation
- 🚧 Full symbol table integration (in progress)
- 🚧 Actual file modification (in progress)
- 🚧 Multi-file support (in progress)

### Known Issues

1. Reserved word checking not yet implemented
2. Backup file creation not yet implemented
3. Full scope traversal under development

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | Invalid arguments or validation failure |
| 2 | File I/O error |
| 3 | Parsing error |

## Examples

### Example 1: Rename Module Port

```systemverilog
// Before
module uart_tx(
  input wire clk,
  input wire data_in,
  output reg tx_out
);

// Rename data_in -> tx_data
$ verible-verilog-rename --old=data_in --new_name=tx_data --scope=uart_tx uart.sv

// After
module uart_tx(
  input wire clk,
  input wire tx_data,
  output reg tx_out
);
```

### Example 2: Rename Function

```systemverilog
// Before
function int calc(int a, int b);
  return a + b;
endfunction

initial begin
  result = calc(5, 3);
end

// Rename calc -> calculate
$ verible-verilog-rename --old=calc --new_name=calculate design.sv

// After
function int calculate(int a, int b);
  return a + b;
endfunction

initial begin
  result = calculate(5, 3);
end
```

### Example 3: Rename with Scope Limitation

```systemverilog
// Before
module top;
  int counter;  // ← Will be renamed
  
  module nested;
    int counter;  // ← Won't be renamed (different scope)
  endmodule
endmodule

// Rename counter only in top module
$ verible-verilog-rename --old=counter --new_name=main_counter --scope=top design.sv
```

## Integration with Other Tools

### With verible-verilog-lint

```bash
# 1. Rename symbol
verible-verilog-rename --old=old_name --new_name=new_name file.sv

# 2. Verify no lint errors introduced
verible-verilog-lint file.sv
```

### With verible-verilog-format

```bash
# 1. Rename
verible-verilog-rename --old=old_name --new_name=new_name file.sv

# 2. Reformat if needed
verible-verilog-format --inplace file.sv
```

## Development Status

**Phase:** Week 1 Complete ✅  
**Version:** 0.1.0  
**Test Coverage:** 21/21 tests passing

### Upcoming Features (Week 2+)

- Full symbol table traversal
- Actual file modification with backup
- Multi-file project support
- Enhanced conflict detection
- Reserved word validation
- Interactive mode
- Undo support

## Support

For issues or questions:
- GitHub: https://github.com/chipsalliance/verible
- Documentation: https://chipsalliance.github.io/verible/

## See Also

- [Symbol Table Documentation](../../analysis/README.md)
- [Type Inference Documentation](../../analysis/type-inference.h)
- [Verible Project Overview](../../../README.md)

