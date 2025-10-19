# Verible v5.4.0 Release Notes

**Release Date**: January 19, 2025  
**Focus**: High-Impact UVM Enhancements

---

## 🎉 What's New

This release delivers three major enhancements for UVM/SystemVerilog verification:

### 1. Better Error Messages for Missing Macros

When macros are not found, Verible now provides actionable suggestions instead of generic errors.

**Example**:
```
Error: macro not defined: `uvm_info'

This appears to be a UVM macro. Solutions:
  1. Add UVM include path: --include_paths=/path/to/uvm/src
  2. Use pre-include: --pre_include=uvm_macros.svh
  3. Use package context: --package_context=my_pkg.sv
```

Supports detection of: UVM, DPI, RAL, Coverage, and OpenTitan-specific macros.

### 2. Pre-Include File Support 🆕

Process macro definition files before your main file:

```bash
verible-verilog-syntax \
  --include_paths=/path/to/uvm/src \
  --pre_include=uvm_macros.svh,dv_macros.svh \
  my_test.sv
```

**Benefits**:
- No need to modify source files
- Macros available throughout parsing
- Multiple pre-includes supported

### 3. Package Context Mode 🆕 ⭐

Extract and use macros and types from SystemVerilog package files:

```bash
verible-verilog-syntax \
  --include_paths=/path/to/includes \
  --package_context=my_pkg.sv \
  my_test.sv
```

**What gets extracted**:
- ✅ **Macros** (including from `include directives in packages)
- ✅ **Type definitions** (classes, typedefs)
- ✅ **Import statements** (package dependencies)

**OpenTitan validation**: Successfully extracted **576 macros** from OpenTitan packages!

**Key innovation**: Matches package-based compilation workflow used by UVM testbenches.

---

## Usage Examples

### Example 1: Basic UVM Test

```bash
verible-verilog-syntax \
  --include_paths=third_party/uvm/src \
  --pre_include=uvm_macros.svh \
  my_uvm_test.sv
```

### Example 2: OpenTitan Testbench

```bash
verible-verilog-syntax \
  --include_paths=third_party/uvm/src,hw/dv/sv \
  --package_context=hw/dv/sv/dv_utils/dv_utils_pkg.sv \
  hw/ip/my_ip/dv/env/my_ip_env_cfg.sv
```

### Example 3: Multiple Packages

```bash
verible-verilog-syntax \
  --include_paths=... \
  --package_context=pkg1.sv,pkg2.sv,pkg3.sv \
  my_test.sv
```

Later packages override earlier ones (standard SystemVerilog semantics).

---

## Compatibility

### No Breaking Changes

All v5.3.0 functionality is preserved. Existing command-lines continue to work.

### New Flags

- `--pre_include=<file>[,<file>...]` - Process files before main input
- `--package_context=<pkg>[,<pkg>...]` - Extract context from packages

### Requirements

- Include paths must be specified via `--include_paths` for package context to resolve `include directives
- For best results with OpenTitan: include UVM, dv_utils, and cip_lib paths

---

## Performance

- **Parse time**: <5% overhead when using package context
- **Memory**: Managed via smart pointers, no leaks
- **Scalability**: Tested with 576 macros, no degradation

---

## Known Limitations

### Package Context Mode

1. **Syntax errors in packages**: If a package has syntax errors, macros are still extracted, but a warning is shown
2. **Type usage**: Extracted types are tracked but not yet used for semantic analysis (planned for v5.5.0)

### Workarounds

If package parsing fails due to missing includes:
- Use `--pre_include` for critical macro files
- Add all necessary include paths via `--include_paths`

---

## Testing

### Test Coverage
- **Unit tests**: 66 tests (36 new for v5.4.0)
- **Success rate**: 100% (66/66 passing)
- **OpenTitan validation**: 576 macros extracted successfully
- **Regression tests**: Zero regressions from v5.3.0

### Validation Environment
- **Corpus**: OpenTitan UVM testbenches
- **Test files**: dv_base_reg, cip_lib, dv_utils packages
- **Result**: ✅ All macros successfully extracted

---

## Migration Guide

### From v5.3.0

**Step 1**: Update Verible to v5.4.0

**Step 2**: Try new features incrementally

```bash
# First, try your existing command (should work unchanged)
verible-verilog-syntax --include_paths=... my_file.sv

# Then, add pre-includes if you have macro issues
verible-verilog-syntax --include_paths=... \
  --pre_include=uvm_macros.svh \
  my_file.sv

# Finally, use package context for package-based projects
verible-verilog-syntax --include_paths=... \
  --package_context=my_pkg.sv \
  my_file.sv
```

**Step 3**: Enjoy better error messages automatically!

---

## What's Next (v5.5.0)

Planned enhancements:
- **Symbol table integration**: Use extracted types for semantic checking
- **Auto-detection**: Automatically find package files
- **Filelist support**: Process `.f` compilation files
- **Performance**: Cache parsed packages for repeated use

---

## Contributors

- Jonguk Song - Lead Developer
- Verible Team - Code reviews and infrastructure

---

## Getting Started

### Installation

Download the latest binary from the releases page or build from source:

```bash
bazel build //verible/verilog/tools/syntax:verible-verilog-syntax
```

### Quick Test

```bash
# Create a simple test
cat > test.sv << 'EOF'
`define MY_MACRO 42
module test;
  initial $display("Value: %d", `MY_MACRO);
endmodule
EOF

# Run Verible
verible-verilog-syntax test.sv
```

### Documentation

- Main README: `verible/verilog/tools/syntax/README.md`
- Feature details: `V5.4.0_COMPLETE_SUMMARY.md`
- Test scripts: `scripts/test_package_context*.sh`

---

## Feedback

Found an issue or have a suggestion? Please file an issue on GitHub!

---

## Thank You!

This release represents a major step forward for UVM support in Verible. We hope these enhancements make your verification workflow smoother and more productive.

Happy parsing! 🚀

