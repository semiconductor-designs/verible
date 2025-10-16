# VeriPG Validator Auto-Fix Guide

**Version 5.0.0** | Complete guide to automated code fixes

## Table of Contents

1. [Overview](#overview)
2. [Safe vs Unsafe Fixes](#safe-vs-unsafe-fixes)
3. [Using Auto-Fix](#using-auto-fix)
4. [Fix Generators Reference](#fix-generators-reference)
5. [Safety Guidelines](#safety-guidelines)
6. [Best Practices](#best-practices)

---

## Overview

VeriPG Validator can automatically generate and apply fixes for many common violations. The auto-fix system is designed with safety in mind, classifying fixes as **safe** (low risk) or **unsafe** (requires manual review).

### Key Features

- **7+ fix generators** covering common violations
- **Safety classification** for all fixes
- **Preview mode** to review changes before applying
- **Backup creation** for all modified files
- **Batch fixing** for entire projects
- **Selective application** by rule or severity

---

## Safe vs Unsafe Fixes

### Safe Fixes (Auto-applicable)

**Safe fixes** make syntactic or formatting changes that preserve functionality:

| Rule | Fix Type | Example |
|------|----------|---------|
| NAM_001 | Rename to snake_case | `MyModule` → `my_module` |
| NAM_003 | Rename to UPPER_CASE | `width` → `WIDTH` |
| CLK_001 | Add clock to sensitivity | `always_ff begin` → `always_ff @(posedge clk) begin` |
| STR_005 | Reorder ports | Reorder to: clk, rst, inputs, outputs |
| STR_006 | Convert to named ports | `.data(data)` instead of positional |
| STR_008 | Add default clause | Add `default:` to case statement |

**Characteristics:**
- ✅ Preserve functionality
- ✅ Syntactic/formatting only
- ✅ Low risk of introducing bugs
- ✅ Can be applied automatically
- ✅ Easy to verify

### Unsafe Fixes (Require Review)

**Unsafe fixes** modify functionality or make assumptions:

| Rule | Fix Type | Why Unsafe | Review Points |
|------|----------|------------|---------------|
| CDC_001 | Add synchronizer | Assumes 2-stage sync sufficient | Clock domain, reset handling |
| CDC_002 | Add Gray code conversion | Assumes Gray code appropriate | Multi-bit semantics |
| RST_001 | Add reset logic | Assumes reset polarity and initial values | Reset value correctness |
| WID_001 | Add explicit cast | May change intended behavior | Data width requirements |
| CLK_004 | Add ICG cell | Technology-specific | ICG cell availability |

**Characteristics:**
- ⚠️ May change functionality
- ⚠️ Make design assumptions
- ⚠️ Require verification
- ⚠️ Need manual review
- ⚠️ Simulation/testing required

---

## Using Auto-Fix

### Preview Fixes (Recommended First Step)

Generate fix suggestions without modifying files:

```bash
veripg-validator --auto-fix design.sv
```

Output shows proposed fixes:

```
[WARNING] NAM_001: Module naming violation
  File: design.sv:1:8
  Current: module MyModule;
  Suggested: module my_module;
  Fix Type: SAFE (automatic rename)

[ERROR] CDC_001: CDC without synchronizer
  File: design.sv:10:5
  Signal: async_data
  Suggested: Add 2-stage synchronizer
  Fix Type: UNSAFE (requires manual review)
  
  // Suggested code:
  logic [1:0] sync_async_data;
  always_ff @(posedge clk_b) begin
    sync_async_data <= {sync_async_data[0], async_data};
    data_b <= sync_async_data[1];
  end
```

### Apply Safe Fixes Only

Automatically apply fixes marked as safe:

```bash
veripg-validator --auto-fix --apply-safe design.sv
```

This will:
1. Create backup (`design.sv.bak`)
2. Apply all safe fixes
3. Report applied changes

### Apply All Fixes (Use with Caution)

```bash
veripg-validator --auto-fix --apply-all design.sv
```

⚠️ **WARNING**: This applies both safe AND unsafe fixes. Always review changes and run simulation/tests.

### Apply Specific Rule Fixes

Apply fixes for specific rules only:

```bash
veripg-validator --auto-fix --apply-rules=NAM_001,NAM_003,STR_008 design.sv
```

### Batch Fixing

Apply fixes to multiple files:

```bash
veripg-validator --auto-fix --apply-safe --batch rtl/**/*.sv
```

### Interactive Mode

Review and approve each fix:

```bash
veripg-validator --auto-fix --interactive design.sv
```

For each violation:
```
[NAM_001] module MyModule; → module my_module;
Apply this fix? [y/n/a/q] (y=yes, n=no, a=all, q=quit):
```

---

## Fix Generators Reference

### NAM_001: Module Name to snake_case

**Type:** Safe  
**Complexity:** Low

**Before:**
```systemverilog
module MyModule;
  // ...
endmodule
```

**After:**
```systemverilog
module my_module;
  // ...
endmodule
```

**Implementation:**
- Converts PascalCase/camelCase to snake_case
- Preserves underscores
- Updates module name and endmodule label
- Updates instantiations in parent modules (if `--fix-references`)

**Configuration:**
```yaml
auto_fix:
  NAM_001:
    fix_references: true  # Update instantiations
    preserve_acronyms: true  # USB_CDC → usb_cdc
```

---

### NAM_003: Parameter Name to UPPER_CASE

**Type:** Safe  
**Complexity:** Low

**Before:**
```systemverilog
parameter width = 8;
parameter DataDepth = 16;
```

**After:**
```systemverilog
parameter WIDTH = 8;
parameter DATA_DEPTH = 16;
```

---

### CLK_001: Add Clock to Sensitivity List

**Type:** Safe  
**Complexity:** Medium

**Before:**
```systemverilog
always_ff begin
  data_reg <= data_in;
end
```

**After:**
```systemverilog
always_ff @(posedge clk) begin
  data_reg <= data_in;
end
```

**Detection:**
- Analyzes signal usage to infer clock name
- Defaults to `clk` if ambiguous
- Detects positive/negative edge from reset logic

**Configuration:**
```yaml
auto_fix:
  CLK_001:
    default_clock_name: "clk"
    default_edge: "posedge"
```

---

### CDC_001: Add 2-Stage Synchronizer (UNSAFE)

**Type:** Unsafe  
**Complexity:** High  
**Review Required:** Yes

**Before:**
```systemverilog
always_ff @(posedge clk_b) begin
  data_b <= data_a;  // From clk_a domain
end
```

**After:**
```systemverilog
logic [1:0] sync_data_a;
always_ff @(posedge clk_b) begin
  sync_data_a <= {sync_data_a[0], data_a};
  data_b <= sync_data_a[1];
end
```

**⚠️ Review Points:**
- Verify 2-stage sync is sufficient (may need 3+ stages)
- Check if reset is needed
- Verify clock domain assumptions
- Consider MTBF requirements
- Test with CDC analysis tools

---

### RST_001: Add Reset Logic (UNSAFE)

**Type:** Unsafe  
**Complexity:** High  
**Review Required:** Yes

**Before:**
```systemverilog
always_ff @(posedge clk) begin
  counter <= counter + 1;
end
```

**After:**
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n)
    counter <= '0;
  else
    counter <= counter + 1;
end
```

**⚠️ Review Points:**
- Verify reset initial value ('0 may not be correct)
- Check reset polarity (active-high vs active-low)
- Verify synchronous vs asynchronous reset
- Test reset behavior

---

### STR_005: Reorder Ports

**Type:** Safe  
**Complexity:** Medium

**Before:**
```systemverilog
module my_module (
  input data_in,
  input clk,
  output data_out,
  input rst_n
);
```

**After:**
```systemverilog
module my_module (
  input clk,
  input rst_n,
  input data_in,
  output data_out
);
```

**Order:** clk → rst → inputs → outputs → inouts

---

### STR_006: Convert to Named Ports

**Type:** Safe  
**Complexity:** Medium

**Before:**
```systemverilog
sub_module u1 (clk, rst_n, data_in, data_out);
```

**After:**
```systemverilog
sub_module u1 (
  .clk      (clk),
  .rst_n    (rst_n),
  .data_in  (data_in),
  .data_out (data_out)
);
```

---

### STR_008: Add Default Clause

**Type:** Safe  
**Complexity:** Low

**Before:**
```systemverilog
always_comb begin
  case (sel)
    2'b00: out = a;
    2'b01: out = b;
  endcase
end
```

**After:**
```systemverilog
always_comb begin
  case (sel)
    2'b00: out = a;
    2'b01: out = b;
    default: out = '0;
  endcase
end
```

---

## Safety Guidelines

### Before Applying Fixes

1. **Backup your code**: Use version control or create backups
   ```bash
   git add -A && git commit -m "Before auto-fix"
   ```

2. **Review in preview mode first**:
   ```bash
   veripg-validator --auto-fix design.sv > fixes.txt
   ```

3. **Read unsafe fix warnings**: Understand what each fix does

4. **Check your test coverage**: Ensure you can verify changes

### After Applying Fixes

1. **Review the diff**:
   ```bash
   git diff design.sv
   ```

2. **Run lint/syntax check**:
   ```bash
   veripg-validator design.sv  # Check for new violations
   ```

3. **Run simulation**:
   ```bash
   make sim  # Verify functionality unchanged
   ```

4. **Run synthesis** (for design changes):
   ```bash
   make synth  # Check for timing/area impact
   ```

5. **CDC analysis** (for CDC fixes):
   ```bash
   spyglass -cdc design.sv
   ```

### Red Flags (Do Not Auto-Apply)

🚫 **Never auto-apply these without careful review:**

- CDC synchronizer additions (CDC_001, CDC_002)
- Reset logic additions (RST_001, RST_002)
- Width conversions that may truncate data (WID_001, WID_002)
- Timing-critical path changes
- Fixes affecting protocol compliance
- Fixes in verified legacy code

---

## Best Practices

### 1. Incremental Adoption

Start with safe, low-impact fixes:

```bash
# Week 1: Naming conventions only
veripg-validator --auto-fix --apply-rules=NAM_001,NAM_003 rtl/**/*.sv

# Week 2: Add structural fixes
veripg-validator --auto-fix --apply-rules=STR_005,STR_006,STR_008 rtl/**/*.sv

# Week 3: Review unsafe fixes manually
veripg-validator --auto-fix --show-unsafe rtl/**/*.sv > unsafe_fixes.txt
```

### 2. Separate Safe and Unsafe Commits

```bash
# Commit 1: Safe fixes
veripg-validator --auto-fix --apply-safe rtl/**/*.sv
git add -A && git commit -m "Auto-fix: Safe naming and structural fixes"

# Commit 2: Each unsafe fix individually after review
# (Manual application and testing for each)
git commit -m "Fix CDC_001 in module X (reviewed and tested)"
```

### 3. Use CI/CD for Validation

```yaml
# .github/workflows/veripg.yml
- name: Check for safe auto-fix opportunities
  run: |
    veripg-validator --auto-fix --safe-only rtl/**/*.sv > safe_fixes.txt
    if [ -s safe_fixes.txt ]; then
      echo "::warning::Safe fixes available"
      cat safe_fixes.txt
    fi
```

### 4. Team Review for Unsafe Fixes

```bash
# Generate fix report for code review
veripg-validator --auto-fix --unsafe-only design.sv > fixes_for_review.md

# Include in pull request for team review
```

### 5. Test-Driven Fixing

```bash
# 1. Run tests before fix
make test > before.log

# 2. Apply fix
veripg-validator --auto-fix --apply-safe design.sv

# 3. Run tests after fix
make test > after.log

# 4. Compare results
diff before.log after.log
```

---

## Configuration

Configure auto-fix behavior in `.veripg.yml`:

```yaml
auto_fix:
  # Safe fixes
  enable_safe_fixes: true
  backup_originals: true
  backup_suffix: ".bak"
  
  # Unsafe fixes
  enable_unsafe_fixes: false  # Require explicit --apply-all
  require_confirmation: true
  
  # Formatting
  preserve_formatting: true
  indent_style: "spaces"
  indent_size: 2
  
  # Rule-specific
  NAM_001:
    fix_references: true  # Update instantiations
    preserve_acronyms: true
  
  CLK_001:
    default_clock_name: "clk"
    infer_edge_from_reset: true
  
  CDC_001:
    sync_stages: 2  # Number of synchronizer stages
    add_reset: true
    generate_assertions: true  # Add SVA for CDC
```

---

## Troubleshooting

### Fix Not Generated

**Problem:** No fix suggestion for a violation

**Reasons:**
- Fix generator not implemented for this rule
- Complex code pattern not supported
- Insufficient context to determine fix

**Solution:** Apply fix manually

### Fix Generated But Incorrect

**Problem:** Suggested fix doesn't work

**Reasons:**
- Ambiguous code pattern
- Incorrect inference of clock/reset names
- Edge case not handled

**Solution:** 
1. Report issue with code example
2. Apply correct fix manually
3. Add to exclusions if persistent

### Applied Fix Breaks Code

**Problem:** Code doesn't compile/simulate after auto-fix

**Actions:**
1. Revert from backup: `mv design.sv.bak design.sv`
2. Review the specific fix that broke
3. Report bug with before/after code
4. Add to unsafe fix list

---

## Example Workflows

### New Project (Greenfield)

```bash
# Apply all safe fixes from day 1
veripg-validator --auto-fix --apply-safe --batch rtl/**/*.sv
git add -A && git commit -m "Enforce coding standards"
```

### Legacy Project (Brownfield)

```bash
# Step 1: Generate report of all fixes (don't apply)
veripg-validator --auto-fix rtl/**/*.sv > all_fixes.txt

# Step 2: Review and prioritize

# Step 3: Apply safe fixes to new files only
veripg-validator --auto-fix --apply-safe rtl/new/**/*.sv

# Step 4: Manually apply critical unsafe fixes to legacy code
# (One at a time with testing)
```

### Pre-Commit Hook

```bash
#!/bin/bash
# .git/hooks/pre-commit

# Check for safe auto-fix opportunities
SAFE_FIXES=$(veripg-validator --auto-fix --safe-only --quiet $FILES)

if [ -n "$SAFE_FIXES" ]; then
  echo "Safe fixes available. Apply with:"
  echo "  veripg-validator --auto-fix --apply-safe <files>"
  echo ""
  echo "Or add --no-verify to commit anyway"
  exit 1
fi
```

---

For more information:
- [User Guide](./veripg-validator-user-guide.md)
- [Rules Reference](./veripg-validator-rules-reference.md)
- [Configuration Guide](./veripg-validator-config-guide.md)

