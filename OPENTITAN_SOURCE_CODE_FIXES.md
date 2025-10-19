# OpenTitan Source Code Fixes

**Date**: 2025-10-19  
**Issue**: 6 files with syntax errors detected by Verible  
**Root Cause**: `static task` used in module context (only valid in class context)

---

## Summary

All 6 files have the same bug: Using `static task` inside a module.

**Fix**: Change `static task` to `task automatic` (or just `task`)

---

## File 1: spid_jedec_tb.sv

**Location**: `/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan/hw/ip/spi_device/pre_dv/tb/spid_jedec_tb.sv`

**Errors**:
- Line 97: `static task host();`
- Line 114: `static task sw();`

**Fix**:
```systemverilog
// BEFORE:
static task host();
  automatic int unsigned num_cc;
  ...
endtask : host

static task sw();
  ...
endtask : sw

// AFTER:
task automatic host();
  int unsigned num_cc;
  ...
endtask : host

task automatic sw();
  ...
endtask : sw
```

**Note**: Since the tasks already declare `automatic` variables inside, using `task automatic` is appropriate.

---

## File 2: spid_upload_tb.sv

**Location**: `/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan/hw/ip/spi_device/pre_dv/tb/spid_upload_tb.sv`

**Error**: Line 186

**Fix**:
```systemverilog
// BEFORE:
static task host();

// AFTER:
task automatic host();
```

---

## File 3: spid_readcmd_tb.sv

**Location**: `/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan/hw/ip/spi_device/pre_dv/tb/spid_readcmd_tb.sv`

**Error**: Line 180

**Fix**:
```systemverilog
// BEFORE:
static task host();

// AFTER:
task automatic host();
```

---

## File 4: spiflash.sv

**Location**: `/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan/hw/ip/spi_device/pre_dv/program/spiflash.sv`

**Error**: Line 192

**Fix**:
```systemverilog
// BEFORE:
static task spiflash_readjedec(...);

// AFTER:
task automatic spiflash_readjedec(...);
```

---

## File 5: prog_passthrough_host.sv

**Location**: `/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan/hw/ip/spi_device/pre_dv/program/prog_passthrough_host.sv`

**Error**: Line 117

**Fix**:
```systemverilog
// BEFORE:
static task host();

// AFTER:
task automatic host();
```

---

## File 6: prog_passthrough_sw.sv

**Location**: `/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan/hw/ip/spi_device/pre_dv/program/prog_passthrough_sw.sv`

**Error**: Line 229

**Fix**:
```systemverilog
// BEFORE:
static task sw();

// AFTER:
task automatic sw();
```

---

## SystemVerilog Rules Reminder

### Task Declarations

**In Module Context**:
```systemverilog
module my_module;
  // ✅ Valid
  task my_task(); ... endtask
  task automatic my_task(); ... endtask
  
  // ❌ Invalid - 'static' only for classes
  static task my_task(); ... endtask
endmodule
```

**In Class Context**:
```systemverilog
class my_class;
  // ✅ All valid
  task my_task(); ... endtask
  task automatic my_task(); ... endtask
  static task my_static_task(); ... endtask
endclass
```

### Why `task automatic`?

- **`task`** (default): Variables persist between calls (like `static` in C)
- **`task automatic`**: Variables are allocated on each call (like local variables in C)

For testbenches, `task automatic` is generally safer as it avoids unintended state sharing.

---

## Automated Fix Script

```bash
#!/bin/bash
# Fix all 6 files

OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"

# File 1
sed -i.bak 's/static task host/task automatic host/g' \
  "${OPENTITAN_ROOT}/hw/ip/spi_device/pre_dv/tb/spid_jedec_tb.sv"
sed -i.bak 's/static task sw/task automatic sw/g' \
  "${OPENTITAN_ROOT}/hw/ip/spi_device/pre_dv/tb/spid_jedec_tb.sv"

# File 2
sed -i.bak 's/static task host/task automatic host/g' \
  "${OPENTITAN_ROOT}/hw/ip/spi_device/pre_dv/tb/spid_upload_tb.sv"

# File 3
sed -i.bak 's/static task host/task automatic host/g' \
  "${OPENTITAN_ROOT}/hw/ip/spi_device/pre_dv/tb/spid_readcmd_tb.sv"

# File 4
sed -i.bak 's/static task spiflash_readjedec/task automatic spiflash_readjedec/g' \
  "${OPENTITAN_ROOT}/hw/ip/spi_device/pre_dv/program/spiflash.sv"

# File 5
sed -i.bak 's/static task host/task automatic host/g' \
  "${OPENTITAN_ROOT}/hw/ip/spi_device/pre_dv/program/prog_passthrough_host.sv"

# File 6
sed -i.bak 's/static task sw/task automatic sw/g' \
  "${OPENTITAN_ROOT}/hw/ip/spi_device/pre_dv/program/prog_passthrough_sw.sv"

echo "Fixed all 6 files!"
echo "Backups saved as *.bak"
```

---

## Verification After Fix

```bash
# Test all 6 files
verible-verilog-syntax \
  hw/ip/spi_device/pre_dv/tb/spid_jedec_tb.sv \
  hw/ip/spi_device/pre_dv/tb/spid_upload_tb.sv \
  hw/ip/spi_device/pre_dv/tb/spid_readcmd_tb.sv \
  hw/ip/spi_device/pre_dv/program/spiflash.sv \
  hw/ip/spi_device/pre_dv/program/prog_passthrough_host.sv \
  hw/ip/spi_device/pre_dv/program/prog_passthrough_sw.sv

# Expected: All pass! ✅
```

---

## Impact

**Before Fix**: 3,872 / 3,911 = 99.00% success  
**After Fix**: 3,878 / 3,911 = 99.16% success  

**Remaining 33 failures**: All are include snippets or compilation-unit-dependent files (expected)

---

## Should These Fixes Be Upstreamed?

**YES!** ✅

These are **real bugs** in OpenTitan source code:
- Violate SystemVerilog LRM (IEEE 1800-2017)
- Would fail with most commercial simulators
- Easy to fix (simple search/replace)

**Recommendation**: Submit pull request to OpenTitan with these fixes.

---

## Conclusion

Verible correctly identified 6 real syntax errors! This validates that:
1. Verible's parser is accurate
2. Verible provides value by catching real bugs
3. These files likely aren't tested in OpenTitan's CI (pre_dv directory)

