# 🎯 UVM User Guide - Start Here!

**Verible v5.3.0 - Complete UVM Support**  
**Last Updated**: October 19, 2025  
**Status**: Production Ready ✅

---

## 📍 Quick Navigation

### For New Users: Start Here! 👋

1. **[README.md](README.md#uvm-support-v530)** (5 minutes)
   - Overview of UVM support
   - Quick start example
   - Feature highlights

2. **[VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md)** (15 minutes)
   - 5 complete, copy-paste ready examples
   - Real-world patterns
   - Python integration scripts

3. **[VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md#-uvm-testbench-analysis)** (10 minutes)
   - Section 4: UVM Testbench Analysis
   - Troubleshooting guide
   - Best practices

---

## 📚 Complete Documentation Library

### 1. Quick Start & Overview

| Document | Purpose | Read Time |
|----------|---------|-----------|
| **[README.md](README.md#uvm-support-v530)** | Project overview + UVM section | 5 min |
| **[PROJECT_COMPLETE.md](PROJECT_COMPLETE.md)** | Project summary & metrics | 10 min |

### 2. User Guides (Most Important!)

| Document | Purpose | Read Time |
|----------|---------|-----------|
| **[VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md)** ⭐ | 5 practical examples with code | 15 min |
| **[VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md)** ⭐ | Integration guide (see Section 4) | 20 min |
| **[UVM_CAPABILITIES_REALITY.md](UVM_CAPABILITIES_REALITY.md)** | Complete feature list | 15 min |

### 3. Release Information

| Document | Purpose | Read Time |
|----------|---------|-----------|
| **[RELEASE_NOTES_v5.3.0.md](RELEASE_NOTES_v5.3.0.md)** | Complete release notes | 20 min |
| **[BINARY_RELEASE_v5.3.0.md](BINARY_RELEASE_v5.3.0.md)** | Binary deployment info | 10 min |
| **[CHANGELOG.md](CHANGELOG.md)** | Version history | 5 min |

### 4. Technical Details

| Document | Purpose | Read Time |
|----------|---------|-----------|
| **[UVM_ENHANCEMENT_STATUS.md](UVM_ENHANCEMENT_STATUS.md)** | Project status & test results | 10 min |
| **[OPENTITAN_PARSING_ANALYSIS.md](OPENTITAN_PARSING_ANALYSIS.md)** | OpenTitan validation results | 15 min |
| **[DEEP_NESTING_FIX_COMPLETE.md](DEEP_NESTING_FIX_COMPLETE.md)** | Deep nesting bug fix details | 10 min |

### 5. Project History

| Document | Purpose | Read Time |
|----------|---------|-----------|
| **[PLAN_REVISION_SUMMARY.md](PLAN_REVISION_SUMMARY.md)** | The 260x efficiency story | 20 min |
| **[PHASE_2_COMPLETE.md](PHASE_2_COMPLETE.md)** | Integration guide phase | 5 min |
| **[PHASE_3_COMPLETE.md](PHASE_3_COMPLETE.md)** | Release prep phase | 5 min |
| **[PHASE_4_COMPLETE.md](PHASE_4_COMPLETE.md)** | Git release phase | 5 min |
| **[PHASE_5_COMPLETE.md](PHASE_5_COMPLETE.md)** | Archive phase | 5 min |

---

## 🚀 Quick Start Guide

### Step 1: Check Your Binary (30 seconds)

```bash
# Verify you have v5.3.0
verible-verilog-syntax --version

# Expected output:
# Version v5.1.0-2-g581e9e37 (or later)
```

### Step 2: Parse Your First UVM File (2 minutes)

```bash
# Create a simple UVM component
cat > my_driver.sv << 'EOF'
`include "uvm_macros.svh"
import uvm_pkg::*;

class my_driver extends uvm_driver #(my_transaction);
  `uvm_component_utils(my_driver)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
EOF

# Parse it with UVM support
verible-verilog-syntax \
  --include_paths=third_party/uvm/src \
  my_driver.sv

# Should complete without errors! ✅
```

### Step 3: Extract Kythe Facts (3 minutes)

```bash
# Parse and extract variable references
verible-verilog-semantic \
  --include_kythe \
  --include_paths=third_party/uvm/src \
  my_driver.sv > output.json

# View the JSON output
cat output.json | python -m json.tool | less
```

### Step 4: Read the Examples (15 minutes)

Open **[VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md)** and follow:
- Example 1: Simple UVM Component
- Example 2: Parse with Package Context
- Example 3: Extract UVM Hierarchies

---

## 🎯 Use Case Based Navigation

### "I want to parse UVM testbenches"

1. Read: [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - Example 1
2. Command:
   ```bash
   verible-verilog-syntax \
     --include_paths=third_party/uvm/src \
     my_testbench.sv
   ```

### "I want to extract UVM hierarchies"

1. Read: [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - Example 3
2. Read: [VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md) - Section 4

### "I want to integrate with VeriPG"

1. Read: [VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md) - Section 4
2. Read: [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - All examples
3. Read: [BINARY_RELEASE_v5.3.0.md](BINARY_RELEASE_v5.3.0.md)

### "I want to understand what's supported"

1. Read: [UVM_CAPABILITIES_REALITY.md](UVM_CAPABILITIES_REALITY.md)
2. Read: [RELEASE_NOTES_v5.3.0.md](RELEASE_NOTES_v5.3.0.md) - "What Works" section

### "I'm getting errors"

1. Read: [VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md) - Troubleshooting section
2. Read: [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - Troubleshooting section
3. Check: [OPENTITAN_PARSING_ANALYSIS.md](OPENTITAN_PARSING_ANALYSIS.md) for known patterns

### "I want to batch process files"

1. Read: [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - Example 5
2. Use the provided bash and Python scripts

---

## 📖 Recommended Reading Order

### For VeriPG Integration (1 hour total)

1. **[README.md](README.md#uvm-support-v530)** (5 min) - Overview
2. **[VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md)** (20 min) - Practical examples
3. **[VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md#-uvm-testbench-analysis)** (15 min) - Integration details
4. **[UVM_CAPABILITIES_REALITY.md](UVM_CAPABILITIES_REALITY.md)** (10 min) - Feature list
5. **[BINARY_RELEASE_v5.3.0.md](BINARY_RELEASE_v5.3.0.md)** (10 min) - Binary info

### For Technical Understanding (1.5 hours total)

1. **[UVM_CAPABILITIES_REALITY.md](UVM_CAPABILITIES_REALITY.md)** (15 min)
2. **[RELEASE_NOTES_v5.3.0.md](RELEASE_NOTES_v5.3.0.md)** (20 min)
3. **[DEEP_NESTING_FIX_COMPLETE.md](DEEP_NESTING_FIX_COMPLETE.md)** (10 min)
4. **[OPENTITAN_PARSING_ANALYSIS.md](OPENTITAN_PARSING_ANALYSIS.md)** (15 min)
5. **[UVM_ENHANCEMENT_STATUS.md](UVM_ENHANCEMENT_STATUS.md)** (10 min)
6. **[PLAN_REVISION_SUMMARY.md](PLAN_REVISION_SUMMARY.md)** (20 min) - The story

---

## 🎓 Learning Path

### Beginner (30 minutes)
1. Quick Start Guide (this page)
2. [README.md](README.md#uvm-support-v530)
3. [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - Example 1

### Intermediate (2 hours)
1. All Beginner content
2. [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - All examples
3. [VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md) - Section 4
4. [UVM_CAPABILITIES_REALITY.md](UVM_CAPABILITIES_REALITY.md)

### Advanced (4 hours)
1. All Intermediate content
2. [RELEASE_NOTES_v5.3.0.md](RELEASE_NOTES_v5.3.0.md) - Complete
3. [OPENTITAN_PARSING_ANALYSIS.md](OPENTITAN_PARSING_ANALYSIS.md)
4. [DEEP_NESTING_FIX_COMPLETE.md](DEEP_NESTING_FIX_COMPLETE.md)
5. [PLAN_REVISION_SUMMARY.md](PLAN_REVISION_SUMMARY.md)

---

## 🔍 Key Features Supported

### ✅ Complete UVM Grammar
- Type parameters: `class fifo #(type T = int)`
- Extern constraints: `extern constraint my_range;`
- Distribution constraints: `x dist { [0:10] := 50 }`
- All constraint operators: `inside`, `solve...before`, `->`

### ✅ Deep Nesting
- Macro propagation through any depth (3+ levels)
- Tested and verified

### ✅ UVM Library
- UVM-Core 2020.3.1 (IEEE 1800.2-2017)
- Integrated as submodule at `third_party/uvm/`

### ✅ Production Validated
- **136/136 tests passing** (100%)
- **2,094/2,108 OpenTitan files** (99.3%)
- Zero performance impact

---

## 💡 Common Questions

**Q: Where do I start?**  
A: Follow the Quick Start Guide on this page (5 minutes)

**Q: How do I integrate with VeriPG?**  
A: Read [VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md) Section 4

**Q: What examples are available?**  
A: See [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) - 5 complete examples

**Q: What UVM features are supported?**  
A: See [UVM_CAPABILITIES_REALITY.md](UVM_CAPABILITIES_REALITY.md) - 100% grammar coverage

**Q: I'm getting "preprocessing error"?**  
A: See troubleshooting in [VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md#troubleshooting-uvm-files)

**Q: How do I parse package files?**  
A: See [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) Example 2

---

## 🎉 Success Stories

### OpenTitan Validation
- **2,094/2,108 files** (99.3% success)
- Complete design + verification testbenches
- Deep nesting up to 5+ levels

### Test Coverage
- **136/136 tests passing** (100%)
- 124 UVM parser tests
- 2 deep nesting tests
- 10 include file tests

---

## 📞 Support

### Documentation Issues
- Check [VERIPG_INTEGRATION_GUIDE.md](VERIPG_INTEGRATION_GUIDE.md) Troubleshooting
- Check [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md) Troubleshooting

### Feature Questions
- See [UVM_CAPABILITIES_REALITY.md](UVM_CAPABILITIES_REALITY.md)
- See [RELEASE_NOTES_v5.3.0.md](RELEASE_NOTES_v5.3.0.md)

---

## 🚀 Next Steps

1. ✅ Read this index (you're here!)
2. → Follow Quick Start Guide above
3. → Read [VERIPG_UVM_USAGE_EXAMPLES.md](VERIPG_UVM_USAGE_EXAMPLES.md)
4. → Try examples on your UVM code
5. → Integrate into your workflow

---

**Version**: v5.3.0  
**Status**: Production Ready ✅  
**Last Updated**: October 19, 2025

**Ready to parse UVM? Start with the Quick Start Guide above! 🎯**

