# Verible UVM Enhancement Project

**Mission**: Enable complete SystemVerilog codebase analysis (design + verification) by adding comprehensive UVM testbench parsing support to Verible.

**Status**: Phase 1 In Progress (50% complete)  
**Timeline**: 48 weeks (12 months)  
**Methodology**: Test-Driven Development (TDD)

---

## Project Overview

### The Problem

Currently, **89 out of 3,659 OpenTitan SystemVerilog files (2.4%) fail to parse** - and **ALL 89 are UVM testbench files**. Design RTL parsing is excellent (100% success), but verification code is completely unsupported.

### The Solution

Implement full UVM (Universal Verification Methodology) parsing support by addressing **5 technical gaps**:

1. **UVM Macros** 🔴 CRITICAL - Blocks 90% of UVM files
2. **Extern Constraints** 🟠 HIGH - Blocks 50% of UVM files
3. **Type Parameters** 🟠 HIGH - Blocks 30% of UVM files
4. **Distribution Constraints** 🟡 MEDIUM - Blocks 40% of sequences
5. **Complex Macros** 🟡 MEDIUM - Blocks 10% of files

### The Impact

**For OpenTitan**: 97.6% → 100% parse rate (+2.4%)  
**For Industry**: Complete verification methodology analysis  
**For Tooling**: Foundation for UVM-aware static analysis

---

## Key Documents

### Project Planning
- **`/veripg-verible-enhancements.plan.md`** - Complete 48-week plan with detailed phases
- **`UVM_ENHANCEMENT_STATUS.md`** - Real-time tracking of all phases and tasks
- **`UVM_PHASE1_PROGRESS.md`** - Detailed Phase 1 progress report

### Enhancement Requests (from OpenTitan-to-RPG)
- **`VERIBLE_ENHANCEMENT_REQUEST_UVM_SUPPORT.md`** - Technical request for Verible team
- **`VERIPG_ENHANCEMENT_REQUEST_UVM_TESTBENCH_SUPPORT.md`** - Request for VeriPG team
- **`UVM_ENHANCEMENT_REQUEST_PACKAGE_README.md`** - Package overview and usage guide

### Test Infrastructure
- **`verible/verilog/parser/testdata/uvm/README.md`** - Test fixture documentation

---

## Current Status (2025-01-18)

### Phase 1: Test Infrastructure (Weeks 1-2)

**Status**: 50% COMPLETE ✅

**Completed**:
- ✅ Test directory structure created
- ✅ 5 minimal test fixtures created (covering all 5 technical gaps)
- ✅ Documentation written

**In Progress**:
- ⏳ C++ unit test files (0/6 files, 53 tests)
- ⏳ OpenTitan test case extraction (0/10 examples)

**Test Fixtures Created**:
1. `test_uvm_object_utils.sv` - UVM object macros
2. `test_extern_constraint.sv` - Extern constraints with dist operator
3. `test_type_params.sv` - Type parameters in classes
4. `test_distribution.sv` - Distribution constraints
5. `test_macro_in_macro.sv` - Nested macros

---

## Project Timeline

### Completed Phases
None yet - Phase 1 in progress

### Current Phase
**Phase 1** (Weeks 1-2): Test Infrastructure & Fixtures - **50% complete**

### Upcoming Phases
**Phase 2** (Weeks 3-10): UVM Macro Support - **Target: 90% of UVM files parse**  
**Phase 3** (Weeks 11-16): Extern Constraint Support  
**Phase 4** (Weeks 17-22): Type Parameter Support  
**Phase 5** (Weeks 23-26): Distribution Constraint Details  
**Phase 6** (Weeks 27-30): Complex Macro-in-Macro  
**Phase 7** (Weeks 31-36): Kythe UVM Enhancement  
**Phase 8** (Weeks 37-40): Integration Testing  
**Phase 9** (Weeks 41-44): Performance Optimization  
**Phase 10** (Weeks 45-48): Documentation & Release  

### Key Milestones
- **Month 3**: UVM Macros complete - **BIGGEST UNLOCK** (≥80 files parse)
- **Month 5**: Constraints complete
- **Month 8**: Core features complete (macros + constraints + type params)
- **Month 10**: Kythe UVM facts working
- **Month 12**: Release v5.3.0 with full UVM support

---

## Implementation Approach

### Test-Driven Development (TDD)

We follow strict TDD methodology:

1. **Red Phase**: Create failing tests (Phase 1) ← **CURRENT**
2. **Green Phase**: Implement features to make tests pass (Phases 2-7)
3. **Refactor Phase**: Optimize and improve (Phase 9)

### Quality Standards

- **100% test coverage** - All features must have tests
- **No skips** - All tests must pass before proceeding
- **Chase perfection** - Target 98% OpenTitan parse rate (87/89 files)
- **No regressions** - Existing 3,570 design files must continue to parse

---

## Success Criteria

### Minimum (Phases 1-6)
- ✅ Parse ≥80 of 89 OpenTitan UVM files (90%)
- ✅ Core UVM patterns supported (macros, constraints, type params)
- ✅ Performance: <5 min for all 89 files

### Target (Full Implementation)
- ✅ Parse ≥85 of 89 OpenTitan UVM files (95%)
- ✅ All 5 technical gaps addressed
- ✅ Kythe UVM facts extracted
- ✅ Performance: <3 min for all 89 files
- ✅ Memory: <500 MB peak

### Stretch (Perfection)
- ✅ Parse ≥87 of 89 OpenTitan UVM files (98%)
- ✅ Complete UVM 1.2 support
- ✅ Advanced Kythe facts (TLM topology)
- ✅ Performance: <2 min for all 89 files
- ✅ Zero memory leaks

---

## Technical Architecture

### Components Modified

1. **Parser** (`verilog/parser/verilog.y`) - Grammar enhancements
2. **Lexer** (`verilog/parser/verilog.lex`) - New tokens
3. **Preprocessor** (`verilog/preprocessor/`) - Macro expansion
4. **Symbol Table** (`verilog/analysis/symbol-table.cc`) - Type tracking
5. **Kythe Analyzer** (`verilog/analysis/kythe-analyzer.cc`) - UVM facts
6. **CST** (`verilog/CST/verilog-nonterminals.h`) - UVM node types

### New Components

1. **ConstraintAnalyzer** (`verilog/analysis/constraint-analyzer.cc`) - Constraint semantics
2. **UVM Test Fixtures** (`verilog/parser/testdata/uvm/`) - Test cases
3. **UVM Integration Tests** (`verilog/parser/*-uvm-*_test.cc`) - Unit tests

---

## How to Contribute

### For Verible Maintainers

1. Review enhancement request: `VERIBLE_ENHANCEMENT_REQUEST_UVM_SUPPORT.md`
2. Provide feedback on technical approach
3. Review PRs as phases complete
4. Help with grammar conflict resolution

### For VeriPG Team

1. Test intermediate releases on OpenTitan corpus
2. Provide feedback on Kythe UVM fact extraction
3. Validate real-world usability
4. Report bugs and edge cases

### For Community

1. Try Verible on your UVM testbenches
2. Report parsing issues
3. Contribute test cases
4. Provide feedback on usability

---

## Getting Started

### View Current Status
```bash
cat UVM_ENHANCEMENT_STATUS.md
```

### View Test Fixtures
```bash
ls -R verible/verilog/parser/testdata/uvm/
cat verible/verilog/parser/testdata/uvm/README.md
```

### View Phase 1 Progress
```bash
cat UVM_PHASE1_PROGRESS.md
```

### View Full Plan
```bash
cat /veripg-verible-enhancements.plan.md
```

---

## Contact & Collaboration

**Project Lead**: VeriPG Project (via OpenTitan-to-RPG integration)  
**Upstream**: Verible Project (chipsalliance/verible)  
**Requestor**: OpenTitan-to-RPG users  

**Collaboration Model**:
- VeriPG implements workarounds (short-term)
- Verible implements native support (long-term)
- Both teams validate on OpenTitan corpus

---

## References

### Standards
- **IEEE 1800-2017**: SystemVerilog Language Standard
- **IEEE 1800.2-2017**: UVM (Universal Verification Methodology)
- **UVM 1.2 User Guide**: Accellera

### Tools
- **Verible**: https://github.com/chipsalliance/verible
- **VeriPG**: SystemVerilog code analysis (uses Verible)
- **OpenTitan**: Real-world validation corpus (3,659 files)

### Related Work
- **Kythe Integration**: Completed (v5.2.0)
- **Semantic Tool**: verible-verilog-semantic (JSON export)
- **Graph Analysis**: VeriPG FSM/CDC/RDC detection

---

## Acknowledgments

- **OpenTitan-to-RPG Team**: For identifying the need and providing requirements
- **Verible Team**: For excellent RTL parsing foundation
- **VeriPG Team**: For integration and real-world validation
- **UVM Community**: For standardizing verification methodology

---

**Project Start**: 2025-01-18  
**Expected Completion**: 2026-01-18 (12 months)  
**Current Progress**: 1.0% (Phase 1: 50% complete)

---

**Let's make Verible the complete SystemVerilog solution!** 🚀

---

*Last Updated: 2025-01-18*

