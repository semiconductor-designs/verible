# M14: Complete Remaining Niche Features - Final 100% Coverage

**Target:** v4.2.0  
**Timeline:** 3 weeks (feature-by-feature TDD)  
**Goal:** Zero feature gaps, absolute completeness

---

## 🎯 Overview

While Verible already has 99%+ coverage, there are 3 niche feature areas with gaps:

1. **Advanced `randsequence`** - Production system incomplete
2. **DPI Enhancements** - DPI 2.0 features missing
3. **Specify Completion** - Advanced timing checks

These are rarely used but important for 100% completeness claim.

---

## 📅 Week 1: Advanced `randsequence` (Days 1-5)

### Current Status
- ✅ Basic `randsequence` keyword recognized
- ✅ Simple productions parse
- ❌ Weighted productions not fully supported
- ❌ `rand join` not implemented
- ❌ Production arguments incomplete
- ❌ `break`/`return` in productions partial

### Target Features

#### 1. Weighted Productions
```systemverilog
randsequence(main)
  main : first := 5 | second := 3 | third := 2;
  first : { $display("first"); };
  second : { $display("second"); };
  third : { $display("third"); };
endsequence
```

#### 2. Production Arguments
```systemverilog
randsequence(main)
  main : add(1, 2);
  add(int x, int y) : { $display("sum=%0d", x+y); };
endsequence
```

#### 3. Case Productions
```systemverilog
randsequence(main)
  main : case (mode)
    0: mode0;
    1: mode1;
    default: mode_default;
  endcase;
endsequence
```

#### 4. Control Flow
```systemverilog
randsequence(main)
  main : repeat(5) action | if (done) finish;
  action : { count++; if (count > 10) break; };
endsequence
```

#### 5. rand join
```systemverilog
randsequence(main)
  main : rand join seq1 seq2 seq3;
  seq1 : { $display("seq1"); };
  seq2 : { $display("seq2"); };
  seq3 : { $display("seq3"); };
endsequence
```

### Tests to Create (10 tests)

**File:** `verible/verilog/parser/verilog-parser-randsequence-advanced_test.cc`

1. ✅ Basic randsequence (verify existing)
2. Weighted productions with `:=`
3. Multiple weights in one production
4. Production with arguments
5. Case statement in production
6. if-else in production
7. repeat in production
8. rand join (parallel productions)
9. break statement in production
10. return statement in production

### Grammar Enhancement Needed

**Location:** `verilog.y` around line 8500-8600

```yacc
randsequence_production
  : GenericIdentifier ':' production_item_list ';'
  | GenericIdentifier '(' tf_port_list_opt ')' ':' production_item_list ';'
  ;

production_item_list
  : production_item_list '|' production_item
  | production_item
  ;

production_item
  : production_reference weight_spec_opt
  | case_randsequence_item
  | TK_rand TK_join production_list
  | control_statement
  ;

weight_spec
  : TK_COLONEQ expression
  ;
```

### Implementation Steps
1. Check existing `randsequence` grammar (line ~8500)
2. Add weighted production support (`:=` operator)
3. Add production arguments (function-like parameters)
4. Add `rand join` support
5. Enhance control flow (`break`, `return`, `case`)
6. Add CST nodes: `kRandsequenceProduction`, `kProductionWeight`
7. Create 10 tests
8. Verify zero regressions

---

## 📅 Week 2: DPI Enhancements (Days 1-5)

### Current Status
- ✅ Basic DPI `import`/`export` working
- ✅ `context` keyword recognized
- ✅ `pure` keyword recognized
- ❌ DPI-C 2.0 open arrays incomplete
- ❌ Advanced type mappings partial
- ❌ DPI task/function edge cases

### Target Features

#### 1. DPI-C Open Arrays
```systemverilog
import "DPI-C" function void process_array(
  input int arr[],
  input int size
);
```

#### 2. Context Import/Export
```systemverilog
import "DPI-C" context function void context_func();
export "DPI-C" context task context_task;
```

#### 3. Pure Functions
```systemverilog
import "DPI-C" pure function int pure_calc(input int x);
```

#### 4. Advanced Type Mappings
```systemverilog
import "DPI-C" function void handle_chandle(
  input chandle ptr
);

import "DPI-C" function void handle_string(
  input string str
);
```

#### 5. DPI Return Types
```systemverilog
import "DPI-C" function string get_name();
import "DPI-C" function chandle create_handle();
import "DPI-C" function void return_void();
```

### Tests to Create (8 tests)

**File:** `verible/verilog/parser/verilog-parser-dpi-enhanced_test.cc`

1. ✅ Basic DPI import (verify existing)
2. DPI with open array `arr[]`
3. DPI context function
4. DPI context task export
5. DPI pure function
6. DPI with chandle type
7. DPI with string type
8. DPI function returning string

### Grammar Enhancement Needed

**Location:** `verilog.y` around line 5900-6000

```yacc
dpi_import_export
  : TK_import TK_StringLiteral dpi_spec_string_opt
    dpi_function_proto ';'
  | TK_export TK_StringLiteral dpi_function_ident_opt ';'
  ;

dpi_function_proto
  : TK_context_opt TK_function dpi_function_return_type_opt
    GenericIdentifier '(' dpi_port_list_opt ')'
  | TK_context_opt TK_task GenericIdentifier '(' dpi_port_list_opt ')'
  ;

context_opt
  : TK_context
  | /* empty */
  ;

pure_opt
  : TK_pure
  | /* empty */
  ;
```

### Implementation Steps
1. Check existing DPI grammar (line ~5900)
2. Verify `context` keyword handling
3. Verify `pure` keyword handling
4. Add open array syntax `[]` in port lists
5. Enhance type mapping (chandle, string returns)
6. Create 8 tests
7. Verify zero regressions

---

## 📅 Week 3: Specify Block Completion (Days 1-5)

### Current Status
- ✅ Basic specify blocks working
- ✅ Path delays supported
- ✅ `pulsestyle_onevent` / `pulsestyle_ondetect` (M9)
- ❌ `showcancelled` / `noshowcancelled` not implemented
- ❌ Advanced timing checks incomplete
- ❌ Conditional path delays partial

### Target Features

#### 1. showcancelled / noshowcancelled
```systemverilog
specify
  showcancelled (a => b);
  noshowcancelled (c => d);
endspecify
```

#### 2. Advanced Setup/Hold
```systemverilog
specify
  $setuphold(posedge clk, data, 1.5, 2.0);
  $recrem(posedge rst, posedge clk, 1.0, 1.5);
endspecify
```

#### 3. Conditional Path Delays
```systemverilog
specify
  if (sel == 0) (a => out) = 1.2;
  if (sel == 1) (b => out) = 2.3;
endspecify
```

#### 4. Edge-Sensitive Paths
```systemverilog
specify
  (posedge clk => (q +: d)) = (1.5, 2.0);
  (negedge clk => (q -: d)) = (1.8, 2.2);
endspecify
```

#### 5. State-Dependent Paths
```systemverilog
specify
  if (mode) (a *> b) = 1.5;
  ifnone (a *> b) = 2.0;
endspecify
```

### Tests to Create (10 tests)

**File:** `verible/verilog/parser/verilog-parser-specify-complete_test.cc`

1. ✅ Basic specify block (verify existing)
2. showcancelled path
3. noshowcancelled path
4. $setuphold timing check
5. $recrem timing check
6. Conditional path with if
7. Edge-sensitive path (posedge/negedge)
8. Polarity operators (+:, -:)
9. State-dependent with ifnone
10. Multiple specify blocks

### Grammar Enhancement Needed

**Location:** `verilog.y` around line 6200-6400

```yacc
specify_path_declaration
  : showcancelled_opt path_description '=' path_delay_value ';'
  ;

showcancelled_opt
  : TK_showcancelled
  | TK_noshowcancelled
  | /* empty */
  ;

edge_identifier_opt
  : TK_posedge
  | TK_negedge
  | /* empty */
  ;

polarity_operator_opt
  : TK_PLUSCOLON    /* +: */
  | TK_MINUSCOLON   /* -: */
  | /* empty */
  ;
```

### Implementation Steps
1. Check existing specify grammar (line ~6200)
2. Add `showcancelled` / `noshowcancelled` tokens and rules
3. Verify edge-sensitive paths (posedge/negedge in paths)
4. Add polarity operators `+:` and `-:`
5. Enhance conditional paths with `if` / `ifnone`
6. Create 10 tests
7. Verify zero regressions

---

## 📊 Success Criteria

### Quantitative
- ✅ All 28 new tests passing (10 + 8 + 10)
- ✅ Zero regressions (340+ existing tests)
- ✅ Zero grammar conflicts
- ✅ 100% feature completeness (no known gaps)

### Qualitative
- ✅ IEEE 1800-2017 100% coverage
- ✅ All niche features supported
- ✅ World-class parser claim validated
- ✅ Production-ready quality

---

## 🔧 Grammar Changes Summary

### New Tokens Needed
```yacc
%token TK_showcancelled "showcancelled"
%token TK_noshowcancelled "noshowcancelled"
/* Other tokens likely already exist */
```

### New CST Nodes
```cpp
// In verilog-nonterminals.h
kRandsequenceProduction,
kProductionWeight,
kRandJoin,
kShowcancelledPath,
kDPIOpenArray,
```

### Files to Modify
1. **verilog.y** - Grammar enhancements (3 sections)
2. **verilog.lex** - Add `showcancelled`, `noshowcancelled` tokens
3. **verilog-nonterminals.h** - Add 5 new CST nodes
4. **BUILD** - Add 3 new test targets

### New Test Files
1. `verilog-parser-randsequence-advanced_test.cc` (10 tests)
2. `verilog-parser-dpi-enhanced_test.cc` (8 tests)
3. `verilog-parser-specify-complete_test.cc` (10 tests)

---

## 📈 Impact Assessment

### User Impact
- **High-End Verification Teams:** Advanced randsequence useful
- **Simulation Interop:** DPI 2.0 enables latest standards
- **Timing Analysis:** Complete specify for STA tools

### VeriPG Impact
- **Low:** These features rarely used in practice
- **Symbolic:** Demonstrates absolute completeness

### Verible Positioning
- **Before:** 99% coverage, world-class
- **After:** 100% coverage, absolutely complete
- **Marketing:** "The only parser with 100% IEEE 1800-2017 coverage"

---

## 🚀 Release Plan

### Week 1 Checkpoint
- Commit: `randsequence` complete (10/10 tests)
- Tag: `v4.2.0-alpha1`

### Week 2 Checkpoint
- Commit: DPI enhanced (18/18 tests cumulative)
- Tag: `v4.2.0-alpha2`

### Week 3 Final
- Commit: All complete (28/28 tests)
- Tag: `v4.2.0` - "100% Feature Complete"
- Release notes: "Absolute IEEE 1800-2017 completeness"

### Deployment
1. Build optimized binary
2. Push to GitHub with detailed release notes
3. Deploy to VeriPG
4. Update documentation with "100% Complete" badge

---

## 💡 Implementation Strategy

### TDD Approach (Proven Successful)
1. **RED:** Write all tests first (expect failures)
2. **GREEN:** Implement grammar to pass tests
3. **REFACTOR:** Clean up, document, optimize

### Quality Gates
- Every commit must pass all 340+ existing tests
- Zero grammar conflicts at all times
- All new tests must have IEEE references
- Documentation updated incrementally

### Risk Mitigation
- These are niche features, low user impact if delayed
- Can ship any week's completion as incremental release
- Main parser already production-ready (v4.1.0)

---

## 📝 Documentation Deliverables

### Per-Week Docs
- `M14_WEEK1_RANDSEQUENCE.md` - randsequence details
- `M14_WEEK2_DPI.md` - DPI enhancements
- `M14_WEEK3_SPECIFY.md` - specify completion

### Final Docs
- `M14_COMPLETE.md` - All 3 features summary
- `RELEASE_v4.2.0.md` - Release notes
- Update `README.md` - Add "100% IEEE 1800-2017 Coverage" badge

---

## ✅ Ready to Start?

**M14 Implementation Plan Complete!**

- ✅ 3 weeks, 3 features
- ✅ 28 new tests planned
- ✅ TDD approach defined
- ✅ Success criteria clear
- ✅ Release strategy ready

**Shall we begin with Week 1: Advanced `randsequence`?**

