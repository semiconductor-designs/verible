# M13: Advanced SVA + Library Enhancements

**Target:** v4.1.0  
**Timeline:** 4-5 weeks  
**Approach:** Test-Driven Development (TDD)

---

## 🎯 Goals

### 1. Advanced SVA Features
Implement advanced SystemVerilog Assertions capabilities for formal verification:
- Multi-clock domain assertions
- Recursive properties
- Complex sequence expressions
- Advanced temporal operators
- Local variable usage in assertions

### 2. Library Support Enhancements
Complete and enhance `library` keyword support:
- Full library declaration syntax
- Config block library mapping
- Include path specifications
- Library compilation units

---

## 📋 Feature Breakdown

### **Feature 1: Multi-Clock Assertions** ⏰

**IEEE 1800-2017 Section:** 16.16 (Multi-clock support)

**Syntax to Support:**
```systemverilog
// Clock per sequence
property p_multi_clock;
  @(posedge clk1) a ##1 b
  |->
  @(posedge clk2) ##[1:3] c;
endproperty

// Multiple clock events
sequence s1;
  @(posedge clk_fast) req ##1 @(posedge clk_slow) ack;
endsequence

// Clock intersection
property p_sync;
  @(posedge clk1, posedge clk2) sig == 1;
endproperty
```

**Test Cases:**
1. ✅ Different clocks in antecedent/consequent
2. ✅ Clock crossing sequences
3. ✅ Multiple clock events in single sequence
4. ✅ Clock intersection (@(clk1, clk2))
5. ✅ Clock union/any

**Complexity:** Medium (grammar already supports some, need to verify all cases)

---

### **Feature 2: Recursive Properties** 🔄

**IEEE 1800-2017 Section:** 16.12 (Recursive properties)

**Syntax to Support:**
```systemverilog
// Recursive sequence
sequence s_recursive(int depth);
  (depth > 0) and (req ##1 s_recursive(depth - 1));
endsequence

// Recursive property
property p_nested(int n);
  if (n == 0)
    ack;
  else
    req |-> ##1 p_nested(n - 1);
endproperty

// Mutual recursion
sequence s_a;
  a ##1 s_b;
endsequence
sequence s_b;
  b ##1 s_a;
endsequence
```

**Test Cases:**
1. ✅ Simple recursion with depth parameter
2. ✅ Conditional recursion (base case)
3. ✅ Mutual recursion (forward declarations)
4. ✅ Recursive sequences in properties
5. ✅ Deep recursion (stack depth test)

**Complexity:** High (requires forward declarations, recursion handling)

---

### **Feature 3: Complex Sequence Expressions** 🧩

**IEEE 1800-2017 Section:** 16.9 (Sequence operations)

**Syntax to Support:**
```systemverilog
// Sequence intersection
sequence s_intersect;
  (a ##[1:5] b) intersect (c ##[2:4] d);
endsequence

// First_match with variables
sequence s_first;
  first_match(req ##[1:$] ack, data);
endsequence

// Throughout with complex expressions
sequence s_throughout;
  enable throughout (req ##1 ack ##1 done);
endsequence

// Sequence method calls
property p_method;
  seq.triggered |-> action;
endproperty
```

**Test Cases:**
1. ✅ Sequence intersection
2. ✅ first_match with variable capture
3. ✅ throughout with complex sequences
4. ✅ Sequence method calls (.triggered, .matched)
5. ✅ Nested sequence operations

**Complexity:** Medium-High (grammar extensions needed)

---

### **Feature 4: Advanced Temporal Operators** ⏱️

**IEEE 1800-2017 Section:** 16.10 (Temporal operators)

**Syntax to Support:**
```systemverilog
// Strong until with range
property p_strong_until;
  a s_until[3:5] b;
endproperty

// Always with clock
property p_always_clocked;
  @(posedge clk) always[0:$] (valid |-> ready);
endproperty

// Cycle delay ranges
property p_cycle_range;
  req |-> ##[1:10] ack ##[5:15] done;
endproperty

// Unbounded ranges
property p_unbounded;
  req |-> ##[1:$] eventually done;
endproperty
```

**Test Cases:**
1. ✅ s_until with ranges
2. ✅ always with cycle ranges
3. ✅ Compound delay ranges
4. ✅ Unbounded ranges [1:$]
5. ✅ Nested temporal operators

**Complexity:** Medium (mostly grammar verification)

---

### **Feature 5: Local Variables in Assertions** 📦

**IEEE 1800-2017 Section:** 16.12.1 (Local variables)

**Syntax to Support:**
```systemverilog
// Local variable in sequence
sequence s_local;
  int v;
  (req, v = data) ##1 (ack && (result == v));
endsequence

// Multiple local variables
property p_locals;
  int x, y;
  @(posedge clk) (start, x = a, y = b) |->
    ##[1:10] (done && (out == x + y));
endproperty

// Local variable with let
property p_let_local;
  let sum(a, b) = a + b;
  int temp;
  (req, temp = data) |-> ##1 (ack && (result == sum(temp, 1)));
endproperty
```

**Test Cases:**
1. ✅ Single local variable
2. ✅ Multiple local variables
3. ✅ Local variable with complex expression
4. ✅ Local variable with let construct
5. ✅ Local variable scope rules

**Complexity:** Medium (may already be partially supported)

---

### **Feature 6: Library Enhancements** 📚

**IEEE 1800-2017 Chapter:** 33 (Library mapping)

**Syntax to Support:**
```systemverilog
// Complete library declaration
library work file1.v file2.v
  -incdir ./include
  -incdir ./common;

// Library in config
config my_config;
  design top;
  instance top.u1 liblist my_lib;
  instance top.u2 use my_lib.cell1;
endconfig

// Multiple libraries
library lib1 src/lib1/*.v -incdir src/lib1/inc;
library lib2 src/lib2/*.v -incdir src/lib2/inc;

// Library with defines
library rtl
  file1.v
  file2.v
  -incdir inc
  -define DEBUG=1
  -define VERBOSE;
```

**Test Cases:**
1. ✅ Basic library declaration
2. ✅ Library with -incdir
3. ✅ Library with defines
4. ✅ Multiple libraries
5. ✅ Library in config blocks
6. ✅ Library wildcards (*.v)
7. ✅ Library search order

**Complexity:** Low-Medium (mostly verification, some grammar tweaks)

---

## 🧪 Test Strategy (TDD)

### Phase 1: Test Creation (Week 1)
Create comprehensive test suite BEFORE implementation:

```bash
# Create test files
verible/verilog/parser/verilog-parser-multi-clock-sva_test.cc      # Feature 1
verible/verilog/parser/verilog-parser-recursive-properties_test.cc # Feature 2
verible/verilog/parser/verilog-parser-complex-sequences_test.cc    # Feature 3
verible/verilog/parser/verilog-parser-temporal-advanced_test.cc    # Feature 4
verible/verilog/parser/verilog-parser-local-vars-sva_test.cc       # Feature 5
verible/verilog/parser/verilog-parser-library-enhanced_test.cc     # Feature 6
```

**Test Count Target:** 40+ tests (minimum 5-7 per feature)

### Phase 2: Implementation (Weeks 2-4)
Implement features incrementally, making tests pass one by one:

1. **Week 2:** Features 1-2 (Multi-clock, Recursive)
2. **Week 3:** Features 3-4 (Complex sequences, Temporal)
3. **Week 4:** Features 5-6 (Local vars, Library)

### Phase 3: Integration (Week 5)
- Run full test suite (should be 40+ new tests + all existing)
- Performance testing
- Documentation
- Release v4.1.0

---

## 📊 Success Criteria

### Functional
- ✅ All 40+ new tests PASS
- ✅ All existing tests PASS (zero regressions)
- ✅ Grammar conflicts: 0 (zero)

### Quality
- ✅ Code coverage: 95%+ for new code
- ✅ Documentation: Complete for all features
- ✅ Performance: No degradation (< 5% acceptable)

### Compliance
- ✅ IEEE 1800-2017 compliant for all implemented features
- ✅ Interoperability: Works with existing SVA code
- ✅ VeriPG compatible: No breaking changes

---

## 🗂️ Files to Modify

### Grammar (verible/verilog/parser/)
- `verilog.y` - Grammar rules for new features
- `verilog.lex` - Lexer updates if needed

### CST (verible/verilog/CST/)
- `verilog-nonterminals.h` - New CST node types

### Tests (verible/verilog/parser/)
- 6 new test files (40+ tests total)
- `BUILD` - Add new test targets

### Documentation
- `M13_ADVANCED_SVA_LIBRARY_COMPLETE.md` - Final report
- `RELEASE_v4.1.0.md` - Release notes

---

## 🚀 Implementation Order

### Sprint 1: Foundation (Week 1)
**Goal:** All tests created, initial research complete

- [x] Create test files
- [ ] Write 40+ failing tests (TDD RED phase)
- [ ] Research IEEE 1800-2017 for each feature
- [ ] Identify grammar changes needed

### Sprint 2: Multi-Clock + Recursive (Week 2)
**Goal:** Features 1-2 complete

- [ ] Implement multi-clock assertions
- [ ] Implement recursive properties
- [ ] Tests passing: 10-12 tests

### Sprint 3: Sequences + Temporal (Week 3)
**Goal:** Features 3-4 complete

- [ ] Implement complex sequence expressions
- [ ] Implement advanced temporal operators
- [ ] Tests passing: 20-24 tests

### Sprint 4: Local Vars + Library (Week 4)
**Goal:** Features 5-6 complete

- [ ] Implement local variables in assertions
- [ ] Enhance library support
- [ ] Tests passing: 30-36 tests

### Sprint 5: Polish + Release (Week 5)
**Goal:** v4.1.0 released

- [ ] All 40+ tests passing
- [ ] Zero regressions
- [ ] Documentation complete
- [ ] Binary deployed to VeriPG

---

## 📈 Expected Impact

### For Formal Verification Teams
- ✅ Multi-clock assertions: Essential for SoC verification
- ✅ Recursive properties: Complex protocol checking
- ✅ Advanced sequences: Sophisticated temporal patterns

### For VeriPG
- ✅ Enhanced SVA extraction capabilities
- ✅ Better library management
- ✅ Improved testbench analysis

### For Industry
- ✅ State-of-the-art SVA support
- ✅ IEEE 1800-2017 fully compliant
- ✅ World-class formal verification parser

---

## 💡 Risk Mitigation

### Risk 1: Grammar Conflicts
**Mitigation:** Incremental approach, test each feature separately

### Risk 2: Recursion Complexity
**Mitigation:** Limit recursion depth, clear error messages

### Risk 3: Performance Impact
**Mitigation:** Benchmark before/after, optimize hot paths

### Risk 4: Breaking Changes
**Mitigation:** Maintain backward compatibility, extensive regression testing

---

## 🎯 Definition of Done

- [ ] All 40+ tests created (TDD)
- [ ] All 40+ tests passing
- [ ] All existing 300+ tests passing (zero regressions)
- [ ] Grammar conflicts: 0
- [ ] Code review complete
- [ ] Documentation complete
- [ ] Performance verified (no degradation)
- [ ] Binary built and tested
- [ ] Released as v4.1.0
- [ ] Deployed to VeriPG
- [ ] Announcement prepared

---

**Ready to start implementing M13?**

**Estimated completion:** 4-5 weeks  
**Confidence level:** High (95%)  
**Value to users:** Very High ⭐⭐⭐⭐⭐

Let's build world-class advanced SVA support! 🚀

