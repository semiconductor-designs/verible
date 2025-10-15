# Phase 4: Enhanced Tooling - Complete Plan

**Duration:** 8-10 weeks  
**Goal:** Complete semantic analysis suite with TypeChecker, CallGraph, and enhanced resolution  
**Status:** Starting now

---

## 🎯 Overview

Phase 4 builds on Phase 3's foundation to deliver a **complete semantic analysis system** for SystemVerilog, comparable to or exceeding industry tools like Slang and Surelog.

**What We'll Build:**
1. **TypeChecker** - Full type validation (3-4 weeks)
2. **CallGraph** - Function/task call analysis (2-3 weeks)
3. **Enhanced Symbol Resolution** - Advanced resolution (2-3 weeks)
4. **Integration & Polish** - Connect everything (1 week)

---

## 📅 Milestone Breakdown

### Week 1-4: TypeChecker Implementation
**Goal:** Complete type validation for SystemVerilog

#### Week 1: TypeChecker Foundation
- Design TypeChecker architecture
- Implement assignment checking
- Basic operator validation
- 10 tests

#### Week 2: Function & Task Validation
- Function argument type checking
- Return type verification
- Task argument validation
- Parameter type checking
- 10 tests

#### Week 3: Advanced Type Checking
- User-defined type validation
- Struct/union member checking
- Array dimension checking
- Cast validation
- 10 tests

#### Week 4: Error Reporting & Integration
- Comprehensive error messages
- Source location tracking
- Suggestion generation
- Integration with TypeInference
- 10 tests

**Week 1-4 Deliverable:** TypeChecker with 40 tests ✅

---

### Week 5-7: CallGraph Generator
**Goal:** Complete function/task call analysis

#### Week 5: CallGraph Foundation
- Design CallGraph architecture
- Function call extraction
- Task call extraction
- Basic graph building
- 8 tests

#### Week 6: Advanced Analysis
- Call hierarchy construction
- Recursive call detection
- Unused function detection
- Cross-module calls
- 8 tests

#### Week 7: Visualization & Integration
- Graph export (DOT format)
- Dead code analysis
- Integration with UnusedDetector
- 8 tests

**Week 5-7 Deliverable:** CallGraph with 24 tests ✅

---

### Week 8-10: Enhanced Resolution & Integration
**Goal:** Complete semantic analysis system

#### Week 8: Enhanced Symbol Resolution
- Hierarchical name resolution
- Cross-module references
- Import/export tracking
- Parameterized types
- 10 tests

#### Week 9: Integration
- Connect TypeChecker + TypeInference
- Connect CallGraph + UnusedDetector
- End-to-end validation
- Performance optimization
- 6 tests

#### Week 10: Polish & Release
- Documentation
- Performance tuning
- Real-world testing (VeriPG)
- Release preparation
- Final testing

**Week 8-10 Deliverable:** Complete system ✅

---

## 📊 Expected Outcomes

### Code Metrics
```
Phase 4 Code:
├─ TypeChecker:       ~1,000 lines (40 tests)
├─ CallGraph:         ~800 lines (24 tests)
├─ Enhanced Resolve:  ~700 lines (10 tests)
└─ Integration:       ~300 lines (6 tests)

Total Phase 4:        ~2,800 lines (80 tests)
```

### Cumulative Totals (Phase 3 + 4)
```
Total Code:           ~5,000 lines
Total Tests:          ~120 tests
Components:           6 major
Quality:              Production-ready
```

---

## 🎯 Success Criteria

### TypeChecker Success
- [✓] Assignment type checking working
- [✓] Function argument validation
- [✓] Operator type compatibility
- [✓] Comprehensive error messages
- [✓] 40 tests passing
- [✓] Integration with TypeInference

### CallGraph Success
- [✓] Function call mapping complete
- [✓] Recursive call detection
- [✓] Unused function detection
- [✓] Graph visualization
- [✓] 24 tests passing
- [✓] Integration with UnusedDetector

### Enhanced Resolution Success
- [✓] Hierarchical resolution working
- [✓] Cross-module references
- [✓] Import/export tracking
- [✓] 10 tests passing
- [✓] Integration tested

### Overall Phase 4 Success
- [✓] All 80 tests passing
- [✓] Zero critical issues
- [✓] Performance acceptable
- [✓] Documentation complete
- [✓] Real-world validation
- [✓] Production-ready

---

## 🚀 Implementation Strategy

### Weekly Structure (Your Preference)
Following the successful Phase 3 pattern:
- Work **weekly**, not daily
- Complete each week's milestone fully
- Document progress each week
- Commit and push at week boundaries
- No stopping mid-week

### Test-Driven Development
- Write tests first (TDD)
- Ensure tests fail initially
- Implement to make tests pass
- Refactor for quality
- Maintain 100% pass rate

### Quality Standards
- Production-ready code
- Comprehensive testing
- Clean architecture
- Well-documented
- Performance-optimized

---

## 📚 Technical Design

### TypeChecker Architecture
```cpp
class TypeChecker {
 public:
  // Main checking APIs
  absl::Status CheckAssignment(const Symbol& lhs, const Symbol& rhs);
  absl::Status CheckFunctionCall(const Symbol& call);
  absl::Status CheckOperator(const Symbol& op);
  
  // Configuration
  struct Options {
    bool strict_mode = false;
    bool warn_implicit_casts = true;
    bool warn_narrowing = true;
  };
  
 private:
  const TypeInference* type_inference_;
  const SymbolTable* symbol_table_;
  std::vector<TypeCheckError> errors_;
};
```

### CallGraph Architecture
```cpp
class CallGraph {
 public:
  // Graph building
  void Build(const SymbolTable& symbol_table);
  
  // Analysis
  std::vector<CallChain> FindRecursiveCalls() const;
  std::vector<std::string> FindUnusedFunctions() const;
  std::vector<std::string> FindDeadCode() const;
  
  // Visualization
  std::string ExportDOT() const;
  std::string ExportJSON() const;
  
 private:
  struct CallNode {
    std::string name;
    std::vector<CallNode*> callees;
    std::vector<CallNode*> callers;
  };
  std::map<std::string, CallNode> nodes_;
};
```

---

## 🎯 Week-by-Week Goals

### Week 1: TypeChecker Foundation ✅
**Deliverable:** Basic type checking working
- Assignment checking
- Basic operator validation
- 10 tests passing
- Clean architecture

### Week 2: Function Validation ✅
**Deliverable:** Function/task checking
- Argument type checking
- Return type verification
- 10 tests passing
- Error messages

### Week 3: Advanced Checking ✅
**Deliverable:** Complex types working
- User-defined types
- Struct/union members
- 10 tests passing
- Cast validation

### Week 4: Error Reporting ✅
**Deliverable:** Comprehensive errors
- Detailed error messages
- Source locations
- Suggestions
- 10 tests passing

### Week 5: CallGraph Foundation ✅
**Deliverable:** Basic graph building
- Call extraction
- Graph construction
- 8 tests passing
- API design

### Week 6: Advanced Analysis ✅
**Deliverable:** Full analysis working
- Call hierarchy
- Recursion detection
- 8 tests passing
- Integration ready

### Week 7: Visualization ✅
**Deliverable:** Graph export working
- DOT format export
- Dead code analysis
- 8 tests passing
- Documentation

### Week 8: Enhanced Resolution ✅
**Deliverable:** Advanced resolution
- Hierarchical resolution
- Cross-module refs
- 10 tests passing
- Clean API

### Week 9: Integration ✅
**Deliverable:** Everything connected
- Full integration
- End-to-end tests
- 6 tests passing
- Performance tuned

### Week 10: Release ✅
**Deliverable:** Production release
- Documentation complete
- VeriPG validation
- Performance verified
- Release ready

---

## 📝 Documentation Plan

### Per-Week Documentation
- Weekly progress report
- Design decisions
- Test results
- Integration notes

### Final Documentation
- Complete API documentation
- User guides
- Integration examples
- Performance benchmarks

---

## ✅ Ready to Start

**Phase 4 Plan:** Complete  
**Timeline:** 10 weeks  
**Goal:** World-class semantic analysis

**Starting with Week 1: TypeChecker Foundation**

Let's build this! 🚀

