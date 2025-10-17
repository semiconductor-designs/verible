# Phase 2: Cross-Module Analysis - Comprehensive Plan

**Timeline**: 4 weeks (Weeks 6-9, Days 26-45)  
**Approach**: TDD (Test-Driven Development)  
**Philosophy**: "No hurry. Perfection! TDD."  
**Goal**: Multi-file symbol resolution and hierarchical validation

---

## 🎯 Phase 2 Objectives

Building on Phase 1's solid type system foundation, Phase 2 adds:

1. **Multi-file reference validation** - Verify cross-file symbol references
2. **Port connection type checking** - Validate module instantiation ports
3. **Interface & modport validation** - Check interface connections
4. **Parameter propagation tracking** - Track parameters across hierarchy
5. **Hierarchical type checking** - Validate types through module hierarchy

---

## 📋 Current State Assessment

### What We Have (Phase 1)
- ✅ Type system (inference, compatibility, checking)
- ✅ Symbol table (2937 lines, production-grade)
- ✅ Single-file type checking
- ✅ 197+ tests, all passing
- ✅ Comprehensive documentation

### What We Need (Phase 2)
- ⚠️ Cross-file symbol resolution
- ⚠️ Port connection validation
- ⚠️ Interface/modport checking
- ⚠️ Parameter propagation
- ⚠️ Hierarchical type checking

---

## 🗺️ Phase 2 Architecture

```
┌─────────────────────────────────────────────────┐
│         Phase 2: Cross-Module Analysis          │
│                                                   │
│  ┌────────────────────────────────────────┐     │
│  │   Phase 1: Type System (Complete)      │     │
│  │   - Type Inference                     │     │
│  │   - Type Compatibility                 │     │
│  │   - Type Checker                       │     │
│  └──────────────┬─────────────────────────┘     │
│                 │                                 │
│  ┌──────────────▼─────────────────────────┐     │
│  │   Multi-File Symbol Resolver (NEW)     │     │
│  │   - Cross-file references              │     │
│  │   - Module instance tracking           │     │
│  │   - Dependency graph                   │     │
│  └──────────────┬─────────────────────────┘     │
│                 │                                 │
│  ┌──────────────▼─────────────────────────┐     │
│  │   Port Connection Validator (NEW)      │     │
│  │   - Port direction checking            │     │
│  │   - Port type checking                 │     │
│  │   - Width matching                     │     │
│  └──────────────┬─────────────────────────┘     │
│                 │                                 │
│  ┌──────────────▼─────────────────────────┐     │
│  │   Interface Validator (NEW)            │     │
│  │   - Interface definitions              │     │
│  │   - Modport validation                 │     │
│  │   - Interface connections              │     │
│  └──────────────┬─────────────────────────┘     │
│                 │                                 │
│  ┌──────────────▼─────────────────────────┐     │
│  │   Parameter Tracker (NEW)              │     │
│  │   - Parameter declarations             │     │
│  │   - Parameter overrides                │     │
│  │   - Propagation through hierarchy      │     │
│  └──────────────┬─────────────────────────┘     │
│                 │                                 │
│  ┌──────────────▼─────────────────────────┐     │
│  │   Hierarchical Type Checker (NEW)      │     │
│  │   - Type checking across modules       │     │
│  │   - Hierarchy traversal                │     │
│  │   - Consistency validation             │     │
│  └────────────────────────────────────────┘     │
└─────────────────────────────────────────────────┘
```

---

## 📅 Weekly Breakdown

### **Week 6 (Days 26-30): Multi-File Symbol Resolution**

#### Day 26: Planning & Test Framework
- [ ] Create Phase 2 test infrastructure
- [ ] Design multi-file test data structure
- [ ] Create 10 cross-file reference tests
- [ ] Document test strategy

#### Day 27-28: Cross-File Symbol Resolution
- [ ] Write 20 tests for cross-file references
- [ ] Implement MultiFileResolver class
- [ ] Module instance tracking
- [ ] Dependency graph construction

#### Day 29-30: Integration & Testing
- [ ] Run all multi-file tests
- [ ] Debug and fix issues
- [ ] Performance testing
- [ ] Documentation

**Deliverables**:
- MultiFileResolver class (200+ lines)
- 30 tests for cross-file resolution
- Dependency graph support

---

### **Week 7 (Days 31-35): Port Connection Validation**

#### Day 31: Port Connection Test Suite
- [ ] Create 15 port connection tests
- [ ] Cover all port directions (input/output/inout)
- [ ] Test width mismatches
- [ ] Test type mismatches

#### Day 32-33: Port Validator Implementation
- [ ] Write PortConnectionValidator class
- [ ] Port direction checking
- [ ] Port type checking
- [ ] Width compatibility checking

#### Day 34-35: Integration & Edge Cases
- [ ] Handle unpacked arrays
- [ ] Handle parameters in port connections
- [ ] Test hierarchical connections
- [ ] Documentation

**Deliverables**:
- PortConnectionValidator class (300+ lines)
- 15+ port connection tests
- Comprehensive port validation

---

### **Week 8 (Days 36-40): Interface & Parameter Support**

#### Day 36-37: Interface Validation
- [ ] Create 10 interface tests
- [ ] Test modport validation
- [ ] Test interface connections
- [ ] Implement InterfaceValidator

#### Day 38-39: Parameter Tracking
- [ ] Create 10 parameter tests
- [ ] Test parameter overrides
- [ ] Test parameter propagation
- [ ] Implement ParameterTracker

#### Day 40: Integration
- [ ] Integrate interface and parameter support
- [ ] Cross-component testing
- [ ] Documentation

**Deliverables**:
- InterfaceValidator class (250+ lines)
- ParameterTracker class (200+ lines)
- 20 tests for interfaces and parameters

---

### **Week 9 (Days 41-45): Hierarchical Type Checking & Integration**

#### Day 41-42: Hierarchical Type Checking
- [ ] Create 15 hierarchical tests
- [ ] Test type checking through hierarchy
- [ ] Test consistency validation
- [ ] Implement HierarchicalTypeChecker

#### Day 43: Integration Tests
- [ ] Create 10 end-to-end tests
- [ ] Test complete cross-module analysis
- [ ] Performance testing
- [ ] Real-world scenarios

#### Day 44: Documentation
- [ ] API documentation
- [ ] User guides
- [ ] Examples
- [ ] Phase 2 completion report

#### Day 45: Final Validation
- [ ] Run all tests (Phase 1 + Phase 2)
- [ ] Performance benchmarks
- [ ] Final metrics
- [ ] Celebrate! 🎉

**Deliverables**:
- HierarchicalTypeChecker class (300+ lines)
- 25 hierarchical and integration tests
- Complete Phase 2 documentation

---

## 🎯 Test Plan (80+ New Tests)

### Week 6: Multi-File Symbol Resolution (30 tests)
1. Cross-file module references (10 tests)
2. Dependency graph construction (10 tests)
3. Circular dependency detection (5 tests)
4. Missing module detection (5 tests)

### Week 7: Port Connection Validation (15 tests)
1. Port direction validation (5 tests)
2. Port type checking (5 tests)
3. Port width checking (5 tests)

### Week 8: Interface & Parameters (20 tests)
1. Interface definition validation (5 tests)
2. Modport validation (5 tests)
3. Parameter declaration (5 tests)
4. Parameter override (5 tests)

### Week 9: Hierarchical & Integration (25 tests)
1. Hierarchical type checking (10 tests)
2. End-to-end integration (10 tests)
3. Real-world scenarios (5 tests)

**Total New Tests**: 90+  
**Phase 1 + Phase 2 Total**: 287+ tests

---

## 📊 Success Criteria

### Must Have (100% Required)
- [ ] 80+ new tests, all passing
- [ ] Multi-file symbol resolution working
- [ ] Port connection validation complete
- [ ] Interface validation working
- [ ] Parameter tracking implemented
- [ ] Hierarchical type checking functional
- [ ] All Phase 1 tests still passing
- [ ] Documentation complete

### Should Have (90% Target)
- [ ] Performance within 2x of single-file
- [ ] 85%+ code coverage maintained
- [ ] Clear error messages for cross-module issues
- [ ] Examples for all features

### Nice to Have (If Time Permits)
- [ ] Graphviz export of module hierarchy
- [ ] Dependency graph visualization
- [ ] Performance optimization
- [ ] Advanced error recovery

---

## 🏗️ Component Specifications

### 1. MultiFileResolver

```cpp
class MultiFileResolver {
 public:
  explicit MultiFileResolver(const SymbolTable* symbol_table);
  
  // Resolve cross-file references
  absl::Status ResolveReferences();
  
  // Get module definition by name
  const SymbolTableNode* GetModuleDefinition(const std::string& name) const;
  
  // Get all module instances
  std::vector<ModuleInstance> GetModuleInstances(const std::string& module) const;
  
  // Build dependency graph
  absl::Status BuildDependencyGraph();
  
  // Detect circular dependencies
  std::vector<std::vector<std::string>> DetectCircularDependencies() const;
  
 private:
  const SymbolTable* symbol_table_;
  std::map<std::string, const SymbolTableNode*> module_definitions_;
  DependencyGraph dependency_graph_;
};
```

### 2. PortConnectionValidator

```cpp
class PortConnectionValidator {
 public:
  PortConnectionValidator(const TypeInference* type_inference,
                          const TypeCompatibilityChecker* compat_checker);
  
  // Validate port connection
  absl::Status ValidateConnection(
      const PortInfo& port_definition,
      const verible::Symbol& connection,
      const std::string& instance_name) const;
  
  // Validate all ports of an instance
  absl::Status ValidateModuleInstance(
      const ModuleInstance& instance) const;
  
 private:
  const TypeInference* type_inference_;
  const TypeCompatibilityChecker* compat_checker_;
};
```

### 3. InterfaceValidator

```cpp
class InterfaceValidator {
 public:
  explicit InterfaceValidator(const SymbolTable* symbol_table);
  
  // Validate interface definition
  absl::Status ValidateInterfaceDefinition(
      const InterfaceInfo& interface) const;
  
  // Validate modport
  absl::Status ValidateModport(
      const ModportInfo& modport,
      const InterfaceInfo& interface) const;
  
  // Validate interface connection
  absl::Status ValidateInterfaceConnection(
      const verible::Symbol& connection,
      const InterfaceInfo& expected_interface) const;
};
```

### 4. ParameterTracker

```cpp
class ParameterTracker {
 public:
  explicit ParameterTracker(const SymbolTable* symbol_table);
  
  // Track parameter declaration
  void DeclareParameter(const std::string& name, const Type& type);
  
  // Track parameter override
  void OverrideParameter(const std::string& instance,
                        const std::string& param,
                        const verible::Symbol& value);
  
  // Get effective parameter value
  const Type* GetEffectiveParameterType(
      const std::string& instance,
      const std::string& param) const;
};
```

### 5. HierarchicalTypeChecker

```cpp
class HierarchicalTypeChecker {
 public:
  HierarchicalTypeChecker(const SymbolTable* symbol_table,
                          const TypeChecker* type_checker,
                          const MultiFileResolver* resolver);
  
  // Check types through hierarchy
  absl::Status CheckHierarchy(const std::string& top_module);
  
  // Validate consistency across modules
  absl::Status ValidateConsistency();
  
  // Get all type issues in hierarchy
  std::vector<TypeCheckIssue> GetAllIssues() const;
};
```

---

## 📈 Expected Metrics

### Code Metrics (Phase 2)
- New files: 10+
- New lines: 1500+
- New tests: 90+
- Test lines: 2000+

### Combined Metrics (Phase 1 + 2)
- Total files: 18+
- Total code lines: 3800+
- Total tests: 287+
- Test lines: 4700+

### Performance Targets
- Multi-file resolution: <100ms for 10 files
- Port validation: <1ms per port
- Full hierarchy check: <500ms for typical design

---

## 🎓 Learning from Phase 1

### What Worked Well
1. ✅ TDD approach - continue
2. ✅ Daily documentation - continue
3. ✅ Incremental commits - continue
4. ✅ Comprehensive testing - continue

### Improvements for Phase 2
1. 📈 More integration tests early
2. 📈 Performance benchmarks from start
3. 📈 Real-world test cases
4. 📈 Error message consistency

---

## 🚀 Getting Started (Day 26)

### First Tasks
1. [ ] Create Phase 2 test infrastructure
2. [ ] Design multi-file test framework
3. [ ] Write first 10 cross-file tests
4. [ ] Document test data structure

### Test Data Structure
```
testdata/
  cross_module/
    module_a.sv    # Top module
    module_b.sv    # Instantiated by A
    module_c.sv    # Instantiated by B
  interfaces/
    my_interface.sv
    module_with_interface.sv
  parameters/
    parameterized_module.sv
    parent_with_override.sv
```

---

## ✅ Phase 2 Checklist

### Week 6
- [ ] Multi-file test infrastructure
- [ ] 30 cross-file resolution tests
- [ ] MultiFileResolver implementation
- [ ] Dependency graph support

### Week 7
- [ ] 15 port connection tests
- [ ] PortConnectionValidator implementation
- [ ] Port validation complete

### Week 8
- [ ] 10 interface tests
- [ ] 10 parameter tests
- [ ] InterfaceValidator implementation
- [ ] ParameterTracker implementation

### Week 9
- [ ] 25 hierarchical/integration tests
- [ ] HierarchicalTypeChecker implementation
- [ ] Complete documentation
- [ ] Phase 2 completion report

---

**Status**: Ready to begin Phase 2! 🚀  
**Confidence**: 95% (Very High) - Building on solid Phase 1 foundation  
**Next**: Day 26 - Create test infrastructure and first tests

