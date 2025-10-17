# Phase 2 Week 7: Port Connection Validation

**Timeline**: Days 31-35 (5 days)  
**Target**: 100% COMPLETION - Production-ready PortConnectionValidator  
**Philosophy**: "No hurry. Perfection! TDD."

---

## 🎯 Week 7 Objectives

Implement comprehensive port connection validation to ensure:
1. **Port direction checking** - input/output/inout/ref correct usage
2. **Port type checking** - types match at module boundaries
3. **Port width checking** - bit widths compatible
4. **Parameter port handling** - parameters in port declarations work
5. **Array port handling** - packed/unpacked arrays validated

---

## 📋 Week 7 Deliverables

### Must Have (100% Required)
- ✅ **PortConnectionValidator** class (300-400 lines)
- ✅ **15-20+ comprehensive tests** (all passing)
- ✅ **Test data files** (10+ SystemVerilog examples)
- ✅ **API documentation** (header comments)
- ✅ **Week 7 completion report**

### Quality Targets
- ✅ 100% test pass rate
- ✅ Zero build errors
- ✅ Zero technical debt
- ✅ Production-ready quality
- ✅ Comprehensive edge case coverage

---

## 📅 Daily Breakdown

### **Day 31: Port Connection Test Suite (TDD Foundation)**

**Goal**: Create comprehensive test suite FIRST (TDD)

#### Test Categories (15-20 tests)
1. **Basic Port Tests** (5 tests)
   - Simple input port connection
   - Simple output port connection
   - Inout port connection
   - Empty module (no ports)
   - Single-port module

2. **Port Direction Tests** (4 tests)
   - Input connected to output (valid)
   - Output connected to input (valid)
   - Input to input (invalid)
   - Output to output (invalid)

3. **Port Type Tests** (4 tests)
   - Matching types (logic to logic)
   - Type mismatch (logic to reg error)
   - Wire to logic (valid)
   - Struct port connections

4. **Port Width Tests** (4 tests)
   - Matching widths [7:0] to [7:0]
   - Width mismatch [7:0] to [3:0]
   - Implicit vs explicit widths
   - Parameter-based widths

5. **Advanced Port Tests** (3+ tests)
   - Packed array ports
   - Unpacked array ports
   - Multi-dimensional arrays
   - Port expressions (concatenations)

**Deliverables Day 31**:
- ✅ 15-20 test stubs in `port-connection-validator_test.cc`
- ✅ 10+ test data files in `testdata/port_connections/`
- ✅ Test documentation in README
- ✅ All tests compile (fail initially - TDD!)

---

### **Day 32-33: PortConnectionValidator Implementation**

**Goal**: Implement validator to pass all tests

#### Core Components

**1. PortConnectionValidator Class**
```cpp
class PortConnectionValidator {
 public:
  explicit PortConnectionValidator(const SymbolTable* symbol_table,
                                   const TypeChecker* type_checker);
  
  // Main validation method
  absl::Status ValidatePortConnections(const ModuleInstance& instance);
  
  // Port-specific checks
  absl::Status CheckPortDirection(const PortConnection& connection);
  absl::Status CheckPortType(const PortConnection& connection);
  absl::Status CheckPortWidth(const PortConnection& connection);
  
  // Getters for diagnostics
  std::vector<std::string> GetErrors() const;
  std::vector<std::string> GetWarnings() const;
  
 private:
  // Extract port information from module definition
  std::vector<PortInfo> ExtractPorts(const SymbolTableNode& module_node);
  
  // Extract port connections from module instance
  std::vector<PortConnection> ExtractConnections(const verible::Symbol* instance);
  
  // Helper validation methods
  bool IsDirectionCompatible(PortDirection formal, PortDirection actual);
  bool AreTypesCompatible(const Type* formal_type, const Type* actual_type);
  bool AreWidthsCompatible(int formal_width, int actual_width);
  
  const SymbolTable* symbol_table_;
  const TypeChecker* type_checker_;
  std::vector<std::string> errors_;
  std::vector<std::string> warnings_;
};
```

**2. Supporting Structures**
```cpp
enum class PortDirection {
  kInput,
  kOutput,
  kInout,
  kRef
};

struct PortInfo {
  std::string name;
  PortDirection direction;
  const Type* type;
  int width;  // Bit width (-1 for unknown)
  const verible::Symbol* syntax_origin;
};

struct PortConnection {
  std::string formal_name;  // Port name in module definition
  std::string actual_expr;  // Expression in module instance
  const PortInfo* formal_port;
  const Type* actual_type;
  const verible::Symbol* syntax_origin;
};
```

**Implementation Steps**:
1. Create `port-connection-validator.h` header
2. Create `port-connection-validator.cc` implementation
3. Implement `ExtractPorts()` - traverse symbol table for port declarations
4. Implement `ExtractConnections()` - parse instance port connections
5. Implement `CheckPortDirection()` - validate direction compatibility
6. Implement `CheckPortType()` - use TypeChecker for type compatibility
7. Implement `CheckPortWidth()` - validate bit width matching

**Deliverables Days 32-33**:
- ✅ `port-connection-validator.h` (150+ lines)
- ✅ `port-connection-validator.cc` (250+ lines)
- ✅ Basic tests passing (10+ tests)
- ✅ Direction and type checking working

---

### **Day 34-35: Advanced Features & Integration**

**Goal**: Handle edge cases and integrate with MultiFileResolver

#### Advanced Features

**1. Parameter-Based Port Widths**
- Handle `parameter WIDTH = 8; input [WIDTH-1:0] data;`
- Resolve parameter values through hierarchy
- Use ParameterEvaluator (if available) or defer

**2. Array Port Handling**
- Packed arrays: `input [3:0][7:0] data;`
- Unpacked arrays: `input [7:0] data [0:3];`
- Multi-dimensional arrays
- Array slicing in connections

**3. Port Expressions**
- Concatenations: `.port({a, b, c})`
- Replications: `.port({4{data}})`
- Part-selects: `.port(data[7:4])`

**4. Integration with MultiFileResolver**
- Validate all instances found by MultiFileResolver
- Batch validation for entire project
- Generate comprehensive error reports

**5. Edge Cases**
- Implicit port connections (`.port(port)`)
- Named vs positional port connections
- Unconnected ports (warning)
- Extra connections (error)
- Missing required connections (error)

**Deliverables Days 34-35**:
- ✅ All 15-20 tests passing
- ✅ Advanced features implemented
- ✅ Integration with MultiFileResolver
- ✅ Edge case handling
- ✅ Comprehensive error messages

---

## 📊 Success Metrics

### Code Metrics
- PortConnectionValidator: 300-400 lines
- Tests: 15-20+ (all passing)
- Test data files: 10+
- Total new code: 600-800 lines

### Quality Metrics
- Test pass rate: 100%
- Code coverage: 85%+
- Build time: <3s
- Zero regressions in existing tests

### Progress Metrics
- Week 7: 100% complete ✅
- Phase 2: 75% complete (Week 7/9 done)
- Overall: 50% complete (6/12 weeks)

---

## 🔧 Technical Approach

### Leveraging Existing Infrastructure

**1. SymbolTable Integration**
- Use `SymbolMetaType::kModule` to find module definitions
- Use `SymbolMetaType::kPort` to find port declarations
- Extract port direction, type, and width from `SymbolInfo`

**2. TypeChecker Integration**
- Reuse existing type compatibility logic
- Leverage `AreTypesCompatible()` for port type checking
- Use type inference for expressions in port connections

**3. MultiFileResolver Integration**
- Iterate over all `ModuleInstance`s found
- Validate each instance's port connections
- Build comprehensive validation report

**4. CST/AST Navigation**
- Parse port connection syntax from CST
- Extract formal port names and actual expressions
- Handle both named (`.port(expr)`) and positional connections

---

## 📝 Documentation Plan

### Code Documentation
- Comprehensive header comments for all public APIs
- Function-level documentation for complex logic
- Inline comments for tricky CST navigation

### Test Documentation
- Each test documents what it validates
- Test data files include comments explaining scenarios
- README in testdata directory

### Week 7 Report
- Summary of accomplishments
- Metrics and statistics
- Known limitations (if any)
- Path forward to Week 8

---

## 🎯 Week 7 Success Criteria

**All must be 100% complete**:
- ✅ PortConnectionValidator class: Complete and production-ready
- ✅ Tests: 15-20+ all passing
- ✅ Test data: 10+ comprehensive examples
- ✅ Documentation: Comprehensive API docs
- ✅ Integration: Works with MultiFileResolver
- ✅ Quality: Zero technical debt
- ✅ Report: Week 7 completion documented

**Following "No hurry. Perfection! TDD." throughout!** 🎯✨

