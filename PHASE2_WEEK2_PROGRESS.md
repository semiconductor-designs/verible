# Phase 2 Week 2: Type System Enhancement - Progress

**Date:** 2025-10-15  
**Status:** 🚧 In Progress - Day 1  
**Goal:** Add type inference and type checking on top of existing symbol table

---

## 🎯 Week 2 Objectives

| Objective | Status | Notes |
|-----------|--------|-------|
| Design type representation | 🚧 In Progress | SystemVerilog type system |
| Implement TypeInference | 📅 Planned | Expression type inference |
| Implement TypeChecker | 📅 Planned | Compatibility checking |
| Create tests | 📅 Planned | Unit + integration |
| Integration | 📅 Planned | With symbol table |

---

## 🏗️ Architecture Design

### Overview

```
Existing Symbol Table (2,937 lines)
    ↓ (build on top, don't modify)
┌─────────────────────────────────┐
│   Type System Layer (NEW)       │
├─────────────────────────────────┤
│  Type Registry                   │
│    ↓                             │
│  TypeInference                   │
│    ↓                             │
│  TypeChecker                     │
└─────────────────────────────────┘
    ↓
Enhanced Analysis (unused detection, call graph)
```

**Design Principle:** Non-invasive enhancement
- ✅ Read from symbol table
- ✅ Build type annotations separately
- ❌ Don't modify symbol table internals

---

## 📊 Type System Design

### 1. Type Representation

**File:** `verible/verilog/analysis/type-system.h`

```cpp
namespace verilog {
namespace analysis {

// Base type system for SystemVerilog
enum class TypeKind {
  // Primitive types
  kLogic,
  kBit,
  kReg,
  kInteger,
  kReal,
  kString,
  kChandle,
  kVoid,
  
  // Composite types
  kStruct,
  kUnion,
  kEnum,
  kClass,
  kInterface,
  
  // Aggregate types
  kPackedArray,
  kUnpackedArray,
  kQueue,
  kAssociativeArray,
  kDynamicArray,
  
  // Special
  kUnknown,
  kError,
};

class Type {
 public:
  virtual ~Type() = default;
  
  virtual TypeKind kind() const = 0;
  virtual std::string ToString() const = 0;
  
  // Type compatibility
  virtual bool IsCompatibleWith(const Type& other) const = 0;
  virtual bool IsAssignableFrom(const Type& other) const = 0;
  
  // Width for packed types
  virtual int GetWidth() const { return -1; }
  virtual bool IsSigned() const { return false; }
};

// Primitive type (logic, bit, etc.)
class PrimitiveType : public Type {
 public:
  PrimitiveType(TypeKind kind, int width, bool is_signed)
      : kind_(kind), width_(width), is_signed_(is_signed) {}
  
  TypeKind kind() const override { return kind_; }
  int GetWidth() const override { return width_; }
  bool IsSigned() const override { return is_signed_; }
  
  std::string ToString() const override;
  bool IsCompatibleWith(const Type& other) const override;
  bool IsAssignableFrom(const Type& other) const override;
  
 private:
  TypeKind kind_;
  int width_;
  bool is_signed_;
};

// Array type
class ArrayType : public Type {
 public:
  ArrayType(const Type* element_type, 
            const std::vector<int>& dimensions,
            bool is_packed)
      : element_type_(element_type),
        dimensions_(dimensions),
        is_packed_(is_packed) {}
  
  TypeKind kind() const override {
    return is_packed_ ? TypeKind::kPackedArray : TypeKind::kUnpackedArray;
  }
  
  const Type* ElementType() const { return element_type_; }
  const std::vector<int>& Dimensions() const { return dimensions_; }
  
  std::string ToString() const override;
  bool IsCompatibleWith(const Type& other) const override;
  bool IsAssignableFrom(const Type& other) const override;
  
 private:
  const Type* element_type_;
  std::vector<int> dimensions_;
  bool is_packed_;
};

// Struct type
class StructType : public Type {
 public:
  struct Member {
    std::string name;
    const Type* type;
  };
  
  explicit StructType(const std::vector<Member>& members)
      : members_(members) {}
  
  TypeKind kind() const override { return TypeKind::kStruct; }
  const std::vector<Member>& Members() const { return members_; }
  
  const Type* GetMemberType(std::string_view name) const;
  
  std::string ToString() const override;
  bool IsCompatibleWith(const Type& other) const override;
  bool IsAssignableFrom(const Type& other) const override;
  
 private:
  std::vector<Member> members_;
};

// Type registry - manages type instances
class TypeRegistry {
 public:
  // Get built-in types
  const Type* GetLogicType(int width = 1, bool is_signed = false);
  const Type* GetBitType(int width = 1, bool is_signed = false);
  const Type* GetIntegerType();
  const Type* GetRealType();
  const Type* GetStringType();
  const Type* GetVoidType();
  
  // Create composite types
  const Type* CreateArrayType(const Type* element,
                               const std::vector<int>& dims,
                               bool is_packed);
  const Type* CreateStructType(const std::vector<StructType::Member>& members);
  
  // Get or create type by name (for user-defined types)
  const Type* GetOrCreateNamedType(std::string_view name);
  
 private:
  // Cache of created types (for deduplication)
  std::vector<std::unique_ptr<Type>> types_;
  std::map<std::string, const Type*> named_types_;
};

}  // namespace analysis
}  // namespace verilog
```

---

### 2. Type Inference

**File:** `verible/verilog/analysis/type-inference.h`

```cpp
namespace verilog {
namespace analysis {

class TypeInference {
 public:
  TypeInference(const SymbolTable* symbols, TypeRegistry* registry)
      : symbols_(symbols), registry_(registry) {}
  
  // Main entry point: infer type of any expression
  const Type* InferType(const verible::Symbol& expr,
                        const SymbolTableNode& context);
  
  // Infer from declaration
  const Type* InferFromDeclaration(const SymbolTableNode& symbol);
  
  // Infer from literal
  const Type* InferFromLiteral(const verible::Symbol& literal);
  
  // Infer from identifier (lookup in symbol table)
  const Type* InferFromIdentifier(std::string_view name,
                                   const SymbolTableNode& context);
  
  // Infer from binary operation
  const Type* InferBinaryOp(const verible::Symbol& op,
                             const Type* left_type,
                             const Type* right_type);
  
  // Infer from unary operation
  const Type* InferUnaryOp(const verible::Symbol& op,
                            const Type* operand_type);
  
  // Infer from function call
  const Type* InferFunctionCall(const SymbolTableNode& function,
                                 const std::vector<const Type*>& arg_types);
  
  // Infer from array index
  const Type* InferArrayAccess(const Type* array_type,
                                const std::vector<const Type*>& indices);
  
  // Infer from member access (struct.member)
  const Type* InferMemberAccess(const Type* base_type,
                                 std::string_view member_name);
  
 private:
  const SymbolTable* symbols_;
  TypeRegistry* registry_;
  
  // Cache for performance
  std::map<const verible::Symbol*, const Type*> type_cache_;
};

}  // namespace analysis
}  // namespace verilog
```

---

### 3. Type Checker

**File:** `verible/verilog/analysis/type-checker.h`

```cpp
namespace verilog {
namespace analysis {

class TypeChecker {
 public:
  struct TypeError {
    enum class Kind {
      kIncompatibleAssignment,
      kIncompatibleOperation,
      kWidthMismatch,
      kSignednessMismatch,
      kTypeMismatch,
      kUnknownType,
    };
    
    Kind kind;
    verible::Location location;
    std::string message;
    const Type* expected = nullptr;
    const Type* actual = nullptr;
    std::string suggestion;
  };
  
  TypeChecker(TypeInference* inference) : inference_(inference) {}
  
  // Check entire file/module
  std::vector<TypeError> CheckModule(const SymbolTableNode& module);
  
  // Check assignment compatibility
  absl::Status CheckAssignment(const verible::Symbol& lhs,
                                const verible::Symbol& rhs,
                                const SymbolTableNode& context);
  
  // Check binary operation
  absl::Status CheckBinaryOp(const verible::Symbol& op,
                              const verible::Symbol& left,
                              const verible::Symbol& right,
                              const SymbolTableNode& context);
  
  // Check function call
  absl::Status CheckFunctionCall(const verible::Symbol& call,
                                  const SymbolTableNode& function,
                                  const std::vector<const verible::Symbol*>& args,
                                  const SymbolTableNode& context);
  
  // Check if/case condition
  absl::Status CheckCondition(const verible::Symbol& condition,
                               const SymbolTableNode& context);
  
  // Get all accumulated errors
  const std::vector<TypeError>& GetErrors() const { return errors_; }
  
 private:
  TypeInference* inference_;
  std::vector<TypeError> errors_;
  
  void ReportError(TypeError error);
  std::string GenerateSuggestion(const TypeError& error) const;
};

}  // namespace analysis
}  // namespace verilog
```

---

## 📝 Implementation Strategy

### Phase 1: Foundation (Day 1)
**Status:** 🚧 In Progress

1. **Create type-system.h skeleton**
   - Define TypeKind enum
   - Define Type base class
   - Define PrimitiveType

2. **Create TypeRegistry**
   - Basic type factory
   - Built-in types (logic, bit, integer, etc.)

3. **Initial tests**
   - Test type creation
   - Test type equality
   - Test basic compatibility

### Phase 2: Type Inference (Day 2)
**Status:** 📅 Planned

1. **Create type-inference.h skeleton**
   - Define TypeInference class
   - Implement literal inference
   - Implement identifier lookup

2. **Expression inference**
   - Binary operators (+, -, *, /, etc.)
   - Unary operators (!, ~, etc.)
   - Ternary operator (? :)

3. **Tests**
   - Test literal inference
   - Test operator inference
   - Test identifier inference

### Phase 3: Type Checking (Day 3-4)
**Status:** 📅 Planned

1. **Create type-checker.h skeleton**
   - Define TypeChecker class
   - Define TypeError struct

2. **Assignment checking**
   - Width compatibility
   - Signedness compatibility
   - Type compatibility

3. **Operation checking**
   - Binary operation types
   - Function call arguments

4. **Tests**
   - Test assignment checks
   - Test operation checks
   - Test error reporting

### Phase 4: Integration (Day 5)
**Status:** 📅 Planned

1. **Integration with symbol table**
   - Read declarations from symbol table
   - Annotate with inferred types

2. **End-to-end tests**
   - Test on real SystemVerilog files
   - Performance validation
   - False positive analysis

3. **Documentation**
   - API documentation
   - Usage examples
   - Integration guide

---

## 🧪 Test Strategy

### Unit Tests
```cpp
// type-system_test.cc
TEST(TypeSystemTest, PrimitiveTypeCreation) {
  TypeRegistry registry;
  const Type* logic8 = registry.GetLogicType(8, false);
  EXPECT_EQ(logic8->GetWidth(), 8);
  EXPECT_FALSE(logic8->IsSigned());
}

TEST(TypeSystemTest, TypeCompatibility) {
  TypeRegistry registry;
  const Type* logic8 = registry.GetLogicType(8, false);
  const Type* logic16 = registry.GetLogicType(16, false);
  
  // Can assign logic[7:0] to logic[15:0] (widening)
  EXPECT_TRUE(logic16->IsAssignableFrom(*logic8));
  
  // Cannot assign logic[15:0] to logic[7:0] (narrowing - warning)
  EXPECT_FALSE(logic8->IsAssignableFrom(*logic16));
}

// type-inference_test.cc
TEST(TypeInferenceTest, LiteralInference) {
  TypeRegistry registry;
  TypeInference inference(nullptr, &registry);
  
  // 8'hFF -> logic[7:0]
  const Type* type = inference.InferFromLiteral(/* literal node */);
  EXPECT_EQ(type->GetWidth(), 8);
}

TEST(TypeInferenceTest, BinaryOpInference) {
  TypeRegistry registry;
  TypeInference inference(nullptr, &registry);
  
  const Type* logic8 = registry.GetLogicType(8, false);
  const Type* logic16 = registry.GetLogicType(16, false);
  
  // logic[7:0] + logic[15:0] -> logic[15:0]
  const Type* result = inference.InferBinaryOp(/* + op */, logic8, logic16);
  EXPECT_EQ(result->GetWidth(), 16);
}

// type-checker_test.cc
TEST(TypeCheckerTest, AssignmentWidthMismatch) {
  // logic [7:0] a;
  // logic [15:0] b;
  // a = b;  // Should warn
  
  TypeChecker checker(&inference);
  auto status = checker.CheckAssignment(/* a */, /* b */, context);
  EXPECT_FALSE(status.ok());
  EXPECT_THAT(status.message(), HasSubstr("width mismatch"));
}
```

### Integration Tests
- Test on real SystemVerilog modules
- Verify type inference correctness
- Check false positive rate (<1%)

---

## 📈 Success Metrics

### Quantitative
- [ ] All primitive types supported
- [ ] Array types supported
- [ ] Struct types supported
- [ ] >90% expression types inferred correctly
- [ ] <1% false positives in type checking
- [ ] <100ms overhead for 10K line file

### Qualitative
- [ ] Clean, extensible API
- [ ] Comprehensive test coverage
- [ ] Good error messages
- [ ] Integration-ready

---

## 🚧 Current Status (Day 1)

### Completed
- ✅ Architecture designed
- ✅ API interfaces defined
- ✅ Test strategy planned
- ✅ Implementation phases defined

### In Progress
- 🚧 Creating type-system.h skeleton
- 🚧 Implementing TypeRegistry

### Next Steps
- 📅 Implement PrimitiveType
- 📅 Create unit tests
- 📅 Start type-inference.h

---

## 📝 Notes & Decisions

### Design Decisions

1. **Non-Invasive Enhancement**
   - Build on top of existing symbol table
   - Don't modify symbol-table.{h,cc}
   - Keep as separate analysis layer

2. **Type Representation**
   - Use abstract Type base class
   - Concrete subclasses for different type kinds
   - TypeRegistry for type instance management

3. **Caching Strategy**
   - Cache inferred types for performance
   - Invalidate on symbol table changes
   - Trade memory for speed

4. **Error Reporting**
   - Collect all errors (don't fail fast)
   - Provide actionable suggestions
   - Link back to source locations

### Open Questions

1. **User-Defined Types**
   - How to handle typedef?
   - How to handle class types?
   - Answer: Use named_types_ map in TypeRegistry

2. **Parameterized Types**
   - How to handle module parameters?
   - Answer: Resolve parameters first, then infer types

3. **Integration Point**
   - Where to store inferred types?
   - Answer: Separate type annotation map, keyed by CST node

---

## ✅ Week 2 Day 1 Status

- **Documentation:** Complete (this file)
- **Design:** Complete
- **Implementation:** Starting
- **Timeline:** On track

**Next:** Implement type-system.h skeleton and basic TypeRegistry

