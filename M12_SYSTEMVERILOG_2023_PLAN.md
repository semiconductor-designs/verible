# M12: SystemVerilog 2023 (IEEE 1800-2023) Support

**Goal:** Extend Verible from 100% SV-2017 coverage to support SystemVerilog 2023 enhancements

**Status:** Planning Phase  
**Standard:** IEEE 1800-2023 (approved December 6, 2023)  
**Current Base:** v3.9.0 with 243/243 IEEE 1800-2017 keywords

---

## 🎯 Overview

SystemVerilog 2023 introduces **7 major enhancements** focusing on:
- Better FSM modularization
- Enhanced parameterization
- Improved string handling
- More powerful preprocessor
- Flexible packed unions
- Type safety improvements
- Array manipulation enhancements

---

## 📊 Feature Breakdown

### Priority Classification

| Priority | Feature | Complexity | Impact | Effort |
|----------|---------|------------|--------|--------|
| **HIGH** | 1. `ref static` arguments | High | High | 5-7 days |
| **HIGH** | 2. Multiline string literals (`"""`) | Medium | High | 3-4 days |
| **MEDIUM** | 3. Enhanced preprocessor | Medium | Medium | 4-5 days |
| **MEDIUM** | 4. `soft` packed unions | Medium | Medium | 3-4 days |
| **MEDIUM** | 5. Type parameter restrictions | High | Medium | 5-6 days |
| **LOW** | 6. Associative array parameters | Medium | Low | 3-4 days |
| **LOW** | 7. Array `map` method | Medium | Low | 3-4 days |

**Total Estimated Effort:** 26-38 days (4-6 weeks)

---

## Feature 1: `ref static` Arguments (HIGH PRIORITY)

### Description
Allow tasks and functions to accept `ref static` arguments for FSM state updates.

### Syntax
```systemverilog
task update_fsm(ref static state_t current_state, input event_t event);
  current_state <= next_state(current_state, event);  // Nonblocking assignment
endtask

// Usage in FSM
always_ff @(posedge clk) begin
  update_fsm(state, input_event);
end
```

### Impact
- **High:** Enables better FSM modularization
- Widely requested feature for state machine design
- Solves longstanding limitation with ref arguments

### Implementation Steps

1. **Add Keyword** (verilog.lex)
```
static { UpdateLocation(); return TK_static; }  // Already exists, extend usage
```

2. **Extend Grammar** (verilog.y)
```yacc
tf_port_direction
  : TK_input
  | TK_output  
  | TK_inout
  | TK_ref
  | TK_ref TK_static       // NEW: ref static combination
    { $$ = MakeNode($1, $2); }
  ;
```

3. **Write Tests** (verilog-parser-ref-static_test.cc)
```cpp
TEST(RefStaticTest, TaskArgument) {
  TestParserAcceptValid(
    "module m;\n"
    "  task t(ref static logic [7:0] state);\n"
    "    state <= 8'h00;\n"
    "  endtask\n"
    "endmodule\n", 5001);
}

TEST(RefStaticTest, FunctionArgument) {
  TestParserAcceptValid(
    "module m;\n"
    "  function void f(ref static int counter);\n"
    "    counter <= counter + 1;\n"
    "  endfunction\n"
    "endmodule\n", 5002);
}

TEST(RefStaticTest, InFSM) {
  TestParserAcceptValid(
    "module fsm;\n"
    "  typedef enum {IDLE, ACTIVE} state_t;\n"
    "  state_t state;\n"
    "  task update_state(ref static state_t s);\n"
    "    s <= ACTIVE;\n"
    "  endtask\n"
    "  always_ff @(posedge clk) update_state(state);\n"
    "endmodule\n", 5003);
}
```

**Expected:** 3/3 tests pass

---

## Feature 2: Multiline String Literals (HIGH PRIORITY)

### Description
Python-style triple-quoted strings for multiline literals.

### Syntax
```systemverilog
string msg = """
  This is a multiline
  string literal without
  escape characters!
""";

$display("""
  Status: %d
  Value:  %h
""", status, value);
```

### Impact
- **High:** Improves readability for long strings
- Common in testbench messages, documentation
- Modern language feature

### Implementation Steps

1. **Extend Lexer** (verilog.lex)
```lex
/* Multiline string literal (SV-2023) */
\"\"\" {
  UpdateLocation();
  yy_push_state(MULTILINE_STRING);
}

<MULTILINE_STRING>{
  \"\"\" {
    UpdateLocation();
    yy_pop_state();
    return TK_MultilineStringLiteral;
  }
  [^\"]+ { yymore(); }
  \" { yymore(); }
  \n { IncrementLine(); yymore(); }
}
```

2. **Update Grammar** (verilog.y)
```yacc
string_literal
  : TK_StringLiteral
    { $$ = std::move($1); }
  | TK_MultilineStringLiteral
    /* SV-2023: Triple-quoted multiline strings */
    { $$ = std::move($1); }
  ;
```

3. **Write Tests** (verilog-parser-multiline-string_test.cc)
```cpp
TEST(MultilineStringTest, Basic) {
  TestParserAcceptValid(
    "module m;\n"
    "  string s = \"\"\"Hello\n"
    "World\"\"\";\n"
    "endmodule\n", 5011);
}

TEST(MultilineStringTest, InDisplay) {
  TestParserAcceptValid(
    "module m;\n"
    "  initial $display(\"\"\"Line 1\n"
    "Line 2\n"
    "Line 3\"\"\");\n"
    "endmodule\n", 5012);
}

TEST(MultilineStringTest, WithIndentation) {
  TestParserAcceptValid(
    "module m;\n"
    "  string doc = \"\"\"\n"
    "    Parameter: width\n"
    "    Default: 8\n"
    "    Range: 1-32\n"
    "  \"\"\";\n"
    "endmodule\n", 5013);
}
```

**Expected:** 3/3 tests pass

---

## Feature 3: Enhanced Preprocessor (MEDIUM PRIORITY)

### Description
Logical operators in preprocessor conditionals.

### Syntax
```systemverilog
`ifdef (FEATURE_A && FEATURE_B)
  // Both defined
`endif

`ifdef (!DEBUG || VERBOSE)
  // Not debug OR verbose
`endif

`ifdef (MODE -> ADVANCED)
  // If MODE then ADVANCED (implication)
`endif
```

### Impact
- **Medium:** More powerful conditional compilation
- Reduces preprocessor complexity
- Aligns with modern tooling

### Implementation Steps

1. **Extend Preprocessor** (preprocessor/)
```cpp
// Add logical expression evaluator for `ifdef conditions
bool EvaluatePreprocessorExpression(const string& expr) {
  // Support: !, &&, ||, ->, <->
  // Parse and evaluate macro-defined identifiers
}
```

2. **Update Grammar**
```yacc
preprocessor_ifdef
  : PP_ifdef preprocessor_condition
  | PP_ifdef '(' preprocessor_logical_expr ')'  // NEW: Allow expressions
  ;

preprocessor_logical_expr
  : preprocessor_identifier
  | '!' preprocessor_logical_expr
  | preprocessor_logical_expr TK_LAND preprocessor_logical_expr
  | preprocessor_logical_expr TK_LOR preprocessor_logical_expr
  | preprocessor_logical_expr TK_LOGICAL_IMPLIES preprocessor_logical_expr
  | preprocessor_logical_expr TK_LOGEQUIV preprocessor_logical_expr
  ;
```

3. **Write Tests** (verilog-parser-enhanced-preprocessor_test.cc)
```cpp
TEST(EnhancedPreprocessorTest, LogicalAnd) {
  TestParserAcceptValid(
    "`define A\n"
    "`define B\n"
    "`ifdef (A && B)\n"
    "  module m; endmodule\n"
    "`endif\n", 5021);
}

TEST(EnhancedPreprocessorTest, LogicalNot) {
  TestParserAcceptValid(
    "`ifdef (!UNDEFINED)\n"
    "  module m; endmodule\n"
    "`endif\n", 5022);
}

TEST(EnhancedPreprocessorTest, Implication) {
  TestParserAcceptValid(
    "`define MODE 1\n"
    "`ifdef (MODE -> ADVANCED)\n"
    "  module m; endmodule\n"
    "`endif\n", 5023);
}
```

**Expected:** 3/3 tests pass

---

## Feature 4: `soft` Packed Unions (MEDIUM PRIORITY)

### Description
Allow packed unions with different-sized members.

### Syntax
```systemverilog
typedef union packed soft {
  logic [7:0]  byte_val;
  logic [15:0] word_val;
  logic [31:0] dword_val;  // Union size = 32 bits (largest)
} flexible_data_t;
```

### Impact
- **Medium:** More flexible data structures
- Useful for protocol handling
- Reduces need for workarounds

### Implementation Steps

1. **Add Keyword** (verilog.lex)
```
soft { UpdateLocation(); return TK_soft; }
```

2. **Extend Grammar** (verilog.y)
```yacc
union_declaration
  : TK_union TK_packed TK_soft data_type_or_implicit '{' struct_union_member_list '}'
    /* SV-2023: soft packed union */
    { $$ = MakeTaggedNode(N::kUnionDeclaration, $1, $2, $3, $4, $5, $6, $7); }
  | TK_union TK_packed data_type_or_implicit '{' struct_union_member_list '}'
    { $$ = MakeTaggedNode(N::kUnionDeclaration, $1, $2, $3, $4, $5, $6); }
  ;
```

3. **Write Tests** (verilog-parser-soft-union_test.cc)
```cpp
TEST(SoftUnionTest, BasicDecl) {
  TestParserAcceptValid(
    "module m;\n"
    "  typedef union packed soft {\n"
    "    logic [7:0] byte_val;\n"
    "    logic [31:0] word_val;\n"
    "  } data_t;\n"
    "endmodule\n", 5031);
}

TEST(SoftUnionTest, DifferentSizes) {
  TestParserAcceptValid(
    "module m;\n"
    "  union packed soft {\n"
    "    bit [3:0] nibble;\n"
    "    bit [15:0] word;\n"
    "    bit [63:0] dword;\n"
    "  } flexible;\n"
    "endmodule\n", 5032);
}
```

**Expected:** 2/2 tests pass

---

## Feature 5: Type Parameter Restrictions (MEDIUM PRIORITY)

### Description
Restrict type parameters to specific categories.

### Syntax
```systemverilog
class Container #(type enum T);  // T must be enum type
  T data;
endclass

module GenericFIFO #(type struct entry_t);  // entry_t must be struct
  entry_t buffer[$];
endmodule

class Registry #(type class handler_t);  // handler_t must be class
  handler_t handlers[$];
endclass
```

### Impact
- **Medium:** Enhanced type safety
- Better compile-time checking
- Clearer intent

### Implementation Steps

1. **Extend Grammar** (verilog.y)
```yacc
type_parameter
  : TK_type GenericIdentifier type_parameter_default_opt
    { $$ = MakeTaggedNode(N::kTypeParameter, $1, $2, $3); }
  | TK_type TK_enum GenericIdentifier type_parameter_default_opt
    /* SV-2023: Restrict to enum types */
    { $$ = MakeTaggedNode(N::kTypeParameter, $1, $2, $3, $4); }
  | TK_type TK_struct GenericIdentifier type_parameter_default_opt
    /* SV-2023: Restrict to struct types */
    { $$ = MakeTaggedNode(N::kTypeParameter, $1, $2, $3, $4); }
  | TK_type TK_class GenericIdentifier type_parameter_default_opt
    /* SV-2023: Restrict to class types */
    { $$ = MakeTaggedNode(N::kTypeParameter, $1, $2, $3, $4); }
  ;
```

2. **Write Tests** (verilog-parser-type-restrictions_test.cc)
```cpp
TEST(TypeRestrictionsTest, EnumRestriction) {
  TestParserAcceptValid(
    "class C #(type enum T);\n"
    "  T data;\n"
    "endclass\n", 5041);
}

TEST(TypeRestrictionsTest, StructRestriction) {
  TestParserAcceptValid(
    "module m #(type struct entry_t);\n"
    "  entry_t buffer[$];\n"
    "endmodule\n", 5042);
}

TEST(TypeRestrictionsTest, ClassRestriction) {
  TestParserAcceptValid(
    "class Registry #(type class handler_t);\n"
    "  handler_t obj;\n"
    "endclass\n", 5043);
}
```

**Expected:** 3/3 tests pass

---

## Feature 6: Associative Array Parameters (LOW PRIORITY)

### Description
Use associative arrays as module/class parameters.

### Syntax
```systemverilog
module ConfigurableModule #(
  parameter int config[string] = '{
    "width": 32,
    "depth": 1024,
    "mode": 1
  }
);
  localparam int W = config["width"];
endmodule
```

### Impact
- **Low:** Niche feature for complex configurations
- Useful for highly parameterized designs
- Alternative approaches exist

### Implementation Steps

1. **Extend Grammar** (verilog.y)
```yacc
parameter_declaration
  : TK_parameter data_type_or_implicit list_of_param_assignments
  | TK_parameter associative_array_type list_of_param_assignments
    /* SV-2023: Allow associative array parameters */
    { $$ = MakeTaggedNode(N::kParameterDeclaration, $1, $2, $3); }
  ;
```

2. **Write Tests** (verilog-parser-assoc-array-param_test.cc)
```cpp
TEST(AssocArrayParamTest, StringIndexed) {
  TestParserAcceptValid(
    "module m #(parameter int cfg[string] = '{\"a\": 1});\n"
    "endmodule\n", 5051);
}
```

**Expected:** 1/1 test passes

---

## Feature 7: Array `map` Method (LOW PRIORITY)

### Description
Element-wise array operations without temporary arrays.

### Syntax
```systemverilog
int a[] = {1, 2, 3, 4, 5};
int b[];

// Traditional approach (creates temporary)
b = new[a.size()];
foreach (a[i]) b[i] = a[i] * 2;

// SV-2023: map method
b = a.map(x => x * 2);  // Cleaner!

// With transformation function
function int square(int x); return x * x; endfunction
int c[] = a.map(square);
```

### Impact
- **Low:** Syntactic sugar, not essential
- Improves code readability
- Functional programming style

### Implementation Steps

1. **Extend Grammar** (verilog.y)
```yacc
method_call
  : '.' GenericIdentifier '(' expression_list_proper_opt ')'
  | '.' TK_map '(' lambda_expression ')'
    /* SV-2023: Array map method */
    { $$ = MakeTaggedNode(N::kMethodCall, $1, $2, MakeParenGroup($3, $4, $5)); }
  ;

lambda_expression
  : identifier TK_LAMBDA expression
    /* Lambda: x => x * 2 */
    { $$ = MakeTaggedNode(N::kLambdaExpression, $1, $2, $3); }
  | identifier
    /* Function reference */
    { $$ = std::move($1); }
  ;
```

2. **Add Tokens** (verilog.lex)
```
"=>" { UpdateLocation(); return TK_LAMBDA; }  // Lambda operator
```

3. **Write Tests** (verilog-parser-array-map_test.cc)
```cpp
TEST(ArrayMapTest, BasicMap) {
  TestParserAcceptValid(
    "module m;\n"
    "  int a[] = {1, 2, 3};\n"
    "  int b[] = a.map(x => x * 2);\n"
    "endmodule\n", 5061);
}

TEST(ArrayMapTest, WithFunction) {
  TestParserAcceptValid(
    "module m;\n"
    "  function int square(int x); return x*x; endfunction\n"
    "  int a[] = {1, 2, 3};\n"
    "  int b[] = a.map(square);\n"
    "endmodule\n", 5062);
}
```

**Expected:** 2/2 tests pass

---

## 📊 Implementation Plan

### Phase 1: High Priority (Days 1-14)
1. ✅ Feature 2: Multiline strings (Days 1-4)
2. ✅ Feature 1: `ref static` (Days 5-11)
3. ✅ Integration test Phase 1 (Days 12-14)

### Phase 2: Medium Priority (Days 15-28)
4. ✅ Feature 4: `soft` unions (Days 15-18)
5. ✅ Feature 3: Enhanced preprocessor (Days 19-23)
6. ✅ Feature 5: Type restrictions (Days 24-29)
7. ✅ Integration test Phase 2 (Days 30-31)

### Phase 3: Low Priority (Days 32-38)
8. ✅ Feature 6: Associative array params (Days 32-35)
9. ✅ Feature 7: Array map method (Days 36-38)
10. ✅ Final integration & docs (Days 39-40)

---

## 🎯 Success Criteria

- All 7 features implemented with comprehensive tests
- **Minimum 15+ new tests** (2-3 per feature)
- Zero regressions in IEEE 1800-2017 tests
- Clean grammar (no new conflicts)
- Full documentation with examples
- **Coverage: IEEE 1800-2023 compliance**

---

## 📦 Files to Create/Modify

### New Test Files (7)
1. `verilog-parser-ref-static_test.cc`
2. `verilog-parser-multiline-string_test.cc`
3. `verilog-parser-enhanced-preprocessor_test.cc`
4. `verilog-parser-soft-union_test.cc`
5. `verilog-parser-type-restrictions_test.cc`
6. `verilog-parser-assoc-array-param_test.cc`
7. `verilog-parser-array-map_test.cc`

### Modified Files
1. `verible/verilog/parser/verilog.lex` - New tokens (soft, multiline strings, =>)
2. `verible/verilog/parser/verilog.y` - 7 grammar extensions
3. `verible/verilog/CST/verilog-nonterminals.h` - New CST nodes
4. `verible/verilog/parser/BUILD` - 7 new test targets
5. `verible/common/text/token-info.h` - Token definitions

---

## 🏆 Expected Outcome

**Verible v4.0.0: The First Parser with SystemVerilog 2023 Support**

- ✅ 100% IEEE 1800-2017 (v3.9.0 baseline)
- ✅ IEEE 1800-2023 enhancements
- ✅ World's most advanced open-source SV parser
- ✅ Ahead of commercial tools in standards support

---

## 📚 References

1. IEEE Standard 1800-2023 (SystemVerilog)
2. Brad Pierce's Blog: "What's new in SystemVerilog-2023?"
   - Part 1: Design enhancements
   - Part 2: Verification enhancements
3. IEEE Xplore: https://ieeexplore.ieee.org/document/10458102

---

## 🚀 Next Steps

1. **Review this plan** - Confirm priorities and scope
2. **Start with Feature 2** - Multiline strings (highest ROI)
3. **TDD approach** - Tests first, always
4. **Incremental releases** - v3.10, v3.11, ... → v4.0.0

---

**Ready to push Verible to the cutting edge of SystemVerilog support?** 🌟

Let's make Verible the **first parser to fully support SV-2023**!

