# Phase 2: UVM Macro Support - Grammar Analysis

**Date**: 2025-01-18  
**Phase**: 2 - UVM Macro Support (Weeks 3-10)  
**Status**: ANALYSIS IN PROGRESS

---

## Executive Summary

Phase 2 focuses on implementing UVM macro parsing support - the **biggest unlock** that will enable parsing of ~80 out of 89 failing OpenTitan UVM files (90%). This document analyzes Verible's current preprocessor and parser architecture to inform implementation.

**Key Insight**: Verible separates preprocessing from parsing, so UVM macro support requires changes to **both** the preprocessor (macro expansion) and potentially the parser (grammar for macro calls).

---

## Current Verible Architecture

### Component Overview

```
User Code (*.sv with UVM macros)
         ↓
┌────────────────────────────────┐
│  verilog-preprocess.cc         │  
│  - Macro expansion             │
│  - Conditional compilation     │
│  - Include resolution          │
└────────────────────────────────┘
         ↓
   Preprocessed Text
         ↓
┌────────────────────────────────┐
│  verilog.y (Bison Grammar)     │
│  - Lexical analysis (lex)      │
│  - Syntax analysis (yacc)      │
└────────────────────────────────┘
         ↓
   Concrete Syntax Tree (CST)
         ↓
┌────────────────────────────────┐
│  verilog-analyzer.cc           │
│  - Semantic analysis           │
│  - Symbol table                │
└────────────────────────────────┘
```

### Key Files

1. **Preprocessor**:
   - `verible/verilog/preprocessor/verilog-preprocess.cc` - Main preprocessor logic
   - `verible/verilog/preprocessor/verilog-preprocess.h` - Public API
   - `verible/verilog/preprocessor/verilog-preprocess-expr.cc` - Expression evaluation

2. **Parser**:
   - `verible/verilog/parser/verilog.y` - Bison grammar (8,944 lines)
   - `verible/verilog/parser/verilog.lex` - Flex lexer (if exists)

3. **CST**:
   - `verible/verilog/CST/verilog-nonterminals.h` - Node type definitions

---

## Problem Analysis

### Why UVM Macros Fail

**UVM macro example**:
```systemverilog
`uvm_object_utils_begin(simple_item)
  `uvm_field_int(data, UVM_DEFAULT)
`uvm_object_utils_end
```

**Expected expansion** (simplified):
```systemverilog
typedef uvm_object_registry#(simple_item, "simple_item") type_id;
static function type_id get_type();
  return type_id::get();
endfunction
// ... 40+ more lines ...
```

**Current Verible behavior**:
1. Preprocessor sees `` `uvm_object_utils_begin`` as undefined macro
2. Either passes through unchanged OR emits error
3. Parser sees macro call as invalid syntax
4. Parse fails with "Parse tree is null"

---

## Root Causes

### Issue 1: UVM Macro Library Not Recognized

**Problem**: Verible doesn't have built-in UVM macro definitions

**Current state**:
- Preprocessor only knows about macros defined in current file
- No awareness of external library macros (UVM, VCS, etc.)

**Solution needed**:
- Add UVM macro library to preprocessor
- ~50+ macro definitions
- Handle complex expansions

### Issue 2: Complex Macro Arguments

**Problem**: UVM macros take class names, expressions, and flags as arguments

**Example**:
```systemverilog
`uvm_object_param_utils_begin(cip_base_vseq#(RAL_T, CFG_T))
  `uvm_field_int(data, UVM_DEFAULT | UVM_HEX)
`uvm_object_param_utils_end
```

**Challenges**:
- Argument is parameterized class: `cip_base_vseq#(RAL_T, CFG_T)`
- Comma inside `#()` shouldn't split argument
- Bitwise OR in second argument

**Solution needed**:
- Smart argument parsing (track parentheses depth)
- Handle operators in arguments

### Issue 3: Nested Macros

**Problem**: UVM macros are nested (macro calls inside macro expansions)

**Example**:
```systemverilog
`uvm_object_utils_begin(MyClass)  // Outer macro
  `uvm_field_int(data, UVM_DEFAULT)  // Inner macro
`uvm_object_utils_end
```

**Current state**: Likely not handled properly

**Solution needed**:
- Recursive macro expansion
- Track expansion depth
- Prevent infinite recursion

### Issue 4: Token Pasting

**Problem**: UVM uses token pasting (``##``) extensively

**Example (from UVM source)**:
```systemverilog
`define uvm_object_utils(T) \
  typedef uvm_object_registry#(T, `"T`") type_id; \
  // Token pasting: stringify T
```

**Current state**: Unknown if supported

**Solution needed**:
- Token pasting operator support
- Stringification operator support

---

## Implementation Strategy

### Approach 1: Preprocessor Enhancement (RECOMMENDED)

**Rationale**: Most UVM issues are preprocessing problems, not grammar problems

**Implementation**:

1. **Add UVM Macro Library** (Week 3-4)
   - Create `verible/verilog/preprocessor/uvm-macros.cc`
   - Define 50+ common UVM macros
   - Hook into preprocessor

2. **Enhance Argument Parsing** (Week 5-6)
   - Improve macro argument tokenization
   - Track nesting depth for `()`, `<>`, `#()`
   - Handle commas inside nested structures

3. **Implement Recursive Expansion** (Week 7-8)
   - Support nested macro calls
   - Track expansion stack
   - Detect circular references

4. **Test & Validate** (Week 9-10)
   - Run 10 unit tests from Phase 1
   - Validate on OpenTitan files
   - Performance testing

**Pros**:
- ✅ Transparent to parser (parser sees expanded code)
- ✅ No grammar changes needed
- ✅ Reusable for other macro libraries
- ✅ Matches how compilers work

**Cons**:
- ⚠️ Need to maintain UVM macro definitions
- ⚠️ UVM version compatibility

---

### Approach 2: Grammar Enhancement (ALTERNATIVE)

**Rationale**: Add macro call as first-class grammar construct

**Implementation**:

**Grammar additions to `verilog.y`**:
```yacc
class_item
  : class_property
  | class_method
  | class_constraint
  | macro_call  // NEW: Recognize macro as class item
  ;

macro_call
  : MacroIdentifier '(' macro_arg_list_opt ')'
  | MacroIdentifier  // No arguments
  ;

macro_arg_list_opt
  : /* empty */
  | macro_arg_list
  ;

macro_arg_list
  : macro_arg
  | macro_arg_list ',' macro_arg
  ;

macro_arg
  : expression
  | class_type  // NEW: Allow class names
  | macro_call  // NEW: Allow nested macros
  ;
```

**Pros**:
- ✅ More flexible (can parse without expansion)
- ✅ Preserves original macro calls in CST

**Cons**:
- ⚠️ Requires extensive grammar changes
- ⚠️ May cause grammar conflicts
- ⚠️ Still need to understand macro semantics
- ⚠️ Doesn't solve all problems (expansion still needed)

---

### Approach 3: Hybrid (PRAGMATIC)

**Rationale**: Use preprocessor for expansion, enhance parser for edge cases

**Implementation**:

1. **Preprocessor** handles most cases:
   - Expand common UVM macros
   - Handle argument parsing
   - Recursive expansion

2. **Parser** gracefully handles failures:
   - If macro expansion fails, parse macro call as-is
   - Create `kUnexpandedMacro` CST node
   - Allow analysis tools to handle gracefully

**Example flow**:
```
Input: `uvm_object_utils(MyClass)
  ↓
Preprocessor attempts expansion
  ↓ (success)
Parser sees expanded code → Parse ✅
  ↓ (failure)
Parser sees macro call → Create kUnexpandedMacro node → Continue ✅
```

**Pros**:
- ✅ Best of both worlds
- ✅ Graceful degradation
- ✅ Handles unknown macros

---

## Recommended Implementation Plan

### Phase 2.1: Preprocessor Foundation (Weeks 3-4)

**Task 2.1.1**: Create UVM Macro Registry

**File**: `verible/verilog/preprocessor/uvm-macros.h`

```cpp
#ifndef VERIBLE_VERILOG_PREPROCESSOR_UVM_MACROS_H
#define VERIBLE_VERILOG_PREPROCESSOR_UVM_MACROS_H

#include <string>
#include <map>

namespace verilog {
namespace preprocessor {

// UVM macro definition structure
struct UVMMacroDef {
  std::string name;
  std::vector<std::string> parameters;
  std::string body;
};

// Registry of UVM macros
class UVMMacroRegistry {
public:
  static const std::map<std::string, UVMMacroDef>& GetMacros();
  static bool IsUVMMacro(const std::string& name);
  static const UVMMacroDef* GetMacro(const std::string& name);
};

}  // namespace preprocessor
}  // namespace verilog

#endif  // VERIBLE_VERILOG_PREPROCESSOR_UVM_MACROS_H
```

**File**: `verible/verilog/preprocessor/uvm-macros.cc`

```cpp
#include "verible/verilog/preprocessor/uvm-macros.h"

namespace verilog {
namespace preprocessor {

// Static registry (simplified - full version needs ~50 macros)
static const std::map<std::string, UVMMacroDef> kUVMMacros = {
  {
    "uvm_object_utils_begin",
    {
      "uvm_object_utils_begin",
      {"TYPE"},  // Parameter list
      // Body (simplified)
      "typedef uvm_object_registry#(TYPE, `\"TYPE`\") type_id; "
      "static function type_id get_type(); "
      "return type_id::get(); "
      "endfunction "
      "virtual function uvm_object create(string name=\"\"); "
      "TYPE tmp = new(); "
      "return tmp; "
      "endfunction "
      // ... more lines ...
    }
  },
  {
    "uvm_object_utils_end",
    {
      "uvm_object_utils_end",
      {},  // No parameters
      ""   // Just closes the block
    }
  },
  {
    "uvm_field_int",
    {
      "uvm_field_int",
      {"ARG", "FLAG"},
      // Field automation code
      "// Field automation for ARG with FLAG"
    }
  },
  // ... 47+ more macros ...
};

const std::map<std::string, UVMMacroDef>& UVMMacroRegistry::GetMacros() {
  return kUVMMacros;
}

bool UVMMacroRegistry::IsUVMMacro(const std::string& name) {
  return kUVMMacros.find(name) != kUVMMacros.end();
}

const UVMMacroDef* UVMMacroRegistry::GetMacro(const std::string& name) {
  auto it = kUVMMacros.find(name);
  return (it != kUVMMacros.end()) ? &it->second : nullptr;
}

}  // namespace preprocessor
}  // namespace verilog
```

**Testing**: Create unit test `uvm-macros_test.cc` to verify registry

---

### Phase 2.2: Enhance Preprocessor (Weeks 5-7)

**Task 2.2.1**: Integrate UVM Registry into Preprocessor

**File**: `verible/verilog/preprocessor/verilog-preprocess.cc`

**Modification locations** (need to analyze file first):
1. Macro lookup: Check UVM registry if user-defined not found
2. Macro expansion: Use UVM definition if available
3. Argument parsing: Enhance to handle complex arguments

**Pseudocode**:
```cpp
MacroDefinition* FindMacro(const std::string& name) {
  // Check user-defined macros first
  auto* user_macro = user_macros_.Find(name);
  if (user_macro) return user_macro;
  
  // Check UVM registry
  if (UVMMacroRegistry::IsUVMMacro(name)) {
    return ConvertUVMMacro(UVMMacroRegistry::GetMacro(name));
  }
  
  return nullptr;  // Undefined
}
```

---

### Phase 2.3: Argument Parsing Enhancement (Week 7-8)

**Challenge**: Parse complex macro arguments like `MyClass#(T1, T2)`

**Current problem**:
```systemverilog
`uvm_object_param_utils(MyClass#(T1, T2))
                                  ↑ comma here should NOT split argument
```

**Solution**: Track nesting depth

```cpp
std::vector<std::string> ParseMacroArguments(TokenStream& tokens) {
  std::vector<std::string> args;
  std::string current_arg;
  int paren_depth = 0;
  int angle_depth = 0;
  
  while (!tokens.AtEnd()) {
    Token t = tokens.Next();
    
    if (t.IsOpenParen()) {
      paren_depth++;
      current_arg += t.text;
    } else if (t.IsCloseParen()) {
      paren_depth--;
      if (paren_depth < 0) break;  // End of macro call
      current_arg += t.text;
    } else if (t.text == "<" || t.text == "#(") {
      angle_depth++;
      current_arg += t.text;
    } else if (t.text == ">") {
      angle_depth--;
      current_arg += t.text;
    } else if (t.text == "," && paren_depth == 0 && angle_depth == 0) {
      // Comma at top level - end of argument
      args.push_back(current_arg);
      current_arg.clear();
    } else {
      current_arg += t.text;
    }
  }
  
  if (!current_arg.empty()) {
    args.push_back(current_arg);
  }
  
  return args;
}
```

---

### Phase 2.4: CST Node Types (Week 9)

**File**: `verible/verilog/CST/verilog-nonterminals.h`

**Add enum values**:
```cpp
enum class NodeEnum {
  // ... existing 400+ values ...
  
  // UVM-specific nodes (for unexpanded macros or special handling)
  kUVMObjectUtilsMacro,
  kUVMComponentUtilsMacro,
  kUVMFieldMacro,
  kUVMDoMacro,
  kUnexpandedMacro,  // For macros that couldn't be expanded
};
```

**Usage**: Create these nodes when macro calls are recognized but can't be fully expanded

---

### Phase 2.5: Testing & Validation (Week 10)

**Tests**: Run all 10 tests from `verilog-parser-uvm-macros_test.cc`

**Expected progression**:
- Week 3-4: 0/10 passing (baseline)
- Week 5-6: 3-4/10 passing (basic macros)
- Week 7-8: 7-8/10 passing (complex args)
- Week 9: 9/10 passing (edge cases)
- Week 10: 10/10 passing ✅

**OpenTitan validation**:
- Parse all 89 failing UVM files
- **Target**: ≥80 files parse (90%)
- **Stretch**: ≥85 files parse (95%)

---

## Technical Risks

### Risk 1: UVM Macro Complexity

**Issue**: UVM macros can expand to 50+ lines with complex logic

**Mitigation**:
- Start with simplified expansions
- Gradually add complexity
- Test incrementally

**Fallback**: Document unsupported macro features

### Risk 2: Performance Impact

**Issue**: Preprocessing overhead may slow parsing

**Mitigation**:
- Cache expanded macros
- Profile and optimize
- Make UVM support opt-in via flag

**Acceptance**: <10% performance degradation

### Risk 3: Maintenance Burden

**Issue**: UVM evolves (new macros, changed expansions)

**Mitigation**:
- Comprehensive tests
- Version tracking
- Community contributions

**Fallback**: Support specific UVM version (1.2)

---

## Decision Points

### Decision 1: Approach Selection

**Options**:
- A) Preprocessor-only enhancement (RECOMMENDED)
- B) Grammar-only enhancement
- C) Hybrid approach

**Recommendation**: **Option A** - Preprocessor enhancement

**Rationale**:
- Most UVM issues are preprocessing problems
- Transparent to parser
- Matches compiler architecture
- Lower risk of grammar conflicts

**Decision date**: Week 3, Day 1

### Decision 2: UVM Version Support

**Options**:
- A) UVM 1.2 only (fixed point-in-time)
- B) UVM 1.1 + 1.2 (backwards compatible)
- C) Configurable via flag

**Recommendation**: **Option A** for initial release, **Option C** for future

**Rationale**:
- OpenTitan uses UVM 1.2
- Simpler to implement
- Can expand later

---

## Success Criteria

### Phase 2 Complete When:

- [x] UVM macro registry created (50+ macros)
- [x] Preprocessor integrated with registry
- [x] Complex argument parsing works
- [x] Nested macros expand correctly
- [x] All 10 unit tests pass
- [x] ≥80 OpenTitan files parse (90%)
- [x] No regressions in existing tests
- [x] Performance: <10% slowdown

---

## Next Steps (After Analysis)

1. **Week 3**: Create UVM macro registry + unit tests
2. **Week 4**: Integrate registry into preprocessor
3. **Week 5**: Enhance argument parsing
4. **Week 6**: Test complex argument cases
5. **Week 7**: Implement nested macro expansion
6. **Week 8**: Test nested cases
7. **Week 9**: Add CST node types, handle edge cases
8. **Week 10**: OpenTitan validation, performance tuning

---

## Appendix: UVM Macro List (Top 20)

Priority macros to implement first:

1. `uvm_object_utils_begin` / `_end`
2. `uvm_component_utils_begin` / `_end`
3. `uvm_object_utils`
4. `uvm_component_utils`
5. `uvm_object_param_utils_begin` / `_end`
6. `uvm_field_int`
7. `uvm_field_string`
8. `uvm_field_object`
9. `uvm_field_array_int`
10. `uvm_do`
11. `uvm_do_with`
12. `uvm_info`
13. `uvm_error`
14. `uvm_warning`
15. `uvm_fatal`
16. `uvm_create`
17. `uvm_send`
18. `uvm_create_on`
19. `uvm_do_on`
20. `uvm_analysis_imp_decl`

Full list: ~50+ macros needed for complete support

---

**Document Version**: 1.0  
**Status**: Analysis Complete, Ready for Implementation  
**Next**: Begin Phase 2.1 Implementation (Week 3)

