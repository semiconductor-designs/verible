# Design: Macro-Aware Context Tracking

**Status**: Planning / Design Phase  
**Target**: v5.6.0 or later  
**Effort Estimate**: 2-6 weeks  
**Priority**: Medium (current heuristic works for all tested cases)

## Problem Statement

### Current Issue

After macro expansion, the parser loses track of statement boundaries, causing disambiguation failures for operators like `->`:

```systemverilog
`uvm_info(`gfn, "message", UVM_DEBUG)  // Expands to complex code...
-> host_item.byte_sampled_ev;           // Parser doesn't know we're at statement level
```

**Why it fails:**
1. Macro expands to multiple tokens
2. Parser state (`ExpectingBodyItemStart()`) doesn't track through expansion
3. Previous token after expansion doesn't indicate statement boundary
4. Result: `->` misinterpreted as `TK_LOGICAL_IMPLIES` instead of `TK_TRIGGER`

### Current Workaround (v5.4.2)

**Heuristic approach:**
- Check previous token type
- If identifier/operator: assume expression context (LOGICAL_IMPLIES)
- Otherwise in procedural body: assume statement context (TRIGGER)

**Pros:**
- Simple implementation (~24 lines)
- Works for 100% of tested cases
- Fast (no performance impact)
- Easy to understand and maintain

**Cons:**
- Not theoretically perfect
- May have undiscovered edge cases
- Doesn't solve root cause
- Technical debt

## Proposed Solutions

### Option 1: Macro Boundary Markers ⭐ RECOMMENDED

**Concept**: Inject special tokens at macro boundaries to preserve context.

**Implementation:**

```cpp
// In VerilogPreprocess::HandleMacroIdentifier()
void VerilogPreprocess::HandleMacroIdentifier(...) {
  // Inject start marker
  output_stream_ << "<MACRO_START:" << macro_name << ">";
  
  // Expand macro
  ExpandMacro(macro_name, args, output_stream_);
  
  // Inject end marker
  output_stream_ << "<MACRO_END:" << macro_name << ">";
}
```

**Lexer changes:**

```cpp
// In verilog.lex
<MACRO_START:{ID}>    { return TK_MACRO_BOUNDARY_START; }
<MACRO_END:{ID}>      { return TK_MACRO_BOUNDARY_END; }
```

**Parser changes:**

```cpp
// In verilog-lexical-context.cc
void LexicalContext::AdvanceToken(const TokenInfo* token) {
  if (token->token_enum() == TK_MACRO_BOUNDARY_START) {
    macro_depth_++;
    saved_context_stack_.push(current_state_);
  } else if (token->token_enum() == TK_MACRO_BOUNDARY_END) {
    macro_depth_--;
    if (!saved_context_stack_.empty()) {
      current_state_ = saved_context_stack_.top();
      saved_context_stack_.pop();
    }
  }
  // ... rest of token processing
}
```

**Advantages:**
- ✅ Preserves exact context through macros
- ✅ No heuristics needed
- ✅ Works for all macro patterns
- ✅ Minimal performance impact
- ✅ Easier to debug (can see macro boundaries)

**Disadvantages:**
- ⚠️ Moderate implementation effort (2-3 weeks)
- ⚠️ Requires lexer, preprocessor, and parser changes
- ⚠️ Need to handle nested macros correctly
- ⚠️ Marker tokens visible in debug output

**Effort**: 2-3 weeks
**Risk**: Medium

### Option 2: Context Stack

**Concept**: Maintain explicit context stack that persists through macro expansion.

**Implementation:**

```cpp
class MacroContextStack {
 private:
  struct ContextFrame {
    bool expecting_statement;
    bool in_task_body;
    bool in_function_body;
    int balance_depth;
    // ... other relevant state
  };
  
  std::vector<ContextFrame> stack_;
  
 public:
  void PushContext(const ContextFrame& ctx) {
    stack_.push_back(ctx);
  }
  
  void PopContext() {
    if (!stack_.empty()) stack_.pop_back();
  }
  
  ContextFrame CurrentContext() const {
    return stack_.empty() ? ContextFrame{} : stack_.back();
  }
  
  void RestoreContext(LexicalContext* ctx) {
    if (!stack_.empty()) {
      const auto& frame = stack_.back();
      ctx->in_task_body_ = frame.in_task_body;
      ctx->in_function_body_ = frame.in_function_body;
      // ... restore other state
    }
  }
};
```

**Usage:**

```cpp
// Before macro expansion
context_stack_.PushContext({
  .expecting_statement = ExpectingStatement(),
  .in_task_body = in_task_body_,
  .in_function_body = in_function_body_,
  // ...
});

// After macro expansion
context_stack_.RestoreContext(this);
context_stack_.PopContext();
```

**Advantages:**
- ✅ Precise context tracking
- ✅ No token stream modifications
- ✅ Can track arbitrary state

**Disadvantages:**
- ⚠️ Higher complexity (3-4 weeks)
- ⚠️ Need to identify all relevant state to save
- ⚠️ May miss edge cases if state is incomplete
- ⚠️ Harder to debug (context is implicit)

**Effort**: 3-4 weeks
**Risk**: Medium-High

### Option 3: Two-Pass Preprocessing

**Concept**: First pass expands macros with annotations, second pass parses with context.

**Implementation:**

**Pass 1: Preprocessing with annotations**
```cpp
struct AnnotatedToken {
  std::string text;
  int token_type;
  bool from_macro;
  std::string macro_name;
  ParserContext context_before;
  ParserContext context_after;
};

std::vector<AnnotatedToken> PreprocessWithAnnotations(const std::string& source) {
  // Expand macros
  // Annotate each token with context information
  // Return annotated token stream
}
```

**Pass 2: Parsing with annotations**
```cpp
void Parser::Parse(const std::vector<AnnotatedToken>& tokens) {
  for (const auto& token : tokens) {
    if (token.from_macro) {
      // Use annotated context instead of inferring
      context_ = token.context_before;
    }
    // Parse token normally
  }
}
```

**Advantages:**
- ✅ Complete context information
- ✅ Clean separation of preprocessing and parsing
- ✅ Can debug each pass independently

**Disadvantages:**
- ⚠️ Major architectural change (4-6 weeks)
- ⚠️ Requires storing/managing annotations
- ⚠️ Performance impact (two passes)
- ⚠️ High risk of breaking existing functionality

**Effort**: 4-6 weeks
**Risk**: High

## Recommendation

### Start with Option 1: Macro Boundary Markers

**Rationale:**
1. Best balance of effort vs. correctness
2. Clean, understandable approach
3. Moderate risk level
4. Can be implemented incrementally
5. Easy to test and debug

**Implementation Plan:**

### Phase 1: Proof of Concept (Week 1)
1. Add TK_MACRO_BOUNDARY_START/END tokens to lexer
2. Inject markers in simple macro expansions
3. Test with basic examples
4. Validate approach

### Phase 2: Full Implementation (Week 2)
1. Handle nested macros correctly
2. Track macro depth in LexicalContext
3. Save/restore context on boundaries
4. Update ExpectingStatement() logic

### Phase 3: Testing and Refinement (Week 3)
1. Test with OpenTitan corpus
2. Test with Ibex, PULPino
3. Add comprehensive unit tests
4. Fix any edge cases

### Phase 4: Documentation and Release (Week 4+)
1. Update documentation
2. Write migration guide
3. Release as v5.6.0

## Alternative: Enhance Current Heuristic

If macro boundary markers prove too complex, we can enhance the existing heuristic:

### Enhanced Heuristic with Multi-Token Lookahead

```cpp
class TokenHistory {
 private:
  static constexpr int kHistorySize = 3;
  std::array<const TokenInfo*, kHistorySize> history_;
  int current_index_ = 0;
  
 public:
  void AddToken(const TokenInfo* token) {
    history_[current_index_ % kHistorySize] = token;
    current_index_++;
  }
  
  bool PreviousNTokensMatch(std::initializer_list<int> pattern) const {
    int idx = current_index_ - 1;
    for (auto it = pattern.rbegin(); it != pattern.rend(); ++it) {
      if (idx < 0) return false;
      if (history_[idx % kHistorySize]->token_enum() != *it) return false;
      idx--;
    }
    return true;
  }
};
```

**Usage:**

```cpp
// In InterpretToken for _TK_RARROW
if (token_history_.PreviousNTokensMatch({';', ')'})) {
  // Pattern: statement(); \n -> event
  // This is a trigger, not implies
  return TK_TRIGGER;
}
```

**Advantages:**
- ✅ Minimal changes to existing code
- ✅ Low risk
- ✅ Quick to implement (1 week)
- ✅ Can handle more patterns

**Disadvantages:**
- ⚠️ Still heuristic-based
- ⚠️ May need continuous refinement
- ⚠️ Doesn't solve root cause

**Effort**: 1 week
**Risk**: Low

## Timeline and Milestones

### Short-term (v5.5.0 - Current)
- ✅ Heuristic approach working
- ✅ 100% success on tested corpus
- ✅ Documentation complete

### Medium-term (v5.6.0 - 3-6 months)
- Implement Option 1 (Macro Boundary Markers)
- OR enhance heuristic with multi-token lookahead
- Comprehensive testing across multiple projects
- Performance validation

### Long-term (v6.0 - 6-12 months)
- Consider Option 2 or 3 if needed
- Full macro-aware parser
- Contribute improvements upstream to chipsalliance/verible
- Comprehensive parser modernization

## Success Criteria

### For Macro Boundary Markers Implementation

1. **Correctness**: 100% parsing success on:
   - OpenTitan corpus (maintained)
   - Ibex RISC-V
   - PULPino
   - Synthetic edge cases

2. **Performance**: No degradation >5%
   - Parse timing maintained
   - Memory usage acceptable

3. **Compatibility**: No regressions
   - All existing tests pass
   - All existing features work

4. **Maintainability**: Code quality
   - Clear implementation
   - Comprehensive tests
   - Good documentation

## Risks and Mitigation

### Risk 1: Breaks Existing Functionality
**Mitigation**: Comprehensive testing, feature flag for rollback

### Risk 2: Performance Degradation
**Mitigation**: Benchmark before/after, optimize if needed

### Risk 3: Scope Creep
**Mitigation**: Strict phased approach, clear milestones

### Risk 4: Upstream Conflicts
**Mitigation**: Track upstream changes, regular rebasing

## Open Questions

1. **Should markers be visible in CST?**
   - Probably no - filter them out like other preprocessor artifacts

2. **How to handle macro-in-macro?**
   - Stack depth tracking, nested markers

3. **Performance impact of marker injection?**
   - Benchmark needed, likely negligible

4. **Compatibility with existing tools?**
   - Markers should be internal only

## References

- **Current Implementation**: `verible/verilog/parser/verilog-lexical-context.cc` (lines 698-721)
- **Preprocessor**: `verible/verilog/preprocessor/verilog-preprocess.cc`
- **Lexer**: `verible/verilog/parser/verilog.lex`
- **Related Issue**: Event trigger disambiguation (v5.4.2)

---

**Document Status**: Implementation Phase - v5.6.0  
**Last Updated**: October 19, 2025  
**Author**: Development Team  
**Review Status**: Approved for Implementation

---

## Implementation Details (v5.6.0)

### Detailed Code Examples - Option 1 (Macro Boundary Markers)

#### Example 1: Simple Macro Expansion

**Source Code**:
```systemverilog
`define LOG(msg) $display(msg)

task test();
  `LOG("Starting")
  -> my_event;
endtask
```

**After Preprocessing (with markers)**:
```
task test ( ) ;
<MACRO_START:LOG>
$display ( "Starting" )
<MACRO_END:LOG>
-> my_event ;
endtask
```

**Context Flow**:
```
Line 1: task test()     → in_task_body = true, expecting_statement = true
Line 2: MACRO_START     → Save context (depth 0 → 1)
Line 3: $display(...)   → Normal parsing
Line 4: MACRO_END       → Restore context (depth 1 → 0)
Line 5: ->              → ExpectingStatement() = true → TK_TRIGGER ✅
```

#### Example 2: Nested Macro Expansion

**Source Code**:
```systemverilog
`define OUTER(x) `INNER(x) + 1
`define INNER(y) y * 2

task test();
  `OUTER(5)
  -> event;
endtask
```

**After Preprocessing**:
```
task test ( ) ;
<MACRO_START:OUTER>
<MACRO_START:INNER>
5 * 2
<MACRO_END:INNER>
+ 1
<MACRO_END:OUTER>
-> my_event ;
endtask
```

**Context Stack Evolution**:
```
Depth 0: task body, expecting_statement=true
  ↓ MACRO_START:OUTER
Depth 1: save state[0], in_task=true
  ↓ MACRO_START:INNER  
Depth 2: save state[1], in_task=true
  ↓ tokens: 5 * 2
Depth 2: MACRO_END:INNER
  ↓ restore state[1]
Depth 1: in_task=true (preserved)
  ↓ tokens: + 1
Depth 1: MACRO_END:OUTER
  ↓ restore state[0]
Depth 0: in_task=true, expecting_statement=true
  ↓ token: ->
Result: TK_TRIGGER ✅ (context preserved through 2 levels)
```

#### Example 3: Macro in Expression vs Statement

**Source Code**:
```systemverilog
`define VALUE 42

task test();
  // Case 1: In expression
  result = (condition -> `VALUE);  // -> is LOGICAL_IMPLIES
  
  // Case 2: As statement
  `VALUE;
  -> event;  // -> is TRIGGER
endtask
```

**Context Analysis**:
```
Case 1:
  previous_token = '('
  macro_depth = 0 (VALUE doesn't trigger markers, it's just substitution)
  Result: TK_LOGICAL_IMPLIES ✅

Case 2:
  After macro: previous_token = ';'
  expecting_statement = true
  Result: TK_TRIGGER ✅
```

### Integration Points

#### 1. Lexer (`verilog.lex`)

**Location**: Line ~837, after existing token rules

```lex
/* Macro boundary markers */
"<MACRO_START:"[a-zA-Z_][a-zA-Z0-9_]*">" {
  yylval->SetToken(TokenInfo(TK_MACRO_BOUNDARY_START, yytext));
  return TK_MACRO_BOUNDARY_START;
}

"<MACRO_END:"[a-zA-Z_][a-zA-Z0-9_]*">" {
  yylval->SetToken(TokenInfo(TK_MACRO_BOUNDARY_END, yytext));
  return TK_MACRO_BOUNDARY_END;
}
```

#### 2. Token Enum (`verilog-token-enum.h`)

**Location**: After line ~200

```cpp
// Macro boundary markers (v5.6.0)
TK_MACRO_BOUNDARY_START = 450,
TK_MACRO_BOUNDARY_END = 451,
```

#### 3. Preprocessor (`verilog-preprocess.cc`)

**Location**: In `HandleMacroIdentifier()`, around line 450-550

**Before**:
```cpp
absl::Status VerilogPreprocess::HandleMacroIdentifier(
    const TokenInfo& macro_id_token) {
  const absl::string_view macro_name = macro_id_token.text();
  
  // Find and expand macro
  const MacroDefinition* macro = FindOrNull(macro_definitions_, macro_name);
  if (!macro) {
    return NotFoundError(...);
  }
  
  // Expand
  RETURN_IF_ERROR(ExpandMacro(*macro, args, output_stream_));
  
  return absl::OkStatus();
}
```

**After**:
```cpp
absl::Status VerilogPreprocess::HandleMacroIdentifier(
    const TokenInfo& macro_id_token) {
  const absl::string_view macro_name = macro_id_token.text();
  
  // Find macro
  const MacroDefinition* macro = FindOrNull(macro_definitions_, macro_name);
  if (!macro) {
    return NotFoundError(...);
  }
  
  // [NEW] Inject start marker
  output_stream_ << "<MACRO_START:" << macro_name << ">";
  
  // Expand macro (existing code)
  RETURN_IF_ERROR(ExpandMacro(*macro, args, output_stream_));
  
  // [NEW] Inject end marker
  output_stream_ << "<MACRO_END:" << macro_name << ">";
  
  return absl::OkStatus();
}
```

#### 4. Parser Context (`verilog-lexical-context.h`)

**Location**: Private members section

```cpp
class LexicalContext {
 private:
  // [NEW v5.6.0] Macro context tracking
  int macro_depth_ = 0;
  std::stack<ContextState> saved_context_stack_;
  
  // [NEW v5.6.0] Context state structure
  struct ContextState {
    bool expecting_statement;
    bool in_task_body;
    bool in_function_body;
    bool in_initial_always_final_construct;
    int balance_depth;
    const TokenInfo* previous_token;
    
    ContextState() : expecting_statement(false), in_task_body(false),
                     in_function_body(false), 
                     in_initial_always_final_construct(false),
                     balance_depth(0), previous_token(nullptr) {}
  };
  
  // [NEW v5.6.0] Context management
  ContextState SaveCurrentContext() const;
  void RestoreContext(const ContextState& state);
};
```

#### 5. Parser Context (`verilog-lexical-context.cc`)

**Location**: In `InterpretToken()`, before line 670

```cpp
int LexicalContext::InterpretToken(int token_enum, 
                                    const TokenInfo* token) {
  // [NEW v5.6.0] Handle macro boundary markers
  switch (token_enum) {
    case TK_MACRO_BOUNDARY_START: {
      VLOG(2) << "==> MACRO_START (depth " << macro_depth_ 
              << " → " << (macro_depth_ + 1) << ")";
      
      // Save context before entering macro
      ContextState state = SaveCurrentContext();
      saved_context_stack_.push(state);
      macro_depth_++;
      
      // Log saved state
      VLOG(2) << "    Saved: task=" << state.in_task_body
              << " function=" << state.in_function_body
              << " expecting=" << state.expecting_statement;
      
      return token_enum;  // Pass through
    }
    
    case TK_MACRO_BOUNDARY_END: {
      VLOG(2) << "==> MACRO_END (depth " << macro_depth_ 
              << " → " << (macro_depth_ - 1) << ")";
      
      // Restore context after exiting macro
      if (!saved_context_stack_.empty()) {
        ContextState state = saved_context_stack_.top();
        saved_context_stack_.pop();
        RestoreContext(state);
        
        VLOG(2) << "    Restored: task=" << in_task_body_
                << " function=" << in_function_body_;
      } else {
        LOG(WARNING) << "Context stack underflow at MACRO_END";
      }
      
      macro_depth_--;
      return token_enum;  // Pass through
    }
    
    // ... rest of existing cases ...
  }
}
```

### Edge Case Handling

#### Recursive Macros

**Problem**: Infinite expansion
```systemverilog
`define A `B
`define B `A
```

**Solution**: Already handled by existing recursion depth limit in preprocessor
```cpp
// In verilog-preprocess.h
static constexpr int kMaxMacroExpansionDepth = 100;
```

Markers still injected, but expansion stops at depth limit.

#### Macro-in-Macro with Different Contexts

**Scenario**:
```systemverilog
`define EXPR (a -> b)
`define STMT -> event

task test();
  result = `EXPR;  // -> should be LOGICAL_IMPLIES
  `STMT;           // -> should be TRIGGER
endtask
```

**Solution**: Context from point of invocation is preserved
```
result = <MACRO_START:EXPR> ( a -> b ) <MACRO_END:EXPR> ;
         ^^^^^ saved context: in_expression ^^^^^

<MACRO_START:STMT> -> event <MACRO_END:STMT> ;
^^^^^ saved context: expecting_statement ^^^^^
```

#### Unbalanced Markers (Error Recovery)

**Problem**: Parser crash if START without END
**Solution**: Graceful degradation

```cpp
case TK_MACRO_BOUNDARY_END:
  if (saved_context_stack_.empty()) {
    // Log warning but don't crash
    LOG(WARNING) << "Unbalanced MACRO_END at " << token->location();
    // Fall back to heuristic
    return token_enum;
  }
  // ... normal restore ...
```

---

## Test Coverage Matrix

### Unit Tests by Category

| Test ID | Category | Description | Expected Result |
|---------|----------|-------------|-----------------|
| T01 | Basic | Simple macro expansion | Markers recognized |
| T02 | Basic | Context save/restore | State preserved |
| T03 | Basic | Macro depth tracking | Increments/decrements |
| T04 | Basic | Empty stack handling | No crash |
| T05 | Basic | Deep nesting (20 levels) | No overflow |
| T06 | Arrow | Event trigger after macro | TK_TRIGGER |
| T07 | Arrow | Logical implies in macro | TK_LOGICAL_IMPLIES |
| T08 | Arrow | Nested macro event trigger | TK_TRIGGER |
| T09 | Arrow | Macro in task body | Context preserved |
| T10 | Arrow | Macro in module body | Context preserved |
| T11 | Nested | Two-level nesting | Both contexts saved |
| T12 | Nested | Three-level nesting | Stack depth = 3 |
| T13 | Nested | Macro expanding to macro | Indirect handled |
| T14 | Nested | Recursive detection | Stops at limit |
| T15 | Nested | Unbalanced markers | Graceful recovery |
| T16 | Edge | Empty macro body | No markers |
| T17 | Edge | Whitespace in expansion | Preserves spacing |
| T18 | Edge | Comments in macro | Handled correctly |
| T19 | Edge | Multiple arrows in macro | Each disambiguated |
| T20 | Edge | Mixed heuristic/markers | Both work together |
| T21 | Perf | Benchmark vs v5.5.0 | <5% slower |
| T22 | Perf | Deep nesting performance | <10% overhead |

### Integration Test Coverage

| Corpus | Files | Current Rate | Target Rate | Test Focus |
|--------|-------|--------------|-------------|------------|
| OpenTitan | 3911 | 100% | 100% | UVM heavy macros |
| Ibex | 637 | 97% | 97%+ | RTL moderate macros |
| PULPino | 44 | 97% | 97%+ | Mixed RTL/DV |
| Synthetic | 100+ | N/A | 100% | All edge cases |

---

## Performance Analysis

### Theoretical Overhead

**Per macro expansion**:
1. Marker injection: ~10-20 CPU cycles
2. Context save: ~50 CPU cycles
3. Context restore: ~50 CPU cycles
4. Total: ~110-120 cycles per macro

**Comparison**:
- Macro expansion itself: ~1000-5000 cycles
- Marker overhead: ~2-5% of expansion cost
- **Negligible**

### Measured Overhead (Projected)

**Typical file** (100 macros, 1000 lines):
- v5.5.0: 10ms
- v5.6.0: 10.2ms
- Overhead: 2%

**Macro-heavy file** (1000 macros, 5000 lines):
- v5.5.0: 50ms
- v5.6.0: 52.5ms
- Overhead: 5%

**Target**: <5% average, <10% worst case ✅

---

## Lessons Learned (Post-Implementation)

*To be filled after implementation completes*

---

**Document Status**: Updated for v5.6.0 Implementation  
**Last Updated**: October 19, 2025  
**Author**: Development Team  
**Review Status**: Approved - Implementation Starting

