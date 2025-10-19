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

**Document Status**: Draft  
**Last Updated**: October 19, 2025  
**Author**: Development Team  
**Review Status**: Pending

