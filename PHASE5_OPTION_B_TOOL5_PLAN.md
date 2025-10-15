# Phase 5: Option B - Tool 5 Refactoring Engine Implementation Plan

## Current Status

**Risk Assessment Finding**: 🟡 MEDIUM-HIGH
- **Issue**: All 4 operations return `UnimplementedError`
- **Impact**: No actual code modification happens
- **Estimated Effort**: 6-8 hours

---

## What Needs Implementation

### Operation 1: ExtractFunction ⚠️
**Current**: Validation only, returns `UnimplementedError`
**Needed**:
1. Extract CST nodes from selection range
2. Analyze data flow (already has helper)
3. Generate function signature (already has helper)
4. Replace selection with function call
5. Insert new function definition
6. File I/O (read, modify, write)

### Operation 2: InlineFunction ⚠️
**Current**: Validation only, returns `UnimplementedError`
**Needed**:
1. Find function definition
2. Find all call sites
3. Replace each call with function body
4. Handle parameter substitution
5. File I/O

### Operation 3: ExtractVariable ⚠️
**Current**: Validation only, returns `UnimplementedError`
**Needed**:
1. Extract expression from selection
2. Generate variable declaration
3. Replace expression with variable reference
4. File I/O

### Operation 4: MoveDeclaration ⚠️
**Current**: Validation only, returns `UnimplementedError`
**Needed**:
1. Find declaration CST node
2. Calculate new insertion point
3. Remove from old location
4. Insert at new location
5. File I/O

---

## Implementation Strategy

### Phase 1: TDD Setup (30 min)
- Create integration tests that document current limitations
- Tests should pass initially but document UnimplementedError

### Phase 2: File I/O Foundation (1 hour)
- Create common file modification helper
- Pattern: read → backup → modify → write
- Reuse pattern from Tool 2 (Dead Code Eliminator)

### Phase 3: ExtractFunction (2-3 hours)
Most complex, but has best foundation:
- ✅ Data flow analysis helper exists
- ✅ Signature generation helper exists
- Need: CST node extraction by line/column
- Need: Text replacement logic

### Phase 4: ExtractVariable (1-2 hours)
Simpler version of ExtractFunction:
- Extract expression text
- Generate declaration
- Replace expression

### Phase 5: InlineFunction & MoveDeclaration (2-3 hours)
These are advanced operations:
- May implement basic versions
- Or document as "partial implementation"

---

## TDD Approach

### Test Strategy
1. Write test that documents current limitation
2. Test expects `UnimplementedError`
3. Implement actual functionality
4. Update test to verify actual behavior
5. Ensure all existing tests still pass

### Success Criteria per Operation
- ✅ Test with actual code modification
- ✅ Verify modified code is syntactically correct
- ✅ Verify backup file created
- ✅ Verify error handling
- ✅ All existing tests pass

---

## Pragmatic Scope Decision

Given 6-8 hour estimate and perfection goal, I propose:

### Option A: All 4 Operations Basic Implementation
- Each operation does minimal text modification
- May not handle all edge cases
- But demonstrates real functionality

### Option B: Focus on ExtractFunction + ExtractVariable (RECOMMENDED)
- These 2 operations fully production-ready
- InlineFunction & MoveDeclaration: documented limitations
- Better to have 2 perfect than 4 partial

### Option C: Just ExtractFunction Fully Complete
- Single operation, production quality
- Others remain with `UnimplementedError` but documented
- Shows capability, provides foundation

**Recommendation**: Option B - balance between coverage and quality

---

## Implementation Order

1. **File I/O Helper** (30 min)
2. **ExtractFunction Full** (2-3 hours)
3. **ExtractVariable Full** (1-2 hours)
4. **InlineFunction Framework** (1 hour)
5. **MoveDeclaration Framework** (1 hour)
6. **Integration Tests** (1 hour)

**Total**: 6.5-8.5 hours (matches estimate)

---

## Success Metrics

### Minimum (Option C)
- ✅ ExtractFunction works end-to-end
- ✅ Creates real function
- ✅ Replaces code with call
- ✅ All tests pass

### Target (Option B)
- ✅ ExtractFunction production-ready
- ✅ ExtractVariable production-ready
- ✅ InlineFunction & MoveDeclaration documented
- ✅ All tests pass

### Stretch (Option A)
- ✅ All 4 operations functional
- ✅ May have edge case limitations
- ✅ All tests pass

---

## Risk Mitigation

### Technical Risks
- **CST manipulation complexity**: Use text offsets like Tool 2
- **Syntax correctness**: Generate known-good patterns
- **Test compatibility**: Start with documentation tests

### Time Risks
- **Underestimate**: Focus on Option B or C
- **Overestimate**: Expand scope if time permits

---

## Next Steps

1. Confirm approach (A, B, or C)
2. Start with TDD documentation test
3. Implement file I/O helper
4. Proceed with ExtractFunction
5. Iterate based on time and quality

---

*Plan prepared for TRUE 100% production implementation*
*Following TDD and perfection standard*
*No hurry - quality over speed*
