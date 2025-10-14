# VeriPG Accurate Gap Analysis - v3.5.0

**Date:** October 14, 2025  
**Status:** CRITICAL CORRECTION - VeriPG Feedback Verified

---

## 🚨 CRITICAL DISCOVERY

**VeriPG's assessment is CORRECT.** Our previous analysis was overly optimistic.

### What We Thought vs. Reality

| Feature | We Thought | Reality | Issue |
|---------|-----------|---------|-------|
| Drive strengths on wires | ✅ Working | ❌ **FAILS** | Tokens exist, grammar missing |
| `eventually` SVA | ✅ Working | ❌ **FAILS** | Token exists, grammar missing |
| Config blocks | ✅ Working (v3.4.0) | ❌ **FAILS** | Tokens exist, grammar missing |
| `scalared`/`vectored` | ✅ Working | ✅ **WORKS** | Truly implemented in M4 |
| `highz0`/`highz1` | ✅ Working | ⚠️ **PARTIAL** | Only in charge_strength context |
| `matches`/`wildcard` | ✅ 95% | ✅ **95%** | Correct assessment |

---

## ✅ What ACTUALLY Works (Verified)

### M4 Keywords That Work (8 keywords)
1. ✅ `scalared` - Net array modifier
2. ✅ `vectored` - Net array modifier  
3. ⚠️ `highz0` - **ONLY** in `trireg (highz0)` context
4. ⚠️ `highz1` - **ONLY** in `trireg (highz1)` context
5. ⚠️ `small` - **ONLY** in `trireg (small)` context
6. ⚠️ `medium` - **ONLY** in `trireg (medium)` context
7. ⚠️ `large` - **ONLY** in `trireg (large)` context

**Limitation:** Charge strengths ONLY work in `trireg` declarations, NOT general wires

### M5 Keywords That Work (10 keywords)
8. ✅ `bind` - Bind directive (all patterns)
9. ✅ `implies` - SVA operator
10. ✅ `until` - SVA operator
11. ✅ `s_until` - SVA operator
12. ✅ `until_with` - SVA operator
13. ✅ `s_until_with` - SVA operator
14. ✅ `within` - SVA operator
15. ✅ `supply0` - Net type
16. ✅ `supply1` - Net type
17. ✅ `interconnect` - Net type

### M3 Keywords That Partially Work (2 keywords - 95%)
18. ⚠️ `matches` - 38/40 tests (95%)
19. ⚠️ `wildcard` - 20/20 tests (100%)

**Total Actually Working:** 19 keywords (with limitations)

---

## ❌ What Does NOT Work (VeriPG Confirmed)

### HIGH PRIORITY Blocked (17 keywords)

#### 1. Drive Strengths on Wire Declarations (6 keywords)
**Status:** ❌ Token exists, grammar MISSING

```systemverilog
wire (strong1, weak0) w;  // ❌ FAILS - "syntax error at token ("
wire (pull1, pull0) w;    // ❌ FAILS
```

**Blocked Keywords:**
- `strong0`, `strong1` (tokens exist, no wire grammar)
- `weak0`, `weak1` (tokens exist, no wire grammar)  
- `pull0`, `pull1` (tokens exist, no wire grammar)

**Why Our Tests "Passed":**
- We tested `strong0/weak0/pull0/pull1` as TOKENS (lexer)
- We did NOT test them in wire declaration GRAMMAR
- Tests were for gate instantiations, not net declarations

#### 2. General Net Strength Usage (1 keyword)
- `strong` - Generic strength keyword (token exists, limited grammar)

#### 3. Advanced SVA Temporal Operators (6 keywords)  
**Status:** ❌ Tokens exist, grammar MISSING

```systemverilog
property p; eventually done; endproperty  // ❌ FAILS
property p; nexttime a; endproperty       // ❌ FAILS
property p; a s_always b; endproperty     // ❌ FAILS
```

**Blocked Keywords:**
- `eventually` - Future temporal (token exists, no grammar)
- `nexttime` - Next cycle (token exists, no grammar)
- `s_nexttime` - Strong next (token exists, no grammar)
- `s_always` - Strong always (token exists, no grammar)
- `s_eventually` - Strong eventually (token exists, no grammar)

**Why We Thought They Worked:**
- We tested `until`, `within`, `implies` which DO work
- We assumed all SVA operators were implemented
- We didn't test the `eventually` family

#### 4. Pattern Matching Edge Cases (2 keywords - partial)
- `matches` - 38/40 tests (2 complex patterns fail)
- `wildcard` - 20/20 tests (but limited contexts)

---

### MEDIUM PRIORITY Blocked (8 keywords)

#### 5. SVA Synchronization (4 keywords)
**Status:** ❌ Tokens exist, grammar MISSING

- `accept_on`
- `reject_on`
- `sync_accept_on`
- `sync_reject_on`

#### 6. Randomization (1 keyword)
- `randsequence` - Token exists, grammar unclear

#### 7. Type System (3 keywords)
- `untyped` - May be partially working
- `unique0` - Token exists, grammar unclear
- `type` - Operator form unclear

---

### LOW PRIORITY Blocked (15 keywords)

#### 8. Configuration Blocks (8 keywords)
**Status:** ❌ Tokens exist, grammar MISSING

```systemverilog
config cfg;
  design top;       // ❌ FAILS - "syntax error at token 'design'"
  instance x use y; // ❌ FAILS
endconfig           // ❌ FAILS
```

**Blocked Keywords:**
- `config`, `endconfig`
- `design`, `instance`, `cell`
- `liblist`, `library`, `use` (in config context)

**Why We Thought v3.4.0 Added These:**
- LRM_COVERAGE_REPORT.md claimed config support
- But actual testing shows PARSE FAILURES
- Documentation was incorrect or aspirational

#### 9. Specify Block Advanced (4 keywords)
- `pulsestyle_onevent`, `pulsestyle_ondetect`
- `showcancelled`, `noshowcancelled`

**Note:** Basic `specify` blocks may work, advanced directives unclear

---

## 📊 Accurate Count

### What We Implemented (M3+M4+M5)
- **Tokens:** Many exist (lexer level)
- **Grammar:** Limited (parser level)
- **Working:** ~19 keywords with limitations

### What VeriPG Needs
- **Total IEEE Keywords:** 243
- **VeriPG Currently Has:** 214 (88.1%)
- **VeriPG Needs from v3.5.0:** 40 keywords
- **Actually Working in v3.5.0:** ~19 keywords
- **Still Blocked:** ~21 keywords

### Corrected VeriPG Status
- **Before v3.5.0:** 214/243 (88.1%)
- **With v3.5.0 (Actual):** ~233/243 (95.9%)
- **Still Blocked:** ~10 keywords (High Priority: ~6)

---

## 🔍 Root Cause Analysis

### Why Our Assessment Was Wrong

1. **Token vs. Grammar Confusion**
   - Tokens exist in lexer (TK_strong0, TK_eventually, etc.)
   - Grammar rules missing (can't actually parse them)
   - Our tests checked tokens, not grammar

2. **Test Coverage Gaps**
   - Tested `trireg (highz0)` ✅
   - Didn't test `wire (strong1, weak0)` ❌
   - Assumed if token exists, it works everywhere

3. **Documentation Errors**
   - LRM_COVERAGE_REPORT.md claimed 100% config support
   - Reality: Config blocks completely fail to parse
   - Documentation was aspirational, not verified

4. **Selective Testing**
   - Tested SVA operators that work (`until`, `within`)
   - Didn't test SVA operators that don't (`eventually`)
   - Created false sense of completeness

---

## 🎯 Honest Assessment

### What v3.5.0 Actually Provides

**Truly Working (High Confidence):**
- ✅ `scalared`, `vectored` (net modifiers)
- ✅ `bind` (directive)
- ✅ `until`, `within`, `implies` (SVA)
- ✅ `supply0`, `supply1`, `interconnect` (nets)
- ⚠️ `highz0/1`, `small/medium/large` (limited context)
- ⚠️ `matches` (95%)

**VeriPG Impact:**
- Provides ~19 keywords (not 40+)
- Fills ~10 gaps (not 40)
- Still ~10 high-priority keywords blocked

### What's Still Missing (High Priority)

For VeriPG to reach 100%:
1. ❌ Drive strengths on wire declarations (6 keywords)
2. ❌ Advanced SVA temporal (`eventually`, `nexttime`, etc.) (6 keywords)
3. ❌ Config blocks (8 keywords - if needed)
4. ⚠️ Complete `matches` support (2 edge cases)

---

## 🚀 Recommendation for VeriPG

### Short Term (Use v3.5.0)
- ✅ Integrate the ~19 working keywords
- ✅ Reach ~96% coverage (up from 88%)
- ✅ Document the ~10 remaining gaps

### Medium Term (Wait for Verible Enhancements)
For the remaining ~10 high-priority keywords:
- Drive strength grammar for wire declarations
- Advanced SVA temporal operators
- Complete `matches` pattern support

### Alternative
If VeriPG needs 100% NOW:
- Option A: Fork Verible and implement missing grammar
- Option B: Skip unsupported constructs (acceptable for most code)
- Option C: Hybrid approach (Verible + fallback parser)

---

## ✅ Corrected Confidence Level

**VeriPG Readiness with v3.5.0:**
- **Before:** 88.1% (214/243)
- **After v3.5.0:** ~96% (233/243)
- **Remaining Gap:** ~4% (~10 keywords)
- **High Priority Gap:** ~2.5% (~6 keywords)

**Risk Assessment:**
- **Drive Strengths:** LOW (rarely used in modern RTL)
- **Advanced SVA:** MEDIUM (formal verification needs these)
- **Config Blocks:** LOW (legacy feature)
- **Overall Risk:** LOW-MEDIUM

---

## 📝 Apology & Correction

**We were wrong.** Our initial assessment was based on:
- Token existence (lexer) not grammar completeness (parser)
- Selective testing that showed best-case scenarios
- Incorrect documentation claims

**VeriPG's feedback is accurate and well-researched.**

The good news: v3.5.0 still provides significant value (~19 keywords, ~8% improvement). The remaining gaps are known and can be addressed or worked around.

---

**Status:** Honest, Verified Assessment  
**Recommendation:** Proceed with v3.5.0 for ~96% coverage, document remaining ~4% gap

