# Enhancement Plan - v3.6.1

**Current Status:** v3.6.0 with 92.2% coverage (224/243 keywords)  
**Goal:** Address remaining edge cases to improve coverage and quality  
**Target:** v3.6.1 or v3.7.0 depending on scope

---

## 📊 Enhancement Opportunities

### High Impact (3 items)

#### 1. highz0/highz1 Charge Strengths ⚠️
**Current:** Test fails (60% charge strength coverage)  
**Issue:** Syntax may be incorrect in test  
**Effort:** Low (1-2 hours)  
**Impact:** Medium (completes charge strength support)

**Action:**
- Verify correct LRM syntax for charge strengths
- Test: `trireg (highz0, highz1) t;` vs other syntax
- Fix test or grammar as needed

#### 2. Config Library Clause ⚠️
**Current:** 7/8 config keywords working (87.5%)  
**Issue:** Complex `library` clause syntax fails  
**Effort:** Low-Medium (2-4 hours)  
**Impact:** Medium (completes config block support)

**Action:**
- Debug: `instance top use library work;`
- Check LRM Section 33.3 for correct syntax
- Add grammar rule variant if needed

#### 3. Drive Strength on Port Declarations ⚠️
**Current:** Works on nets, fails on ports  
**Issue:** Complex port syntax not supported  
**Effort:** Medium (4-6 hours)  
**Impact:** Medium (enables drive strength on module ports)

**Action:**
- Test: `module m(output (strong0, strong1) wire w);`
- Check if this is valid per LRM Section 23.2.2.3
- Add grammar rules to port_declaration if valid

---

### Medium Impact (2 items)

#### 4. pulsestyle_onevent/ondetect ⚠️
**Current:** 2/4 specify advanced keywords (50%)  
**Issue:** Advanced specify block features  
**Effort:** Low-Medium (2-4 hours)  
**Impact:** Low (niche SDF-specific features)

**Action:**
- Check LRM Section 31.5 for correct syntax
- Test simpler syntax variants
- May be LRM version differences

#### 5. matches Complex Patterns ⚠️
**Current:** 38/40 patterns (95%)  
**Issue:** Multi-level nested tagged unions  
**Effort:** High (8-12 hours)  
**Impact:** Low (rare edge cases)

**Action:**
- Review 2 failing patterns
- Determine if grammar fix is feasible
- May require significant refactoring

---

### Low Impact (1 item)

#### 6. Additional SVA sync variants
**Current:** Likely working but not tested separately  
**Issue:** sync_accept_on, sync_reject_on not tested individually  
**Effort:** Very Low (30 mins)  
**Impact:** Very Low (verification only)

**Action:**
- Add 2 explicit test cases
- Verify they work (likely already do)

---

## 🎯 Recommended Options

### Option A: Quick Wins (1-2 days)
**Target:** v3.6.1 patch release  
**Scope:**
- ✅ Fix highz0/highz1 (item #1)
- ✅ Fix config library clause (item #2)  
- ✅ Test sync_accept_on/reject_on (item #6)

**Expected Result:** 94-95% coverage, 31-32/35 tests passing

---

### Option B: Comprehensive Enhancement (1 week)
**Target:** v3.7.0 minor release  
**Scope:**
- ✅ All Option A items
- ✅ Drive strength on ports (item #3)
- ✅ pulsestyle_onevent/ondetect (item #4)

**Expected Result:** 96-97% coverage, 33-34/35 tests passing

---

### Option C: Complete Perfection (2-3 weeks)
**Target:** v3.8.0 or v4.0.0 major release  
**Scope:**
- ✅ All Option B items
- ✅ matches complex patterns (item #5) - requires significant refactoring

**Expected Result:** 98-100% coverage, 35/35 tests passing

---

### Option D: Accept Current State
**Target:** Keep v3.6.0 as-is  
**Scope:**
- ✅ No changes
- ✅ Document limitations clearly
- ✅ Focus on other features

**Rationale:** 92.2% is excellent, edge cases have workarounds

---

## 💡 My Recommendation

**Option A: Quick Wins** for v3.6.1

**Why:**
1. **High ROI:** Fix 3 issues in 1-2 days
2. **Measurable:** +2-3% coverage improvement
3. **Low Risk:** Small, localized changes
4. **User Impact:** Addresses most common edge cases

**Defer:**
- Drive strength on ports (Option B) - if users request
- pulsestyle (Option B) - niche feature
- matches complex patterns (Option C) - diminishing returns

---

## 📋 Implementation Plan (Option A)

### Day 1: Investigation & Fix highz0/highz1

**Tasks:**
1. Research LRM Section 28.15 (charge strengths)
2. Test various syntax variants
3. Fix test or add grammar rules
4. Verify all 5 charge strengths work

### Day 2: Fix config library & test sync variants

**Tasks:**
1. Research LRM Section 33.3 (config blocks)
2. Debug library clause syntax
3. Add grammar rule if needed
4. Add 2 sync test cases
5. Run full integration tests

### Day 3: Release v3.6.1

**Tasks:**
1. Build binary
2. Test with VeriPG
3. Update documentation
4. Tag and release

---

## 🎯 Success Criteria (Option A)

**Must Have:**
- ✅ highz0/highz1 working (5/5 charge strengths)
- ✅ Config library working (8/8 config keywords)
- ✅ sync_accept_on/reject_on verified (9/9 SVA sync)

**Nice to Have:**
- ✅ Coverage: 94-95% (230-232/243)
- ✅ Tests: 31-32/35 passing (88-91%)

**Release:**
- ✅ v3.6.1 tagged
- ✅ VeriPG verified
- ✅ Documentation updated

---

## 📊 Expected Coverage Improvement

| Version | Coverage | Tests | Improvement |
|---------|----------|-------|-------------|
| v3.6.0 (current) | 92.2% (224/243) | 29/35 (82.9%) | Baseline |
| v3.6.1 (Option A) | 94-95% (230-232) | 31-32/35 (88-91%) | +2-3% |
| v3.7.0 (Option B) | 96-97% (233-236) | 33-34/35 (94-97%) | +4-5% |
| v3.8.0 (Option C) | 98-100% (238-243) | 35/35 (100%) | +6-8% |

---

