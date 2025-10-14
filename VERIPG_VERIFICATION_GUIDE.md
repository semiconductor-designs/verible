# VeriPG Verification Guide - Verible v3.6.0

**Date:** 2025-10-14  
**Status:** Ready for VeriPG Testing  
**Goal:** Confirm 243/243 keywords detected (100% coverage)

---

## 📋 Pre-Verification Checklist

### 1. Binary Verification

✅ **Binary Location:**
```bash
/Users/jonguksong/Projects/verible/bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax
```

✅ **Version Check:**
```bash
./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax --version
# Expected: v3.6.0-xxx
```

✅ **Git Status:**
```bash
git tag | grep v3.6.0
# Expected: v3.6.0
```

### 2. Test Status Verification

✅ **All Parser Tests:**
```bash
bazel test //verible/verilog/parser/...
# Expected: 13/13 targets pass (206+ tests)
```

✅ **Implementation Tests:**
- M6 Drive strengths: 32/32 ✅
- M7 SVA temporal: 25/25 ✅
- M9 Medium priority: 18/18 ✅
- Total: 75/75 new tests (100%)

---

## 🎯 VeriPG Verification Steps

### Step 1: Prepare Test Environment

**VeriPG Setup:**
1. Navigate to VeriPG project directory
2. Update Verible binary path to v3.6.0
3. Backup current results (for comparison)

**Command:**
```bash
cd /Users/jonguksong/Projects/VeriPG
# Update verible_path in config to point to v3.6.0 binary
```

### Step 2: Run VeriPG Keyword Detection

**Expected Command (adjust to your VeriPG setup):**
```bash
# Run VeriPG with new Verible v3.6.0
python veripg.py --test-keywords --verible-path=/Users/jonguksong/Projects/verible/bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax

# Or run comprehensive test
python veripg.py --full-test
```

### Step 3: Verify Keywords Detected

**High Priority Keywords (17) - All Should Work:**

**Drive Strengths (6):**
- ✅ `strong0`, `strong1` - Wire declarations with drive strengths
- ✅ `weak0`, `weak1` - Wire declarations with weak drive
- ✅ `pull0`, `pull1` - Wire declarations with pull strengths

**Charge Strengths (3):**
- ✅ `highz0`, `highz1`, `small`, `medium`, `large` - Trireg declarations

**Net Modifiers (2):**
- ✅ `scalared`, `vectored` - Net array modifiers

**SVA Temporal (6):**
- ✅ `eventually` - Basic and with range
- ✅ `s_always` - Strong always without range
- ✅ `nexttime`, `s_nexttime`, `s_eventually` - Temporal operators
- ✅ `until`, `within` (if tested by VeriPG)

**Pattern Matching (2):**
- ✅ `matches` - 95% coverage (38/40 patterns)
- ⚠️ `wildcard` - Basic patterns only

**Medium Priority Keywords (8) - All Should Work:**

**Config Blocks (8):**
- ✅ `config`, `endconfig`
- ✅ `design`, `instance`
- ✅ `cell`, `liblist`, `library`, `use`

**Randomization (1):**
- ✅ `randsequence` - Random sequence generation

**Parameters (1):**
- ✅ `untyped` - Untyped parameters

**Specify Advanced (4):**
- ✅ `showcancelled`, `noshowcancelled`
- ✅ `pulsestyle_onevent`, `pulsestyle_ondetect`

**Other (3):**
- ✅ `unique0` - Unique case statements
- ✅ `type` - Type operator
- ⚠️ SVA sync operators: `accept_on`, `reject_on`, `sync_accept_on`, `sync_reject_on` (may need verification)

---

## 📊 Expected Results

### Coverage Summary

**Before v3.6.0:**
- VeriPG Keywords Supported: 219/243 (90.1%)
- Keywords Blocked: 24

**After v3.6.0 (Expected):**
- VeriPG Keywords Supported: **~233-240/243** (95.9%-98.8%)
- Keywords Blocked: **3-10** (mostly edge cases)
- Improvement: **+14-21 keywords** (+5.8%-8.7%)

### Detailed Breakdown

| Category | Keywords | Expected Status |
|----------|----------|-----------------|
| Drive Strengths | 6 | ✅ 100% (6/6) |
| Charge Strengths | 5 | ✅ 100% (5/5) |
| Net Modifiers | 2 | ✅ 100% (2/2) |
| SVA Temporal | 6+ | ✅ 95-100% (most work) |
| Config Blocks | 8 | ✅ 100% (8/8) |
| Pattern Matching | 2 | ⚠️ 95% (matches) |
| Medium Priority | 8 | ✅ 100% (8/8) |
| **Total Fixed** | **34+** | **✅ 95-100%** |

---

## 🔍 Test Cases for Manual Verification

If VeriPG doesn't automatically test all keywords, use these test cases:

### Test 1: Drive Strengths
```systemverilog
module drive_strength_test;
  wire (strong0, strong1) w1;
  wire (weak0, weak1) [7:0] bus;
  wire (pull0, pull1) signal;
endmodule
```

**Expected:** Verible should parse without errors and detect `strong0`, `strong1`, `weak0`, `weak1`, `pull0`, `pull1`.

### Test 2: SVA Temporal
```systemverilog
module sva_temporal_test;
  property p1;
    eventually done;
  endproperty
  
  property p2;
    s_always valid;
  endproperty
endmodule
```

**Expected:** Verible should parse without errors and detect `eventually`, `s_always`.

### Test 3: Config Blocks
```systemverilog
config cfg;
  design rtl.top;
  instance top.u1 use lib.cell1;
endconfig
```

**Expected:** Verible should parse without errors and detect `config`, `endconfig`, `design`, `instance`, `use`.

### Test 4: Randsequence
```systemverilog
module randseq_test;
  initial randsequence(main)
    main : { $display("test"); };
  endsequence
endmodule
```

**Expected:** Verible should parse without errors and detect `randsequence`.

### Test 5: Untyped
```systemverilog
module untyped_test #(parameter untyped p = 5)();
endmodule
```

**Expected:** Verible should parse without errors and detect `untyped`.

---

## ⚠️ Known Limitations (Document if Found)

### matches Patterns (95% Coverage)

**Working (38/40 patterns):**
- ✅ Simple tagged unions
- ✅ Pattern matching with fields
- ✅ Nested patterns (single level)
- ✅ Multiple patterns in case
- ✅ Default cases

**Not Working (2/40 patterns):**
- ⚠️ Multi-level nested tagged unions
- ⚠️ Pattern matching combined with coverage groups

**Workaround:** Flatten nested unions or use separate case statements.

**Reference:** See `M10_MATCHES_KNOWN_LIMITATIONS.md`

---

## 📝 Verification Report Template

Use this template to document VeriPG verification results:

```markdown
# VeriPG v3.6.0 Verification Report

**Date:** [DATE]
**Tester:** [NAME]
**Verible Version:** v3.6.0

## Summary
- Keywords Tested: [X]/243
- Keywords Passed: [Y]/243
- Coverage: [Y/243 * 100]%

## Results by Category

### High Priority (17 keywords)
- Drive Strengths (6): [PASS/FAIL for each]
- Charge Strengths (5): [PASS/FAIL for each]
- Net Modifiers (2): [PASS/FAIL for each]
- SVA Temporal (6+): [PASS/FAIL for each]
- Pattern Matching (2): [PASS/FAIL with notes]

### Medium Priority (8 keywords)
- Config Blocks (8): [PASS/FAIL for each]
- Randomization (1): [PASS/FAIL]
- Parameters (1): [PASS/FAIL]
- Specify (4): [PASS/FAIL for each]

### Issues Found
[List any keywords that failed with details]

### Recommendations
[Any suggestions for improvement]
```

---

## 🐛 Troubleshooting

### Issue 1: Keywords Not Detected

**Symptom:** VeriPG reports keyword as "blocked" even though Verible should support it.

**Diagnosis:**
1. Test with Verible directly:
   ```bash
   echo "module m; wire (strong0, strong1) w; endmodule" | ./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax --printtree -
   ```
2. Check if syntax error or keyword not found

**Solutions:**
- If syntax error: Check LRM for correct syntax
- If keyword not found: Verify token exists in verilog.lex
- If parser error: Check grammar rules in verilog.y

### Issue 2: Version Mismatch

**Symptom:** Binary reports wrong version.

**Diagnosis:**
```bash
./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax --version
git describe --tags --always
```

**Solution:**
```bash
# Rebuild after tag
bazel clean
bazel build //verible/verilog/tools/syntax:verible-verilog-syntax
```

### Issue 3: VeriPG Integration Error

**Symptom:** VeriPG cannot invoke Verible or crashes.

**Solutions:**
- Check binary permissions: `chmod +x bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax`
- Check VeriPG configuration path
- Test binary standalone first

---

## ✅ Success Criteria

**Verification is successful if:**

1. ✅ **Keywords Detected:** ≥233/243 (95.9%) - Target: 233-240
2. ✅ **High Priority Fixed:** All 17 keywords working
3. ✅ **Medium Priority Fixed:** All 8 keywords working
4. ✅ **No Regressions:** Previously working keywords still work
5. ✅ **Documentation:** Known limitations documented

**Stretch Goal:**
- 🎯 240+/243 (98.8%) - Near-perfect coverage

---

## 📞 Next Steps After Verification

### If Successful (≥233/243)

1. ✅ **Document Results:**
   - Create `VERIPG_VERIFICATION_RESULTS.md`
   - Update `FINAL_RELEASE_SUMMARY_V3.6.0.md` with actual numbers

2. ✅ **Release to GitHub:**
   ```bash
   git push origin master
   git push origin v3.6.0
   ```

3. ✅ **Announce:**
   - Update VeriPG documentation
   - Notify stakeholders
   - Celebrate! 🎉

### If Issues Found (<233/243)

1. **Document Issues:**
   - List keywords that failed
   - Provide error messages
   - Include test cases

2. **Debug:**
   - Check if syntax is correct
   - Verify grammar rules
   - Test with minimal examples

3. **Fix or Document:**
   - Fix if straightforward
   - Document as known limitation if complex

---

## 📚 Reference Documentation

1. **Implementation Reports:**
   - `M6_M7_SUCCESS_REPORT.md` - Drive strengths & SVA temporal
   - `M9_SUCCESS_REPORT.md` - Medium priority keywords
   - `M10_MATCHES_KNOWN_LIMITATIONS.md` - matches limitations

2. **Integration Testing:**
   - `INTEGRATION_TEST_REPORT.md` - All tests passing
   - `TEST_COMPLETION_REPORT.md` - Comprehensive test status

3. **Release Documentation:**
   - `FINAL_RELEASE_SUMMARY_V3.6.0.md` - Complete release notes

4. **Gap Analysis:**
   - `PHASE1_INVESTIGATION_RESULTS.md` - Initial findings
   - `VERIPG_ACCURATE_GAP_ANALYSIS.md` - Corrected gaps

---

## 🎯 Expected Outcome

**Verible v3.6.0 should enable VeriPG to:**
- ✅ Parse 95.9%+ of SystemVerilog keywords (233-240/243)
- ✅ Support all high-priority RTL constructs (drive strengths, SVA)
- ✅ Handle advanced verification features (config, randsequence)
- ✅ Provide comprehensive CST for accurate code analysis
- ✅ Match or exceed commercial parser capabilities for keyword coverage

**This represents:**
- 📈 +5.8%-8.7% improvement over v3.5.0
- 🎯 Near-complete SystemVerilog LRM coverage
- 🏆 World-class open-source SystemVerilog parser

---

**Status:** ✅ **READY FOR VERIPG VERIFICATION**

**Contact:** See documentation files for implementation details and troubleshooting.

