# UVM Enhancement Request Package - README

**Created:** October 18, 2025  
**Purpose:** Comprehensive documentation for requesting UVM testbench support  
**Target Audiences:** VeriPG maintainers, Verible maintainers, community

---

## 📦 What's in This Package

This package contains everything needed to request and implement UVM testbench parsing support:

### **Document 1: For VeriPG** ⭐ **PRIMARY**

**File:** `VERIPG_ENHANCEMENT_REQUEST_UVM_TESTBENCH_SUPPORT.md`

**Audience:** VeriPG project maintainers  
**Purpose:** Comprehensive enhancement request with implementation options  
**Length:** ~50 pages  

**Contents:**
- Executive summary with real-world data
- Complete technical analysis (5 failure modes)
- **Two-track solution approach:**
  - Track A: VeriPG-level workarounds (3 options)
  - Track B: Upstream Verible enhancement
- Implementation roadmap (Phase 1-3)
- Test cases and validation data
- Collaboration model

**Key Message:** "Here's what we need, here are 3 ways you could solve it, and here's the Verible enhancement that would help long-term."

---

### **Document 2: For Verible** (via VeriPG)

**File:** `VERIBLE_ENHANCEMENT_REQUEST_UVM_SUPPORT.md`

**Audience:** Verible project maintainers (chipsalliance/verible)  
**Purpose:** Technical enhancement request for UVM construct parsing  
**Length:** ~25 pages  

**Contents:**
- Executive summary with quantitative data
- 5 specific technical issues with examples
- Minimal reproducible test cases
- 3 implementation options (Full/Phased/Minimal)
- Expected impact and benefits
- Collaboration offer

**Key Message:** "UVM files fail to parse. Here are the exact technical issues, test cases, and solution options. We'll help validate."

---

### **Document 3: Analysis & Evidence**

**File:** `VERIPG_V4.6.0_PARSING_ERRORS_ANALYSIS.md`

**Audience:** Technical readers, documentation  
**Purpose:** Detailed analysis of 89 parsing failures  
**Length:** ~30 pages  

**Contents:**
- Error distribution by category (seq_lib, dv/env, etc.)
- Common patterns in failed files
- Impact assessment (why it matters)
- Root cause analysis (Verible limitations)
- Recommendations (3 tiers)
- Complete list of 89 failed files

**Key Message:** "Here's exactly what's failing, why, and what it means."

---

### **Document 4: Supporting Data**

**File:** `data/veripg_raw/parsing_errors_v4.6.0.txt`

**Audience:** Developers, validators  
**Purpose:** Raw list of failed file paths  
**Format:** Plain text, one path per line  

**Contents:**
- All 89 failed file paths
- Sortable/filterable list
- For easy reference and automation

---

## 🎯 How to Use This Package

### **Scenario 1: You Want VeriPG to Implement UVM Support**

**Action:** Share Document 1 with VeriPG

**Steps:**
1. Create GitHub issue at: https://github.com/semiconductor-designs/VeriPG/issues
2. Title: "Enhancement Request: UVM Testbench Analysis Support"
3. Paste or attach: `VERIPG_ENHANCEMENT_REQUEST_UVM_TESTBENCH_SUPPORT.md`
4. Reference: `VERIPG_V4.6.0_PARSING_ERRORS_ANALYSIS.md` as supporting evidence
5. Tag as: `enhancement`, `verification`, `uvm`

**What Happens Next:**
- VeriPG reviews request (~1-2 weeks)
- VeriPG chooses solution approach (A1, A2, or A3)
- VeriPG may submit Document 2 to Verible
- VeriPG implements chosen solution (~3-6 months)

---

### **Scenario 2: You Want to Submit Directly to Verible**

**Action:** Share Document 2 with Verible

**Steps:**
1. Create GitHub issue at: https://github.com/chipsalliance/verible/issues
2. Title: "Enhancement Request: UVM Construct Support (Macros, Constraints, Type Params)"
3. Paste or attach: `VERIBLE_ENHANCEMENT_REQUEST_UVM_SUPPORT.md`
4. Reference: OpenTitan project as real-world validation
5. Tag as: `enhancement`, `parser`, `systemverilog`

**What Happens Next:**
- Verible team reviews (~2-4 weeks)
- Feasibility assessment
- If accepted: Implementation (~6-12 months)
- If rejected: You have evidence for workarounds

---

### **Scenario 3: You Want Both (Recommended)** ⭐

**Action:** Two-pronged approach

**Steps:**
1. **Submit to VeriPG** (Document 1)
   - Get short-term solution (workarounds)
   - Let VeriPG coordinate with Verible
   
2. **Monitor Verible** (VeriPG will likely submit Document 2)
   - Watch for upstream enhancements
   - Validate when available
   - Eventually get native support

**Benefits:**
- ✅ Short-term: VeriPG workaround (3-6 months)
- ✅ Long-term: Verible native support (12-24 months)
- ✅ Not blocked waiting for upstream

---

## 📋 Quick Reference Guide

### Key Numbers to Cite

| Metric | Value | Context |
|--------|-------|---------|
| **Total files** | 3,659 | OpenTitan SystemVerilog codebase |
| **Design RTL success** | 3,570 (100%) | All critical files parse |
| **UVM failures** | 89 (2.4%) | Testbench files only |
| **Success rate** | 97.6% | Excellent for design-focused work |

### Key Technical Issues (Summary)

1. **UVM macros** → Blocks 90% of UVM files
2. **Extern constraints** → Blocks 50% of UVM files  
3. **Type parameters** → Blocks 30% of UVM files
4. **Distribution constraints** → Blocks 40% of sequences
5. **Macro-in-macro** → Blocks 10% of advanced tests

### Key Selling Points

**For VeriPG:**
- "Complete your coverage: Design ✅ + Verification = 100%"
- "Industry standard: UVM is IEEE 1800.2-2017"
- "Differentiation: Most tools ignore testbenches"

**For Verible:**
- "Serve the full SV ecosystem: Design + Verification"
- "Real-world evidence: OpenTitan (Google's chip)"
- "We'll help: Test cases, validation, documentation"

---

## 🗣️ Talking Points

### For Email/Issue Description

**Subject:** "Enhancement Request: Enable Complete Codebase Analysis (UVM Testbench Support)"

**Opening:**
> We've successfully used [VeriPG/Verible] to analyze OpenTitan's RTL design code (3,570 files, 100% success rate). However, UVM testbench files (89 files, 2.4% of codebase) currently fail to parse.
> 
> We've created a comprehensive analysis of the issue, including root causes, test cases, and solution options. This enhancement would enable complete codebase analysis (design + verification) and benefit the entire SystemVerilog tool ecosystem.

**Body:** [Paste relevant document]

**Closing:**
> We're committed to helping validate any solution through testing on real-world codebases. We can provide additional test cases, bug reports, and documentation as needed.

---

### For GitHub Issue

**Labels to Use:**

**VeriPG:**
- `enhancement`
- `verification`
- `uvm`
- `testbench`
- `priority: medium`

**Verible:**
- `enhancement`
- `parser`
- `systemverilog`
- `uvm`
- `verification`

---

## 🎯 Expected Outcomes

### Best Case (10% probability)

**Timeline:** 12-24 months

**Outcome:**
1. VeriPG implements preprocessor workaround (6 months)
2. Verible accepts enhancement request
3. Verible implements UVM support (12 months)
4. VeriPG migrates to native Verible support
5. **Result:** 100% coverage with clean architecture

---

### Likely Case (60% probability)

**Timeline:** 3-12 months

**Outcome:**
1. VeriPG implements workaround (6 months)
2. Verible acknowledges but doesn't prioritize
3. **Result:** 100% coverage via VeriPG workaround
4. **Status:** Production-ready, may simplify if Verible adds support later

---

### Conservative Case (30% probability)

**Timeline:** 3-6 months

**Outcome:**
1. VeriPG implements minimal solution (3 months)
2. Verible declines enhancement (out of scope)
3. **Result:** Partial UVM support (class hierarchy only)
4. **Status:** Better than current 0%, document limitation

---

## ✅ Action Checklist

Before submitting:
- [ ] Review Documents 1 & 2 for any project-specific updates
- [ ] Verify all file paths are correct
- [ ] Confirm statistics are current (3,659 files, 89 failures)
- [ ] Prepare to provide additional info if requested

When submitting:
- [ ] Create GitHub issue (VeriPG and/or Verible)
- [ ] Attach or link to documents
- [ ] Use recommended labels
- [ ] Set watch/notifications for responses

After submitting:
- [ ] Monitor for questions/feedback (respond within 48 hours)
- [ ] Provide additional test cases if requested
- [ ] Test any experimental implementations
- [ ] Update community on progress

---

## 📞 Support & Questions

### If VeriPG/Verible Ask for More Info

**Have ready:**
- OpenTitan repository link
- VeriPG version used (v4.6.0)
- Verible version used (v5.0.1)
- Extraction logs (available)
- Willing to create minimal test cases on demand

### If They Decline

**Fallback options:**
1. Document limitation in your project
2. Use current 97.6% (sufficient for design-focused work)
3. Manual testbench analysis for critical verification
4. Monitor for future tool updates

---

## 🎓 Key Insights

### Why This Is Well-Positioned to Succeed

1. **Real-world evidence:** Not theoretical, actual 3,659-file project
2. **Quantified impact:** Exact numbers (89 files, 2.4%)
3. **Solution options:** Not demanding one approach, offering choices
4. **Collaboration:** Offering to help, not just requesting
5. **Precedent:** VeriPG has successfully requested features before

### Why This Might Not Happen

1. **UVM complexity:** Legitimate technical challenges
2. **Resource constraints:** Open source teams are busy
3. **Scope creep:** Verification vs. synthesis/design focus
4. **Alternative parsers:** Verilator, commercial tools exist

### Bottom Line

**Worth submitting?** ✅ **Absolutely YES**

**Why:**
- Low effort (docs ready)
- High potential value (100% coverage)
- Community benefit (helps everyone)
- No downside (already have 97.6% working)

---

## 📚 Additional Resources

### Background Reading
- **IEEE 1800-2017:** SystemVerilog standard
- **IEEE 1800.2-2017:** UVM standard
- **Verible docs:** https://chipsalliance.github.io/verible/
- **VeriPG docs:** https://github.com/semiconductor-designs/VeriPG

### Community
- **Verible discussions:** GitHub Discussions
- **VeriPG issues:** GitHub Issues
- **SystemVerilog community:** reddit.com/r/FPGA, comp.lang.verilog

---

**Package Version:** 1.0  
**Last Updated:** October 18, 2025  
**Status:** Ready to submit

---

**Good luck! 🚀** This is a well-researched, well-documented request with real-world validation. Whether or not it gets implemented, you've done due diligence and created valuable documentation for the community.

