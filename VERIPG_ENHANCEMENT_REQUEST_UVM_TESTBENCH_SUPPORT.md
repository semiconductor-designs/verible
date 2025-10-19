# VeriPG Enhancement Request: UVM Testbench Analysis Support

**Request Date:** October 18, 2025  
**Requestor:** OpenTitan-to-RPG Project  
**Priority:** MEDIUM (High value, but not blocking current work)  
**Scope:** Architecture + Upstream Verible Enhancement  
**Impact:** Unlocks complete codebase analysis (design + verification)

---

## 🎯 Executive Summary

**Request:** Enable VeriPG to analyze UVM (Universal Verification Methodology) testbenches in addition to design RTL, achieving **100% SystemVerilog codebase coverage**.

**Current State:**
- ✅ Design RTL: **97.6% success rate** (3,570 of 3,659 files in OpenTitan)
- ❌ UVM Testbenches: **0% success rate** (89 files, 2.4% of codebase)

**Proposed Solution:** Two-track approach:
1. **Track A (VeriPG-level):** Add UVM preprocessing and alternative parser support
2. **Track B (Upstream):** Request Verible enhancements to natively support UVM

**Expected Outcome:** 
- **Short-term (3-6 months):** VeriPG workarounds achieve 100% coverage
- **Long-term (12-24 months):** Verible native support simplifies architecture

---

## 📊 Problem Statement

### Real-World Evidence: OpenTitan Case Study

**Project:** OpenTitan-to-RPG - Repository Planning Graph for OpenTitan SoC  
**Scale:** 3,659 SystemVerilog files across ~100 IP cores  
**Tool:** VeriPG v4.6.0 with Verible v5.0.1

**Extraction Results:**

| Category | Files | Status | Success Rate |
|----------|-------|--------|--------------|
| **Design RTL** | 3,570 | ✅ Parsed | 100% |
| **UVM Testbenches** | 89 | ❌ Failed | 0% |
| **Total** | 3,659 | ⚠️ Partial | **97.6%** |

**Failed File Breakdown:**

| File Type | Count | % of Failures | Examples |
|-----------|-------|---------------|----------|
| UVM Virtual Sequences (`*_vseq.sv`) | 45 | 51% | `hmac_stress_all_vseq.sv` |
| UVM Environment Config (`*_env_cfg.sv`) | 10 | 11% | `cip_base_env_cfg.sv` |
| UVM Sequence Items | 8 | 9% | `alert_esc_seq_item.sv` |
| UVM Scoreboards | 5 | 6% | `aon_timer_scoreboard.sv` |
| Testbench Programs | 10 | 11% | `prog_passthrough_sw.sv` |
| Auto-generated TB | 11 | 12% | `tb__xbar_connect.sv` |

**Full Analysis:** See attached `VERIPG_V4.6.0_PARSING_ERRORS_ANALYSIS.md`

### Why This Matters

#### Use Case 1: **Complete Repository Analysis**
- Users want **full codebase insight**: design + verification
- Testbench files contain valuable metadata:
  - Test coverage scope
  - Verification methodology
  - Design-under-test relationships
  - Constrained-random test parameters

#### Use Case 2: **Design-Verification Traceability**
- Map **which tests exercise which modules**
- Identify **untested code paths**
- Generate **verification coverage reports**
- Support **ISO 26262 / DO-254 compliance** (safety-critical designs)

#### Use Case 3: **Industry Standard Support**
- **UVM is the industry standard** for complex SoC verification
- **RISC-V ecosystem** (OpenTitan, Ibex, CVA6) uses UVM extensively
- **Commercial designs** routinely have 50-70% verification code
- **Academic research** on testbench quality needs UVM parsing

---

## 🔬 Technical Analysis: Why Verible Fails on UVM

### Root Cause Categories

#### 1. **UVM Macro Expansion Complexity** 🔴 CRITICAL

**Problem:** UVM uses preprocessor macros that expand to hundreds of lines of template code.

**Example:**
```systemverilog
class alert_esc_seq_item extends uvm_sequence_item;
  rand bit s_alert_send;
  rand int unsigned ping_delay;
  
  `uvm_object_utils_begin(alert_esc_seq_item)
    `uvm_field_int(s_alert_send, UVM_DEFAULT)
    `uvm_field_int(ping_delay, UVM_DEFAULT)
  `uvm_object_utils_end
  
  extern constraint delay_c;
endclass
```

**What `uvm_object_utils_begin` expands to** (~50 lines):
```systemverilog
// Factory registration
typedef uvm_object_registry#(alert_esc_seq_item, "alert_esc_seq_item") type_id;
static function type_id get_type();
  return type_id::get();
endfunction

// Virtual functions for create/clone
virtual function uvm_object create(string name="");
  alert_esc_seq_item tmp = new();
  return tmp;
endfunction

// Field automation (copy, compare, pack, unpack, print, record)
virtual function void do_copy(uvm_object rhs);
  alert_esc_seq_item _rhs;
  if(!$cast(_rhs, rhs)) return;
  super.do_copy(rhs);
  s_alert_send = _rhs.s_alert_send;
  ping_delay = _rhs.ping_delay;
endfunction

// ... 40+ more lines for compare, pack, unpack, etc.
```

**Why Verible Fails:**
- ❌ Macro takes **parameterized class name** as argument
- ❌ Nested macro calls (`uvm_field_*` inside `uvm_object_utils_*`)
- ❌ Token pasting and stringification (``)
- ❌ Metaprogramming patterns beyond simple text substitution

**Impact:** Blocks **all UVM classes** (~90% of failed files)

---

#### 2. **Extern Constraint Declarations** 🟠 HIGH

**Problem:** Constraints can be declared inside class but defined outside (like extern functions).

**Example:**
```systemverilog
class alert_esc_seq_item extends uvm_sequence_item;
  rand int unsigned ping_delay;
  rand int unsigned ack_delay;
  
  extern constraint delay_c;  // Declaration
  extern constraint alert_esc_mode_c;
endclass

// Definition outside class body
constraint alert_esc_seq_item::delay_c {
  soft ping_delay dist {0 :/ 5, [1:10] :/ 5};
  soft ack_delay  dist {0 :/ 5, [1:10] :/ 5};
}

constraint alert_esc_seq_item::alert_esc_mode_c {
  r_esc_rsp == 1 -> (!s_alert_send && !r_alert_rsp);
}
```

**Why Verible Fails:**
- ❌ Scope resolution operator (`::`) in constraint definition
- ❌ `dist` operator with weight syntax (`:/ 5`)
- ❌ `soft` constraint modifier
- ❌ Implication operator (`->`) in constraints

**Impact:** Blocks **all UVM sequences** (~50% of failed files)

---

#### 3. **Parameterized Virtual Class Hierarchies** 🟠 HIGH

**Problem:** UVM base classes use type parameters (similar to C++ templates) with complex inheritance.

**Example:**
```systemverilog
class cip_base_vseq #(
  type RAL_T               = dv_base_reg_block,
  type CFG_T               = cip_base_env_cfg,
  type COV_T               = cip_base_env_cov,
  type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer
) extends dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T);

  `uvm_object_param_utils_begin(cip_base_vseq#(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T))
    `uvm_field_string(common_seq_type, UVM_DEFAULT)
  `uvm_object_utils_end
  
  // ...
endclass
```

**Why Verible Fails:**
- ❌ **Type parameters** (not just value parameters)
- ❌ **Default type assignments** (`type RAL_T = dv_base_reg_block`)
- ❌ **Passing type params to base class** (`extends dv_base_vseq #(...)`)
- ❌ **Type params in macros** (`uvm_object_param_utils_begin`)

**Impact:** Blocks **all parameterized UVM base classes** (~30% of failed files)

---

#### 4. **Complex Macro-in-Macro Patterns** 🟡 MEDIUM

**Problem:** UVM uses macros that take code blocks as arguments and contain control flow.

**Example from OpenTitan:**
```systemverilog
`define loop_ral_models_to_create_threads(body) \
  fork \
    begin : isolation_fork \
      foreach (cfg.ral_models[i]) begin \
        automatic string ral_name = i; \
        fork \
          begin \
            body \  // ← Code block passed as macro argument!
          end \
        join_none \
      end \
      wait fork; \
    end : isolation_fork \
  join

// Usage:
`loop_ral_models_to_create_threads(
  `uvm_info(`gfn, $sformatf("Processing %s", ral_name), UVM_LOW)
)
```

**Why Verible Fails:**
- ❌ **Code block as macro argument** (not just identifiers)
- ❌ **Nesting:** `fork`/`join` inside `foreach` inside `fork`/`join_none`
- ❌ **Automatic variables** in macro context
- ❌ **Macro call inside macro argument** (nested macros)

**Impact:** Blocks **advanced UVM testbenches** (~10% of failed files)

---

#### 5. **Distribution Constraints & Soft Constraints** 🟡 MEDIUM

**Problem:** Randomization features require constraint solver understanding.

**Example:**
```systemverilog
constraint delay_c {
  soft ping_delay dist {
    0       := 50,    // 50% weight
    [1:10]  := 40,    // 40% weight across range
    [11:20] := 10     // 10% weight across range
  };
  
  ack_stable inside {[1:5]};
  
  // Implication
  enable_feature -> (delay > 10);
  
  // Soft (can be overridden)
  soft timeout == 100;
}
```

**Why Verible Fails:**
- ❌ `dist` operator with weight syntax (`:=` vs `:/`)
- ❌ `inside` operator with ranges
- ❌ `soft` modifier (override semantics)
- ❌ `->` implication operator
- ❌ `solve ... before` ordering constraints

**Impact:** Blocks **all constrained-random UVM sequences** (~40% of failed files)

---

## 💡 Proposed Solution: Two-Track Approach

### **Track A: VeriPG-Level Workarounds** (Short-term: 3-6 months)

#### Solution A1: **UVM Macro Preprocessor** ⭐ RECOMMENDED

**Concept:** Expand UVM macros to standard SystemVerilog before Verible parsing.

**Architecture:**
```python
# New module: src/parser/uvm_preprocessor.py

class UVMMacroExpander:
    """Expand UVM macros to standard SystemVerilog."""
    
    def __init__(self):
        self.uvm_library_path = self._find_uvm_library()
        self.macro_definitions = self._load_uvm_macros()
    
    def is_uvm_file(self, filepath: Path) -> bool:
        """Detect UVM files by patterns."""
        indicators = [
            '_vseq.sv', '_seq.sv', '_item.sv',
            'dv/env/', 'seq_lib/',
            'extends uvm_', '`uvm_'
        ]
        content = filepath.read_text()
        return any(ind in str(filepath) or ind in content 
                   for ind in indicators)
    
    def expand(self, sv_content: str) -> str:
        """Expand UVM macros to standard SV."""
        # Step 1: Expand simple registration macros
        sv_content = self._expand_uvm_object_utils(sv_content)
        sv_content = self._expand_uvm_component_utils(sv_content)
        
        # Step 2: Expand field automation macros
        sv_content = self._expand_uvm_field_macros(sv_content)
        
        # Step 3: Expand sequence macros
        sv_content = self._expand_uvm_do_macros(sv_content)
        
        return sv_content
    
    def _expand_uvm_object_utils(self, content: str) -> str:
        """
        Expand: `uvm_object_utils(MyClass)
        To:     typedef uvm_object_registry#(MyClass) type_id;
                static function type_id get_type(); ...
        """
        # Use UVM's own macro definitions as reference
        # Or implement minimal compatible expansion
        pass

# Integration in batch_processor.py:

class BatchProcessor:
    def __init__(self, ...):
        self.uvm_preprocessor = UVMMacroExpander()
    
    def process_files(self, file_paths, ...):
        for file_path in file_paths:
            if self.uvm_preprocessor.is_uvm_file(file_path):
                # Preprocess UVM files
                original_content = file_path.read_text()
                expanded_content = self.uvm_preprocessor.expand(original_content)
                
                # Parse expanded version
                ast = self.parser.parse(expanded_content)
            else:
                # Standard flow for design RTL
                ast = self.parser.parse(file_path)
```

**Benefits:**
- ✅ **No waiting for Verible** - works immediately
- ✅ **Reuses UVM's own definitions** - accurate expansion
- ✅ **Transparent to rest of VeriPG** - just better input to Verible
- ✅ **Backward compatible** - doesn't affect non-UVM files

**Challenges:**
- ⚠️ Requires UVM library as dependency (or bundled subset)
- ⚠️ Macro expansion is complex (but well-defined by UVM spec)
- ⚠️ Maintenance as UVM evolves (but UVM is stable)

**Estimated Effort:** 2-4 weeks for core functionality

---

#### Solution A2: **Hybrid Parser Architecture** (Alternative)

**Concept:** Use different parsers for different file types.

**Architecture:**
```python
class HybridParser:
    """Route files to best parser based on content."""
    
    def __init__(self):
        self.verible_parser = VeribleParser()  # For design RTL
        self.verilator_parser = VerilatorParser()  # For UVM (better support)
        
    def parse(self, file_path: Path):
        if self._is_design_rtl(file_path):
            return self.verible_parser.parse(file_path)
        elif self._is_uvm_testbench(file_path):
            return self.verilator_parser.parse(file_path)
        else:
            # Try Verible first, fallback to Verilator
            try:
                return self.verible_parser.parse(file_path)
            except ParseError:
                return self.verilator_parser.parse(file_path)
    
    def _is_design_rtl(self, file_path: Path) -> bool:
        """Detect design files: rtl/, hw/ip/*/rtl/, *.sv but not *_tb.sv"""
        path_str = str(file_path)
        return (
            '/rtl/' in path_str or 
            '/prim/' in path_str or
            '/top_' in path_str
        ) and 'dv' not in path_str
    
    def _is_uvm_testbench(self, file_path: Path) -> bool:
        """Detect UVM files."""
        return any(pattern in str(file_path) for pattern in [
            '_vseq.sv', '_seq.sv', 'seq_lib/',
            '_env.sv', 'dv/env/',
            '_agent.sv', '_monitor.sv', '_driver.sv',
            '_scoreboard.sv', '_cov.sv'
        ])
```

**Benefits:**
- ✅ **Best-of-both-worlds** - leverage each parser's strengths
- ✅ **Verilator has better UVM support** than Verible
- ✅ **Future-proof** - can add more parsers as needed

**Challenges:**
- ⚠️ **Architectural complexity** - unified output format needed
- ⚠️ **Verilator dependency** - larger installation footprint
- ⚠️ **Parser feature gaps** - need to reconcile differences

**Estimated Effort:** 4-6 weeks for architecture + integration

---

#### Solution A3: **Minimal UVM Support** (Quick Win)

**Concept:** Parse just class declarations, skip macro/constraint details.

**Architecture:**
```python
class MinimalUVMParser:
    """Extract minimal useful info from UVM files."""
    
    def parse_uvm_class(self, file_path: Path):
        """
        Extract:
        - Class name
        - Base class (parent)
        - File location
        
        Ignore:
        - Macros (just note they exist)
        - Constraints (mark as unparsed)
        - Internal details
        """
        content = file_path.read_text()
        
        # Regex-based extraction (simple but fragile)
        class_match = re.search(
            r'class\s+(\w+)\s+extends\s+([\w#(),\s]+);',
            content
        )
        
        if class_match:
            return {
                'type': 'class',
                'name': class_match.group(1),
                'base_class': class_match.group(2).strip(),
                'file': str(file_path),
                'category': 'uvm_testbench',
                'details': 'minimal_parse'  # Flag for users
            }
```

**Benefits:**
- ✅ **Very quick to implement** - 1 week
- ✅ **Provides testbench hierarchy** - "which tests exist"
- ✅ **Low risk** - simple regex, easy to maintain

**Challenges:**
- ⚠️ **Limited value** - misses detailed relationships
- ⚠️ **Fragile** - regex can break on complex syntax
- ⚠️ **Incomplete** - users may want more later

**Estimated Effort:** 1 week

---

### **Track B: Upstream Verible Enhancement** (Long-term: 12-24 months)

#### What to Request from Verible

**Enhancement Request Package:**

1. **UVM Macro Support**
   - Add preprocessor rules for common UVM patterns
   - Recognize `uvm_*_utils*` macros
   - Handle nested macro expansion
   - Support token pasting in macro arguments

2. **Enhanced Constraint Parser**
   - Parse `extern constraint` declarations
   - Support constraint scope resolution (`Class::constraint_name`)
   - Add `dist` operator support (distribution constraints)
   - Handle `soft` constraint modifier
   - Parse implication operator (`->`) in constraints
   - Support `solve...before` ordering

3. **Type Parameter Improvements**
   - Better parameterized class parsing
   - Support default type parameters (`type T = default_type`)
   - Type parameters in inheritance chains
   - Type parameters in macro arguments

4. **Distribution & Randomization**
   - `dist` operator: `variable dist { value := weight, ... }`
   - `inside` operator: `variable inside { [low:high], ... }`
   - Weight syntax: `:=` (single value) vs `:/` (range distribution)

**Reference Document for Verible Team:**

Attached to this request:
- `VERIBLE_ENHANCEMENT_REQUEST_UVM_SUPPORT.md` (draft for Verible)
- `VERIPG_V4.6.0_PARSING_ERRORS_ANALYSIS.md` (evidence)
- `UVM_MINIMAL_TEST_CASES.sv` (reproducible examples)

**Timeline Expectations:**
- **Submission:** Immediate (once VeriPG reviews this request)
- **Verible response:** 2-4 weeks
- **Implementation (if accepted):** 6-12 months
- **Release in stable version:** 12-18 months

---

## 📈 Expected Benefits

### Quantitative Impact

**For OpenTitan Project:**
| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| Files parsed | 3,570 | 3,659 | +89 files (+2.4%) |
| Success rate | 97.6% | 100% | +2.4 percentage points |
| Testbench visibility | 0% | 100% | ∞ |

**For Industry:**
- **RISC-V ecosystem**: OpenTitan, Ibex, CVA6, Ariane all use UVM
- **Commercial designs**: 50-70% verification code now visible
- **Research**: Testbench quality analysis now possible

### Qualitative Impact

**New Capabilities Unlocked:**

1. **Design-Test Traceability**
   - "Which tests exercise module X?"
   - "Is feature Y tested?"
   - "What's the verification coverage?"

2. **Verification Methodology Analysis**
   - UVM component reuse patterns
   - Test sequence complexity metrics
   - Randomization constraint analysis

3. **Compliance & Documentation**
   - ISO 26262 (automotive) traceability
   - DO-254 (aerospace) verification evidence
   - Automated test plan generation

4. **Research Applications**
   - Testbench quality studies
   - Verification pattern mining
   - ML-based test generation research

---

## 🎯 Recommendation & Prioritization

### **Recommended Implementation Path**

#### Phase 1: Quick Win (1-2 months)
- ✅ **Implement Solution A3** (Minimal UVM Support)
- ✅ Extract testbench class hierarchy
- ✅ Document 100% file coverage achievement
- ✅ Provide immediate value to users

#### Phase 2: Full Solution (3-6 months)
- ✅ **Implement Solution A1** (UVM Macro Preprocessor)
- ✅ Full UVM parsing capability
- ✅ Complete design-verification graph

#### Phase 3: Upstream (12-24 months)
- ✅ **Submit Track B** (Verible Enhancement Request)
- ✅ Engage with Verible maintainers
- ✅ Contribute test cases and validation
- ⏳ Wait for Verible implementation
- ✅ Integrate native Verible UVM support when available
- ✅ Deprecate preprocessor workaround (optional)

### Priority Justification

**Why MEDIUM priority (not LOW)?**
- ✅ **2.4% of code** is non-trivial in large projects
- ✅ **Industry standard** verification methodology
- ✅ **Differentiator** - most RTL tools ignore testbenches
- ✅ **Complete solution** - design + verification = full picture

**Why not HIGH priority?**
- ⚠️ **Design RTL works** - core functionality not blocked
- ⚠️ **Workarounds exist** - manual testbench analysis possible
- ⚠️ **Specialized use case** - not all users need testbench graphs

---

## 📦 Deliverables (What We Provide)

To support VeriPG implementation, we provide:

### 1. **Evidence & Analysis**
- ✅ `VERIPG_V4.6.0_PARSING_ERRORS_ANALYSIS.md` - Full 89-file analysis
- ✅ `parsing_errors_v4.6.0.txt` - Complete file list
- ✅ Categorization: By type, location, failure pattern

### 2. **Test Cases**
We'll create minimal reproducible examples:
- `test_uvm_object_utils.sv` - Macro expansion
- `test_extern_constraint.sv` - Constraint parsing
- `test_parameterized_base.sv` - Type parameters
- `test_distribution_constraint.sv` - Randomization

### 3. **Upstream Request Draft**
- ✅ `VERIBLE_ENHANCEMENT_REQUEST_UVM_SUPPORT.md` - Ready for Verible submission
- Includes technical details, test cases, justification
- VeriPG can submit directly or adapt as needed

### 4. **Reference Implementation** (Optional)
If VeriPG wants, we can contribute:
- Prototype UVM preprocessor (Solution A1)
- Example integration in batch_processor.py
- Unit tests for UVM file detection

---

## 🤝 Collaboration Model

### What We Ask from VeriPG

1. **Review this request** - Validate approach and priorities
2. **Choose solution** - A1, A2, A3, or hybrid?
3. **Provide guidance** - Architecture, coding standards, testing
4. **Review PRs** - If we contribute code
5. **Submit to Verible** - Either our draft or your version

### What We Offer

1. **Real-world validation** - Test on OpenTitan (3,659 files)
2. **Documentation** - User guides, examples, tutorials
3. **Bug reports** - Detailed issues with reproducible cases
4. **Code contributions** - If helpful and aligned with your vision
5. **Evangelism** - Promote VeriPG's UVM support to community

---

## 📚 References

### Standards & Specifications
- **IEEE 1800-2017:** SystemVerilog Language Standard
- **UVM 1.2 User Guide:** Accellera (2020)
- **UVM Reference Manual:** Accellera

### Tools & Projects
- **Verible:** https://github.com/chipsalliance/verible
- **VeriPG:** https://github.com/semiconductor-designs/VeriPG
- **OpenTitan:** https://github.com/lowRISC/opentitan
- **Verilator:** https://www.veripool.org/verilator/

### Related Enhancement Requests
- VeriPG has successfully requested and received:
  - Expression metadata enrichment
  - Ternary operator support
  - Generate block enhancements
  - Parameter override extraction

This request follows the same collaborative model.

---

## 📞 Contact & Next Steps

**Requestor:** OpenTitan-to-RPG Project  
**Contact:** [Available via GitHub for questions]

**Proposed Next Steps:**

1. **Week 1:** VeriPG reviews this request
2. **Week 2:** VeriPG chooses solution approach (A1/A2/A3)
3. **Week 3:** VeriPG creates Verible enhancement request (Track B)
4. **Week 4-8:** Implementation planning & architecture design
5. **Month 3-6:** Solution implementation & testing
6. **Month 12-24:** Verible native support (if accepted)

**We're committed to:**
- ✅ Testing any solution VeriPG implements
- ✅ Providing detailed feedback and bug reports
- ✅ Contributing code if helpful
- ✅ Documenting and promoting the solution

---

## 🎯 Success Criteria

**Minimum Success (Phase 1):**
- ✅ VeriPG can extract UVM class hierarchy
- ✅ Testbench files have 100% basic parsing
- ✅ Users can identify "which tests exist"

**Full Success (Phase 2):**
- ✅ VeriPG extracts complete UVM semantics
- ✅ Design-verification traceability established
- ✅ Constraint and randomization analysis available

**Ultimate Success (Phase 3):**
- ✅ Verible natively supports UVM constructs
- ✅ VeriPG simplifies to use native Verible features
- ✅ Industry-wide benefit to SystemVerilog tooling

---

## 🙏 Acknowledgments

Thank you to:
- **VeriPG Team** for creating an excellent, extensible architecture
- **Verible Team** for open-source SystemVerilog parsing
- **OpenTitan Project** for providing real-world test corpus
- **UVM/Accellera** for verification methodology standardization

---

**Bottom Line:** This request unlocks complete codebase analysis for complex SoC projects. The two-track approach provides both immediate solutions (VeriPG-level workarounds) and long-term excellence (upstream Verible enhancement). We're ready to collaborate on whichever path VeriPG chooses!

---

**Appendices:**
- A. Full error analysis (`VERIPG_V4.6.0_PARSING_ERRORS_ANALYSIS.md`)
- B. Test cases (to be created)
- C. Verible request draft (see next document)
- D. OpenTitan statistics and validation data

**Version:** 1.0  
**Date:** October 18, 2025  
**Status:** Ready for VeriPG review

