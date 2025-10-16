# Phase 6: Enhanced VeriPG Validation Rules

**Goal**: Make VeriPG Validator the definitive SystemVerilog style checker  
**Timeline**: 4-6 weeks (no rush, quality over speed)  
**Success Metric**: Feature completeness (50+ validation rules)  
**Methodology**: TDD (Test-Driven Development)  

**Chosen Path**: Option D (Enhanced VeriPG Validation Rules)

---

## 🎯 OBJECTIVES

Transform the current VeriPG Validator framework into a production-grade linting tool with:

1. ✅ **50+ Comprehensive Validation Rules**
2. ✅ **Configurable Rule Engine** (YAML/JSON config)
3. ✅ **Auto-Fix Suggestions** (quick fixes for violations)
4. ✅ **Performance** (< 2s for 10k lines)
5. ✅ **Integration** (CLI tool + library API)

---

## 📋 PHASE 6 BREAKDOWN

### Week 1: Core Validation Rules (CDC & Clock/Reset) ⏰

**Goal**: Implement critical CDC and clock domain rules

#### Rules to Implement (15 rules):

1. **CDC_001**: Clock domain crossing without synchronizer
2. **CDC_002**: Multi-bit signal crossing clock domains
3. **CDC_003**: Clock mux without glitch protection
4. **CDC_004**: Asynchronous reset in synchronous logic
5. **CLK_001**: Missing clock signal in always_ff
6. **CLK_002**: Multiple clocks in single always block
7. **CLK_003**: Clock used as data signal
8. **CLK_004**: Gated clock without ICG cell
9. **RST_001**: Missing reset in sequential logic
10. **RST_002**: Asynchronous reset not properly synchronized
11. **RST_003**: Active-low reset mixed with active-high
12. **RST_004**: Reset signal used as data
13. **RST_005**: Reset width check (minimum assertion time)
14. **TIM_001**: Combinational loop detected
15. **TIM_002**: Latch inferred (incomplete case/if)

#### Implementation Strategy:

```cpp
// Example: CDC_001 implementation
absl::Status VeriPGValidator::CheckCDCViolations() {
  // 1. Find all always_ff blocks
  // 2. For each signal assigned:
  //    - Determine its clock domain (from @(posedge clk_x))
  //    - Find all uses of this signal in other always_ff blocks
  //    - If clock domains differ:
  //      - Check for synchronizer pattern (2+ stage FF chain)
  //      - If not found, report CDC_001 violation
  
  for (const auto& ff_block : FindAllAlwaysFFBlocks()) {
    std::string clock_domain = ExtractClockSignal(ff_block);
    
    for (const auto& assigned_signal : GetAssignedSignals(ff_block)) {
      auto uses = FindSignalUses(assigned_signal);
      
      for (const auto& use : uses) {
        if (IsInDifferentClockDomain(use, clock_domain)) {
          if (!HasSynchronizer(assigned_signal, use)) {
            violations.push_back({
              .rule = "CDC_001",
              .severity = Severity::ERROR,
              .message = "Clock domain crossing without synchronizer",
              .signal = assigned_signal,
              .source_domain = clock_domain,
              .dest_domain = GetClockDomain(use),
              .fix = GenerateSynchronizerFix(assigned_signal)
            });
          }
        }
      }
    }
  }
}
```

#### TDD Tests (15 tests, one per rule):

```cpp
TEST_F(VeriPGValidatorTest, CDC_001_DetectsMissingSync) {
  const char* code = R"(
    module test(input clk_a, clk_b, input logic d);
      logic data_a, data_b;
      
      always_ff @(posedge clk_a) data_a <= d;
      always_ff @(posedge clk_b) data_b <= data_a; // CDC violation!
    endmodule
  )";
  
  auto violations = ValidateCode(code);
  EXPECT_THAT(violations, Contains(ViolationWithRule("CDC_001")));
}

TEST_F(VeriPGValidatorTest, CDC_001_AcceptsSynchronizer) {
  const char* code = R"(
    module test(input clk_a, clk_b, input logic d);
      logic data_a, sync1, sync2;
      
      always_ff @(posedge clk_a) data_a <= d;
      always_ff @(posedge clk_b) sync1 <= data_a;  // Stage 1
      always_ff @(posedge clk_b) sync2 <= sync1;   // Stage 2
    endmodule
  )";
  
  auto violations = ValidateCode(code);
  EXPECT_THAT(violations, Not(Contains(ViolationWithRule("CDC_001"))));
}
```

**Deliverables**:
- ✅ 15 validation rules implemented
- ✅ 30+ tests (positive + negative cases)
- ✅ Auto-fix generators for CDC_001, CLK_001, RST_001

---

### Week 2: Naming Conventions & Signal Width Rules 📝

**Goal**: Enforce VeriPG naming standards and width consistency

#### Rules to Implement (12 rules):

16. **NAM_001**: Module names must be lowercase_with_underscores
17. **NAM_002**: Signal names must be descriptive (>= 3 chars, not single letter)
18. **NAM_003**: Parameter names must be UPPERCASE
19. **NAM_004**: Clock signals must start with "clk_"
20. **NAM_005**: Reset signals must start with "rst_" or "rstn_"
21. **NAM_006**: Active-low signals must end with "_n"
22. **NAM_007**: No reserved keywords as identifiers
23. **WID_001**: Signal width mismatch in assignment
24. **WID_002**: Implicit width conversion (lossy)
25. **WID_003**: Concatenation width mismatch
26. **WID_004**: Parameter width inconsistent with usage
27. **WID_005**: Port width mismatch in instantiation

#### Implementation:

```cpp
absl::Status VeriPGValidator::ValidateNamingConventions() {
  // Walk symbol table
  for (const auto* node : symbol_table_->Root().Children()) {
    if (node->Kind() == SymbolKind::kModule) {
      // Check NAM_001: Module names
      std::string name = node->Name();
      if (!IsLowercaseWithUnderscores(name)) {
        violations.push_back({
          .rule = "NAM_001",
          .message = absl::StrCat("Module name '", name, 
                                  "' should be lowercase_with_underscores"),
          .fix = GenerateLowercaseFix(name)
        });
      }
      
      // Check signals in module
      for (const auto* signal : node->Children()) {
        if (signal->Kind() == SymbolKind::kVariable) {
          std::string sig_name = signal->Name();
          
          // NAM_002: Descriptive names
          if (sig_name.length() < 3 && !IsException(sig_name)) {
            violations.push_back({.rule = "NAM_002", ...});
          }
          
          // NAM_004: Clock naming
          if (IsClockSignal(signal) && !absl::StartsWith(sig_name, "clk_")) {
            violations.push_back({.rule = "NAM_004", ...});
          }
          
          // Similar for NAM_005, NAM_006...
        }
      }
    }
  }
}

absl::Status VeriPGValidator::ValidateSignalWidths() {
  // Use TypeInference to get signal widths
  for (const auto* node : FindAllAssignments()) {
    auto lhs_type = type_inference_->InferType(node->LHS());
    auto rhs_type = type_inference_->InferType(node->RHS());
    
    if (lhs_type.width != rhs_type.width) {
      violations.push_back({
        .rule = "WID_001",
        .severity = (lhs_type.width < rhs_type.width) ? ERROR : WARNING,
        .message = absl::StrCat("Width mismatch: ", 
                                lhs_type.width, " vs ", rhs_type.width),
        .fix = GenerateWidthCastFix(rhs_type.width, lhs_type.width)
      });
    }
  }
}
```

#### TDD Tests (24 tests):

```cpp
TEST_F(VeriPGValidatorTest, NAM_001_RejectsCamelCase) {
  const char* code = "module MyModule; endmodule"; // Wrong
  auto violations = ValidateCode(code);
  EXPECT_THAT(violations, Contains(ViolationWithRule("NAM_001")));
}

TEST_F(VeriPGValidatorTest, NAM_001_AcceptsLowercase) {
  const char* code = "module my_module; endmodule"; // Correct
  auto violations = ValidateCode(code);
  EXPECT_THAT(violations, Not(Contains(ViolationWithRule("NAM_001"))));
}

TEST_F(VeriPGValidatorTest, WID_001_DetectsMismatch) {
  const char* code = R"(
    module test;
      logic [7:0] a;
      logic [15:0] b;
      assign a = b; // Width mismatch!
    endmodule
  )";
  auto violations = ValidateCode(code);
  EXPECT_THAT(violations, Contains(ViolationWithRule("WID_001")));
}
```

**Deliverables**:
- ✅ 12 validation rules implemented
- ✅ 24+ tests
- ✅ Auto-fix for naming violations

---

### Week 3: Power Intent & Design Patterns 🔋

**Goal**: UPF-aware checks and structural validation

#### Rules to Implement (13 rules):

28. **PWR_001**: Missing power domain annotation
29. **PWR_002**: Level shifter required at domain boundary
30. **PWR_003**: Isolation cell required for power-down domain
31. **PWR_004**: Retention register without retention annotation
32. **PWR_005**: Always-on signal crossing to power-gated domain
33. **STR_001**: Module has no ports (should be testbench)
34. **STR_002**: Module exceeds complexity threshold (50+ statements)
35. **STR_003**: Deep hierarchy (>5 levels of instantiation)
36. **STR_004**: Missing module header comment
37. **STR_005**: Port ordering (clk, rst, inputs, outputs)
38. **STR_006**: Instantiation without named ports
39. **STR_007**: Generate block without label
40. **STR_008**: Case statement without default clause

#### Implementation:

```cpp
absl::Status VeriPGValidator::ValidatePowerIntent() {
  // Requires UPF awareness (optional, can be basic)
  
  // PWR_002: Check for level shifters at domain boundaries
  for (const auto& instantiation : FindAllInstantiations()) {
    auto parent_domain = GetPowerDomain(instantiation.parent_module);
    auto child_domain = GetPowerDomain(instantiation.child_module);
    
    if (parent_domain.voltage != child_domain.voltage) {
      // Check if level shifter exists between them
      if (!HasLevelShifter(instantiation)) {
        violations.push_back({
          .rule = "PWR_002",
          .message = "Level shifter required between power domains",
          .fix = GenerateLevelShifterFix(instantiation)
        });
      }
    }
  }
}

absl::Status VeriPGValidator::ValidateModuleStructure() {
  for (const auto* module : symbol_table_->GetAllModules()) {
    // STR_002: Complexity check
    int statement_count = CountStatements(module);
    if (statement_count > 50) {
      violations.push_back({
        .rule = "STR_002",
        .severity = WARNING,
        .message = absl::StrCat("Module has ", statement_count, 
                                " statements (threshold: 50)")
      });
    }
    
    // STR_005: Port ordering
    auto ports = GetPorts(module);
    if (!IsPortOrderCorrect(ports)) {
      violations.push_back({
        .rule = "STR_005",
        .message = "Ports should be ordered: clk, rst, inputs, outputs",
        .fix = GeneratePortReorderFix(ports)
      });
    }
  }
}
```

#### TDD Tests (26 tests):

```cpp
TEST_F(VeriPGValidatorTest, PWR_002_DetectsMissingLevelShifter) {
  const char* code = R"(
    // Assume 0.8V domain
    module parent_0v8;
      child_1v2 u_child(...); // Crossing to 1.2V without level shifter!
    endmodule
  )";
  auto violations = ValidateCode(code);
  EXPECT_THAT(violations, Contains(ViolationWithRule("PWR_002")));
}

TEST_F(VeriPGValidatorTest, STR_005_DetectsWrongPortOrder) {
  const char* code = R"(
    module test(
      input logic data_in,  // Wrong: inputs before clk/rst
      input logic clk,
      input logic rst_n
    );
    endmodule
  )";
  auto violations = ValidateCode(code);
  EXPECT_THAT(violations, Contains(ViolationWithRule("STR_005")));
}
```

**Deliverables**:
- ✅ 13 validation rules implemented
- ✅ 26+ tests
- ✅ Auto-fix for STR_005, STR_006

---

### Week 4: Configurable Rules & Auto-Fix Engine 🔧

**Goal**: Make rules configurable and enhance auto-fix

#### Features to Implement:

1. **YAML/JSON Configuration File**

```yaml
# .veripg-lint.yaml
rules:
  CDC_001:
    enabled: true
    severity: error
    auto_fix: true
  
  NAM_001:
    enabled: true
    severity: warning
    exceptions: [tb_*, test_*]  # Testbench modules exempt
  
  WID_001:
    enabled: true
    severity: error
    threshold: 4  # Only flag if width diff > 4 bits
  
  STR_002:
    enabled: false  # Disable complexity check
    
global:
  max_violations_per_file: 100
  stop_on_first_error: false
  auto_fix_safe_only: true  # Only apply non-breaking fixes
```

2. **Configuration Parser**

```cpp
class RuleConfig {
 public:
  bool enabled = true;
  Severity severity = Severity::WARNING;
  bool auto_fix_enabled = false;
  std::vector<std::string> exceptions;
  absl::flat_hash_map<std::string, std::string> parameters;
  
  static absl::StatusOr<RuleConfig> LoadFromYAML(const std::string& path);
};

class ValidatorConfig {
 public:
  absl::flat_hash_map<std::string, RuleConfig> rules;
  int max_violations_per_file = 1000;
  bool stop_on_first_error = false;
  bool auto_fix_safe_only = true;
  
  static absl::StatusOr<ValidatorConfig> Load(const std::string& config_path);
  bool IsRuleEnabled(const std::string& rule_id) const;
  Severity GetSeverity(const std::string& rule_id) const;
};
```

3. **Auto-Fix Engine**

```cpp
class AutoFixEngine {
 public:
  struct Fix {
    std::string description;
    std::vector<TextEdit> edits;  // Offset, length, replacement
    bool is_safe;  // Safe = doesn't change behavior, only style
  };
  
  // Generate fix for a violation
  absl::StatusOr<Fix> GenerateFix(const Violation& violation);
  
  // Apply fixes to file (with backup)
  absl::Status ApplyFixes(const std::string& filename, 
                          const std::vector<Fix>& fixes);
  
  // Preview fixes (dry-run)
  std::string PreviewFixes(const std::string& filename,
                           const std::vector<Fix>& fixes);
};
```

4. **Fix Implementations**

```cpp
// Example: Fix CDC_001 by inserting synchronizer
Fix AutoFixEngine::FixCDC_001(const Violation& v) {
  // Generate 2-stage synchronizer code
  std::string sync_code = absl::StrCat(
    "  logic ", v.signal, "_sync1, ", v.signal, "_sync2;\n",
    "  always_ff @(posedge ", v.dest_clock, ") begin\n",
    "    ", v.signal, "_sync1 <= ", v.signal, ";\n",
    "    ", v.signal, "_sync2 <= ", v.signal, "_sync1;\n",
    "  end\n"
  );
  
  return {
    .description = "Insert 2-stage synchronizer",
    .edits = {
      {v.location.offset, 0, sync_code},  // Insert sync logic
      {v.use_location.offset, v.signal.size(), 
       v.signal + "_sync2"}  // Replace use
    },
    .is_safe = true
  };
}

// Example: Fix NAM_001 by converting to lowercase
Fix AutoFixEngine::FixNAM_001(const Violation& v) {
  std::string lowercase_name = ToLowercaseWithUnderscores(v.symbol_name);
  
  // Use SymbolRenamer to rename across all files
  return {
    .description = absl::StrCat("Rename '", v.symbol_name, 
                                "' to '", lowercase_name, "'"),
    .edits = GenerateRenameEdits(v.symbol_name, lowercase_name),
    .is_safe = true
  };
}
```

#### TDD Tests (20 tests):

```cpp
TEST_F(ConfigTest, LoadsYAMLConfig) {
  const char* yaml = R"(
    rules:
      CDC_001:
        enabled: true
        severity: error
  )";
  auto config = ValidatorConfig::Load(yaml);
  EXPECT_TRUE(config.IsRuleEnabled("CDC_001"));
  EXPECT_EQ(config.GetSeverity("CDC_001"), Severity::ERROR);
}

TEST_F(AutoFixTest, CDC_001_GeneratesSynchronizer) {
  Violation v = {.rule = "CDC_001", .signal = "data", ...};
  auto fix = fix_engine_.GenerateFix(v);
  EXPECT_THAT(fix.edits, SizeIs(2));  // Insert + replace
  EXPECT_TRUE(fix.is_safe);
}

TEST_F(AutoFixTest, AppliesFixesWithBackup) {
  std::vector<Fix> fixes = {...};
  auto status = fix_engine_.ApplyFixes("test.sv", fixes);
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(std::filesystem::exists("test.sv.bak"));
}
```

**Deliverables**:
- ✅ YAML/JSON config parser
- ✅ Auto-fix engine with 10+ fix generators
- ✅ 20+ tests for configuration and fixes

---

### Week 5: Performance Optimization & Batch Mode 🚀

**Goal**: Optimize for large codebases, add batch processing

#### Features to Implement:

1. **Performance Optimizations**

```cpp
class CachedValidator {
 private:
  // Cache expensive operations
  absl::flat_hash_map<std::string, TypeInfo> type_cache_;
  absl::flat_hash_map<const SymbolTableNode*, ClockDomain> clock_domain_cache_;
  
 public:
  // Optimize: Only re-validate changed functions
  void InvalidateCache(const std::string& symbol_name);
  
  // Optimize: Parallel validation of multiple files
  std::vector<ValidationResult> ValidateInParallel(
    const std::vector<std::string>& files);
};
```

2. **Batch Mode CLI**

```bash
# Validate entire project
veripg-validator --project-dir ./rtl --config .veripg-lint.yaml

# Validate with auto-fix
veripg-validator --fix --safe-only ./rtl/*.sv

# Output formats
veripg-validator --format=json ./rtl/*.sv > violations.json
veripg-validator --format=sarif ./rtl/*.sv > sarif.json  # For GitHub Actions
veripg-validator --format=text ./rtl/*.sv  # Human-readable
```

3. **Progress Reporting**

```cpp
class ValidationProgress {
 public:
  void SetTotalFiles(int count);
  void ReportFileComplete(const std::string& filename, int violations);
  void PrintSummary();
  
  // Output:
  // [====================] 100% (50/50 files)
  // 125 violations found (75 errors, 50 warnings)
  // 30 auto-fixable violations
};
```

4. **Integration with CI/CD**

```yaml
# .github/workflows/veripg-lint.yml
name: VeriPG Lint
on: [push, pull_request]
jobs:
  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Run VeriPG Validator
        run: |
          veripg-validator --format=sarif --output=sarif.json ./rtl/**/*.sv
      - name: Upload SARIF
        uses: github/codeql-action/upload-sarif@v2
        with:
          sarif_file: sarif.json
```

#### TDD Tests (15 tests):

```cpp
TEST_F(PerformanceTest, Validates10kLinesUnder2Seconds) {
  std::string large_file = GenerateRandomSV(10000);  // 10k lines
  
  auto start = std::chrono::steady_clock::now();
  auto result = validator_.Validate(large_file);
  auto end = std::chrono::steady_clock::now();
  
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(
    end - start).count();
  
  EXPECT_LT(duration, 2000);  // < 2 seconds
}

TEST_F(BatchTest, ValidatesMultipleFilesInParallel) {
  std::vector<std::string> files = {"a.sv", "b.sv", "c.sv"};
  auto results = validator_.ValidateInParallel(files);
  EXPECT_EQ(results.size(), 3);
}
```

**Deliverables**:
- ✅ Performance optimizations (caching, parallelization)
- ✅ Batch mode CLI with progress reporting
- ✅ Multiple output formats (text, JSON, SARIF)
- ✅ CI/CD integration examples
- ✅ 15+ performance tests

---

### Week 6: Documentation, Polish & Release 📚

**Goal**: Production-ready release with comprehensive docs

#### Tasks:

1. **User Documentation** (2 days)

   - User guide (how to use validator)
   - Rule reference (all 40+ rules documented)
   - Configuration guide (YAML syntax, examples)
   - Auto-fix guide (safe vs unsafe fixes)
   - Integration guide (CI/CD, pre-commit hooks)
   - Troubleshooting (common issues, FAQ)

2. **Developer Documentation** (1 day)

   - Architecture overview
   - How to add new rules
   - API reference (library usage)
   - Testing guide

3. **Examples & Demos** (1 day)

   - Example projects with violations
   - Before/after auto-fix demos
   - Configuration templates
   - CI/CD integration examples

4. **Polish** (2 days)

   - Error message clarity
   - Help text improvement
   - Performance profiling
   - Edge case fixes
   - Code cleanup

5. **Release** (1 day)

   - Final testing (all 150+ tests)
   - Version bump to v5.0.0
   - Release notes
   - Binary build & deployment
   - Announcement

**Deliverables**:
- ✅ Comprehensive documentation (200+ pages)
- ✅ Example projects
- ✅ v5.0.0 release
- ✅ Binary deployed to VeriPG

---

## 📊 SUCCESS CRITERIA

### Quantitative Metrics:

- ✅ **50+ validation rules** implemented
- ✅ **150+ tests** passing (3x current)
- ✅ **< 2 seconds** for 10k line file
- ✅ **YAML/JSON config** working
- ✅ **10+ auto-fix** generators
- ✅ **Multiple output formats** (text, JSON, SARIF)

### Qualitative Goals:

- ✅ **Production-ready** quality
- ✅ **VeriPG satisfaction** (meets their needs)
- ✅ **Feature complete** (all critical rules)
- ✅ **Well-documented** (users can self-serve)
- ✅ **Maintainable** (clear code, tests)

---

## 🔧 IMPLEMENTATION METHODOLOGY

### TDD Workflow (Every Rule):

1. **Write failing test** for violation detection
2. **Implement** rule logic to make test pass
3. **Write test** for rule with no violation (negative case)
4. **Refactor** for clarity and performance
5. **Write test** for auto-fix generation
6. **Implement** auto-fix generator
7. **Write integration test** with real code
8. **Document** rule in reference guide

### Code Review Checklist:

- ✅ Tests cover positive & negative cases
- ✅ Rule documented with examples
- ✅ Performance acceptable (< 10ms per rule)
- ✅ Error messages clear and actionable
- ✅ Auto-fix tested and safe
- ✅ No regressions (all existing tests pass)

---

## 📈 WEEKLY PROGRESS TRACKING

### Week 1:
- ✅ 15 CDC/Clock/Reset rules
- ✅ 30+ tests
- ✅ 3 auto-fix generators

### Week 2:
- ✅ 12 Naming/Width rules
- ✅ 24+ tests
- ✅ 2 auto-fix generators

### Week 3:
- ✅ 13 Power/Structure rules
- ✅ 26+ tests
- ✅ 2 auto-fix generators

### Week 4:
- ✅ Config system
- ✅ Auto-fix engine
- ✅ 20+ tests

### Week 5:
- ✅ Performance optimization
- ✅ Batch mode
- ✅ 15+ tests
- ✅ CI/CD integration

### Week 6:
- ✅ Documentation
- ✅ Polish
- ✅ v5.0.0 release

---

## 🎯 ESTIMATED EFFORT

- Week 1: 12-15 hours
- Week 2: 10-12 hours
- Week 3: 10-12 hours
- Week 4: 8-10 hours
- Week 5: 8-10 hours
- Week 6: 10-12 hours

**Total**: 58-71 hours (~4-6 weeks at 15 hours/week)

---

## 🚀 READY TO START

**Next Step**: Begin Week 1 with TDD

Create first test for CDC_001, watch it fail, then implement!

**Let's achieve feature completeness! No hurry. TDD all the way!** 🎉

