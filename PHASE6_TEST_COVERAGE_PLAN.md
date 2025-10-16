# Phase 6: Comprehensive Test Coverage Plan
## Gap 3: Negative Tests + Edge Cases

**Status**: In Progress  
**Goal**: Add 120+ tests (40+ negative, 80+ edge cases) for TRUE 100% coverage  
**Estimated Time**: 8-12 hours

---

## Test Coverage Metrics

### Current Status
- **Positive Tests** (violation detected): 63 test files ✅
- **Negative Tests** (no false positives): 2 test files (CDC only) 🔄
- **Edge Case Tests** (boundary conditions): 0 test files ❌
- **Total**: 65 / 185 target tests (35% coverage)

### Target Coverage
| Rule Category | Positive | Negative | Edge Cases | Total |
|--------------|----------|----------|------------|-------|
| CDC (4 rules) | 7 ✅ | 4 | 8 | 19 |
| CLK (4 rules) | 4 ✅ | 4 | 8 | 16 |
| RST (4 rules) | 4 ✅ | 4 | 8 | 16 |
| TIM (2 rules) | 2 ✅ | 2 | 4 | 8 |
| NAM (7 rules) | 10 ✅ | 7 | 14 | 31 |
| WID (5 rules) | 10 ✅ | 5 | 10 | 25 |
| PWR (5 rules) | 10 ✅ | 5 | 10 | 25 |
| STR (8 rules) | 16 ✅ | 8 | 16 | 40 |
| **TOTALS** | **63** | **39** | **78** | **180** |

---

## Implementation Plan

### Step 1: CDC Negative Tests (4 tests, 30min)
✅ `cdc_no_violation_proper_sync.sv` - Proper 2-stage synchronizer  
✅ `cdc_no_violation_gray_code.sv` - Multi-bit with Gray code  
⏸ `cdc_no_violation_async_fifo.sv` - Async FIFO with proper handshake  
⏸ `cdc_no_violation_single_domain.sv` - All signals in same clock domain  

### Step 2: CDC Edge Cases (8 tests, 1h)
⏸ `cdc_edge_three_stage_sync.sv` - 3-stage synchronizer (over-engineered but valid)  
⏸ `cdc_edge_handshake_protocol.sv` - REQ/ACK handshake CDC  
⏸ `cdc_edge_mux_data_path.sv` - Mux in data path (not clock path - OK)  
⏸ `cdc_edge_async_reset_same_domain.sv` - Async reset but same clock domain  
⏸ `cdc_edge_minimal_gray.sv` - 2-bit Gray code (minimum case)  
⏸ `cdc_edge_maximum_gray.sv` - 64-bit Gray code (maximum practical)  
⏸ `cdc_edge_synchronous_reset_cdc.sv` - Synchronous reset crossing (OK)  
⏸ `cdc_edge_tristate_buffer.sv` - Tristate buffers for CDC (rare but valid)  

### Step 3: CLK Negative Tests (4 tests, 30min)
⏸ `clk_no_violation_single_clock.sv` - Single clock in always_ff  
⏸ `clk_no_violation_derived_enable.sv` - Clock enable (not clock as data)  
⏸ `clk_no_violation_gated_with_icg.sv` - Properly gated clock with ICG cell  
⏸ `clk_no_violation_pll_output.sv` - PLL-generated clocks  

### Step 4: CLK Edge Cases (8 tests, 1h)
⏸ `clk_edge_negedge_only.sv` - Negedge clocking (valid)  
⏸ `clk_edge_both_edges.sv` - Both edges (DDR, valid with comment)  
⏸ `clk_edge_clock_divider.sv` - Clock divider (special case)  
⏸ `clk_edge_async_clear.sv` - Async clear without clock in sensitivity  
⏸ `clk_edge_latch_no_clock.sv` - Level-sensitive latch (no clock, OK)  
⏸ `clk_edge_combinational_only.sv` - No sequential logic (no clock needed)  
⏸ `clk_edge_initial_block.sv` - Initial block (simulation only, no clock)  
⏸ `clk_edge_generate_clock.sv` - Generated clock from logic (documented)  

### Step 5: RST Negative Tests (4 tests, 30min)
⏸ `rst_no_violation_sync_reset.sv` - Synchronous reset properly used  
⏸ `rst_no_violation_async_reset.sv` - Async reset properly synchronized  
⏸ `rst_no_violation_uniform_polarity.sv` - All resets active-low  
⏸ `rst_no_violation_async_set.sv` - Async set (not data path)  

### Step 6: RST Edge Cases (8 tests, 1h)
⏸ `rst_edge_power_on_reset.sv` - POR signal (special reset)  
⏸ `rst_edge_soft_reset.sv` - Software-controlled reset  
⏸ `rst_edge_watchdog_reset.sv` - Watchdog timer reset  
⏸ `rst_edge_reset_tree.sv` - Hierarchical reset distribution  
⏸ `rst_edge_conditional_reset.sv` - Conditional reset (with enable)  
⏸ `rst_edge_reset_synchronizer.sv` - Reset synchronizer itself  
⏸ `rst_edge_multi_domain_reset.sv` - Multiple independent reset domains  
⏸ `rst_edge_partial_reset.sv` - Partial state reset (subset of FFs)  

### Step 7: TIM Negative Tests (2 tests, 20min)
⏸ `tim_no_violation_registered_feedback.sv` - Feedback through register  
⏸ `tim_no_violation_complete_if.sv` - Complete if-else (no latch)  

### Step 8: TIM Edge Cases (4 tests, 40min)
⏸ `tim_edge_case_statement_full.sv` - Full case statement (no latch)  
⏸ `tim_edge_always_comb_blocking.sv` - always_comb with blocking (OK)  
⏸ `tim_edge_function_recursion.sv` - Function recursion (not comb loop)  
⏸ `tim_edge_bidirectional_buffer.sv` - Bidir buffer (special case)  

### Step 9: NAM Negative Tests (7 tests, 1h)
⏸ `nam_no_violation_good_names.sv` - All naming conventions followed  
⏸ `nam_no_violation_long_descriptive.sv` - Long but descriptive names  
⏸ `nam_no_violation_uppercase_params.sv` - UPPERCASE parameters  
⏸ `nam_no_violation_clock_prefix.sv` - clk_ prefix for clocks  
⏸ `nam_no_violation_reset_prefix.sv` - rst_ and rstn_ prefixes  
⏸ `nam_no_violation_active_low_suffix.sv` - _n suffix for active-low  
⏸ `nam_no_violation_no_keywords.sv` - No SystemVerilog keywords  

### Step 10: NAM Edge Cases (14 tests, 2h)
⏸ `nam_edge_abbreviations.sv` - Common abbreviations (clk, rst OK)  
⏸ `nam_edge_numbers_in_names.sv` - Numbers in signal names  
⏸ `nam_edge_hierarchical_names.sv` - Hierarchical path names  
⏸ `nam_edge_escaped_identifiers.sv` - Escaped identifiers  
⏸ `nam_edge_unicode_names.sv` - Unicode in identifiers (SV2017+)  
⏸ `nam_edge_macro_defines.sv` - Macro-defined names  
⏸ `nam_edge_generate_names.sv` - Generated block names  
⏸ `nam_edge_interface_names.sv` - Interface signal names  
⏸ `nam_edge_struct_member_names.sv` - Struct member naming  
⏸ `nam_edge_enum_names.sv` - Enum value naming  
⏸ `nam_edge_package_names.sv` - Package and import names  
⏸ `nam_edge_min_length_three.sv` - Exactly 3 chars (boundary)  
⏸ `nam_edge_underscore_heavy.sv` - Heavy use of underscores  
⏸ `nam_edge_mixed_conventions.sv` - Mixed but documented conventions  

### Step 11: WID Negative Tests (5 tests, 1h)
⏸ `wid_no_violation_matching_widths.sv` - All widths match  
⏸ `wid_no_violation_explicit_cast.sv` - Explicit width casting  
⏸ `wid_no_violation_sized_constants.sv` - Properly sized constants  
⏸ `wid_no_violation_parameter_consistent.sv` - Parameter widths consistent  
⏸ `wid_no_violation_port_widths_match.sv` - Port widths match connections  

### Step 12: WID Edge Cases (10 tests, 1.5h)
⏸ `wid_edge_sign_extension.sv` - Signed extension (valid)  
⏸ `wid_edge_zero_extension.sv` - Zero extension (valid)  
⏸ `wid_edge_dynamic_width.sv` - Width depends on parameter  
⏸ `wid_edge_packed_struct.sv` - Packed struct width calculations  
⏸ `wid_edge_union_width.sv` - Union width (max of members)  
⏸ `wid_edge_part_select.sv` - Part-select width  
⏸ `wid_edge_replication.sv` - Replication operator `{N{x}}`  
⏸ `wid_edge_streaming_operator.sv` - Streaming operators  
⏸ `wid_edge_1bit_to_1bit.sv` - 1-bit signals (minimum width)  
⏸ `wid_edge_max_width.sv` - Very wide signals (1024-bit)  

### Step 13: PWR Negative Tests (5 tests, 1h)
⏸ `pwr_no_violation_upf_annotated.sv` - Proper UPF annotations  
⏸ `pwr_no_violation_level_shifters.sv` - Level shifters at boundaries  
⏸ `pwr_no_violation_isolation_cells.sv` - Isolation cells present  
⏸ `pwr_no_violation_retention.sv` - Retention registers annotated  
⏸ `pwr_no_violation_single_domain.sv` - Single power domain (no crossing)  

### Step 14: PWR Edge Cases (10 tests, 1.5h)
⏸ `pwr_edge_always_on_domain.sv` - Always-on power domain  
⏸ `pwr_edge_multiple_domains.sv` - 3+ power domains  
⏸ `pwr_edge_nested_domains.sv` - Nested power hierarchy  
⏸ `pwr_edge_partial_powerdown.sv` - Partial module power-down  
⏸ `pwr_edge_power_switch.sv` - Power switch cells  
⏸ `pwr_edge_dvfs.sv` - Dynamic voltage/frequency scaling  
⏸ `pwr_edge_backup_restore.sv` - State backup/restore  
⏸ `pwr_edge_clock_gating.sv` - Clock gating for power  
⏸ `pwr_edge_substrate_biasing.sv` - Body biasing for power  
⏸ `pwr_edge_multi_threshold.sv` - Multi-Vt cells  

### Step 15: STR Negative Tests (8 tests, 1h)
⏸ `str_no_violation_good_structure.sv` - Well-structured module  
⏸ `str_no_violation_low_complexity.sv` - Simple, clean logic  
⏸ `str_no_violation_flat_hierarchy.sv` - Flat hierarchy (2-3 levels)  
⏸ `str_no_violation_header_comments.sv` - Proper header comments  
⏸ `str_no_violation_port_ordering.sv` - clk, rst, input, output order  
⏸ `str_no_violation_named_ports.sv` - Named port connections  
⏸ `str_no_violation_labeled_generate.sv` - All generate blocks labeled  
⏸ `str_no_violation_default_case.sv` - All case statements with default  

### Step 16: STR Edge Cases (16 tests, 2h)
⏸ `str_edge_testbench_no_ports.sv` - Testbench module (no ports OK)  
⏸ `str_edge_complexity_exactly_50.sv` - Exactly 50 statements (boundary)  
⏸ `str_edge_hierarchy_exactly_5.sv` - Exactly 5 levels (boundary)  
⏸ `str_edge_doxygen_comments.sv` - Doxygen-style headers  
⏸ `str_edge_naturaldocs_comments.sv` - NaturalDocs-style headers  
⏸ `str_edge_port_ordering_documented.sv` - Different order but documented  
⏸ `str_edge_positional_primitives.sv` - Positional for primitives only  
⏸ `str_edge_mixed_connection_styles.sv` - Mixed but consistent  
⏸ `str_edge_generate_with_label.sv` - Generate with proper labels  
⏸ `str_edge_default_with_warning.sv` - Default with explicit comment  
⏸ `str_edge_interface_ports.sv` - Interface as port (different structure)  
⏸ `str_edge_virtual_interface.sv` - Virtual interface usage  
⏸ `str_edge_class_definition.sv` - Class definitions (OOP)  
⏸ `str_edge_package_definition.sv` - Package definitions  
⏸ `str_edge_bind_statement.sv` - Bind statements for assertions  
⏸ `str_edge_config_block.sv` - Configuration blocks  

---

## Test Implementation Strategy

### Phase A: Create Negative Test Files (4-6 hours)
For each rule, create test files that should **NOT** trigger violations:
- Properly implemented designs
- Best practices followed
- Valid but unusual patterns

### Phase B: Create Edge Case Test Files (4-6 hours)
For each rule, create test files for boundary conditions:
- Minimum/maximum values
- Unusual but valid constructs
- Corner cases from SystemVerilog LRM

### Phase C: Update Integration Tests (1-2 hours)
Add test cases to integration test files:
- Assert NO violations for negative tests
- Assert correct behavior for edge cases
- Measure false positive rate

### Phase D: Documentation (1 hour)
Document:
- Test coverage metrics
- Known limitations of heuristic-based rules
- False positive/negative rates per rule

---

## Success Criteria

✅ **Coverage**: 180+ total tests (63 positive + 39 negative + 78 edge cases)  
✅ **No False Positives**: Negative tests pass (0 violations detected)  
✅ **Edge Cases Handled**: Boundary conditions properly classified  
✅ **Documentation**: Coverage report with metrics  
✅ **Confidence**: >95% confidence in rule accuracy  

---

## Current Progress

**Created**: 2/180 tests (1.1%)  
**Status**: Just started  
**Next**: Continue with CDC edge cases, then scale to all 40 rules  
**Estimated Remaining**: 8-10 hours  


