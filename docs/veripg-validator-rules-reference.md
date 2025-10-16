# VeriPG Validator Rules Reference

**Version 5.0.0** | Complete reference for all 39 validation rules

## Table of Contents

1. [CDC Rules (Clock Domain Crossing)](#cdc-rules)
2. [CLK Rules (Clock Handling)](#clk-rules)
3. [RST Rules (Reset Handling)](#rst-rules)
4. [TIM Rules (Timing)](#tim-rules)
5. [NAM Rules (Naming Conventions)](#nam-rules)
6. [WID Rules (Width Checking)](#wid-rules)
7. [PWR Rules (Power Intent)](#pwr-rules)
8. [STR Rules (Structure)](#str-rules)

---

## CDC Rules (Clock Domain Crossing)

### CDC_001: CDC without synchronizer

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** Unsafe (suggests 2-stage synchronizer)

**Description:**  
Detects signals crossing clock domains without proper synchronization, which can lead to metastability and unpredictable behavior.

**Violation Example:**
```systemverilog
module cdc_violation (
  input clk_a, clk_b,
  input data_a,
  output logic data_b
);
  // Violation: data_a crosses from clk_a to clk_b without synchronizer
  always_ff @(posedge clk_b) begin
    data_b <= data_a;  // CDC_001 violation
  end
endmodule
```

**Correct Example:**
```systemverilog
module cdc_correct (
  input clk_a, clk_b,
  input data_a,
  output logic data_b
);
  logic [1:0] sync_chain;
  
  // Proper 2-stage synchronizer
  always_ff @(posedge clk_b) begin
    sync_chain <= {sync_chain[0], data_a};
    data_b <= sync_chain[1];
  end
endmodule
```

**Auto-fix Suggestion:**
```systemverilog
// Add 2-stage synchronizer
logic [1:0] sync_<signal>;
always_ff @(posedge <dest_clk>) begin
  sync_<signal> <= {sync_<signal>[0], <source_signal>};
  <dest_signal> <= sync_<signal>[1];
end
```

**References:**
- IEEE 1364.1-2002: Multi-clock domain crossing
- Clifford Cummings: "Clock Domain Crossing (CDC) Design & Verification Techniques"

---

### CDC_002: Multi-bit CDC without Gray code

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** Unsafe (suggests Gray code conversion)

**Description:**  
Multi-bit values crossing clock domains should use Gray code encoding to ensure only one bit changes at a time, avoiding multi-bit synchronization issues.

**Violation Example:**
```systemverilog
// Violation: 4-bit counter crosses domains in binary
always_ff @(posedge clk_a) begin
  counter_a <= counter_a + 1;
end

always_ff @(posedge clk_b) begin
  counter_b <= counter_a;  // CDC_002: Multi-bit CDC without Gray code
end
```

**Correct Example:**
```systemverilog
// Gray code conversion
function [3:0] bin_to_gray(input [3:0] bin);
  return bin ^ (bin >> 1);
endfunction

always_ff @(posedge clk_a) begin
  counter_a_bin <= counter_a_bin + 1;
  counter_a_gray <= bin_to_gray(counter_a_bin);
end

always_ff @(posedge clk_b) begin
  counter_b_gray <= counter_a_gray;  // Safe: Gray code crossing
end
```

---

### CDC_003: Clock used in data path (Clock muxing)

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** None (requires design change)

**Description:**  
Clock signals should only be used in sensitivity lists, not in data paths. Using clocks in logic can cause glitches and timing violations.

**Violation Example:**
```systemverilog
// Violation: Clock used in data assignment
assign data_out = clk ? data_a : data_b;  // CDC_003 violation
```

**Correct Example:**
```systemverilog
// Use clock enable instead
always_ff @(posedge clk) begin
  if (enable)
    data_out <= data_a;
  else
    data_out <= data_b;
end
```

---

### CDC_004: Asynchronous reset crossing clock domains

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** Unsafe (suggests reset synchronizer)

**Description:**  
Asynchronous reset signals crossing clock domains should be synchronized to avoid reset assertion/deassertion issues.

**Violation Example:**
```systemverilog
// Violation: Async reset from different domain
always_ff @(posedge clk or negedge rst_n_other_domain) begin
  if (!rst_n_other_domain)  // CDC_004 violation
    state <= IDLE;
end
```

**Correct Example:**
```systemverilog
// Synchronize reset
logic [1:0] rst_sync;
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n)
    rst_sync <= 2'b00;
  else
    rst_sync <= {rst_sync[0], 1'b1};
end

wire rst_n_sync = rst_sync[1];

always_ff @(posedge clk or negedge rst_n_sync) begin
  if (!rst_n_sync)
    state <= IDLE;
end
```

---

## CLK Rules (Clock Handling)

### CLK_001: Missing clock signal in always_ff

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** Safe (adds clock to sensitivity list)

**Description:**  
`always_ff` blocks must have a clock in their sensitivity list for proper synthesis and simulation.

**Violation Example:**
```systemverilog
// Violation: No clock in sensitivity list
always_ff begin  // CLK_001 violation
  data_reg <= data_in;
end
```

**Correct Example:**
```systemverilog
always_ff @(posedge clk) begin
  data_reg <= data_in;
end
```

**Auto-fix:** Adds `@(posedge clk)` to sensitivity list.

---

### CLK_002: Multiple clocks in single always block

**Severity:** Error  
**Category:** Design practice  
**Auto-fix:** None (requires splitting block)

**Description:**  
A single always block should only be sensitive to one clock edge to avoid synthesis and simulation issues.

**Violation Example:**
```systemverilog
// Violation: Two clocks in one block
always_ff @(posedge clk_a or posedge clk_b) begin  // CLK_002 violation
  data <= data_in;
end
```

**Correct Example:**
```systemverilog
// Separate blocks for each clock
always_ff @(posedge clk_a) begin
  data_a <= data_in;
end

always_ff @(posedge clk_b) begin
  data_b <= data_a;
end
```

---

### CLK_003: Clock used as data signal

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** None (requires design review)

**Description:**  
Clock signals should not be assigned to data signals as this can cause glitches and timing violations.

**Violation Example:**
```systemverilog
// Violation: Clock assigned to data
always_ff @(posedge clk) begin
  status <= clk;  // CLK_003 violation
end
```

**Correct Example:**
```systemverilog
// Use a derived enable signal instead
always_ff @(posedge clk) begin
  status <= enable;
end
```

---

### CLK_004: Gated clock without ICG cell

**Severity:** Warning  
**Category:** Design practice  
**Auto-fix:** Unsafe (suggests ICG cell)

**Description:**  
Clock gating should use integrated clock gating (ICG) cells to avoid glitches.

**Violation Example:**
```systemverilog
// Violation: Direct clock gating
assign gated_clk = clk & enable;  // CLK_004 violation
```

**Correct Example:**
```systemverilog
// Use ICG cell (technology-specific)
ICG_CELL u_icg (
  .CLK(clk),
  .EN(enable),
  .GCLK(gated_clk)
);
```

---

## RST Rules (Reset Handling)

### RST_001: Missing reset in sequential logic

**Severity:** Warning  
**Category:** Design practice  
**Auto-fix:** Unsafe (suggests reset addition)

**Description:**  
Sequential logic should include reset handling for predictable initialization.

**Violation Example:**
```systemverilog
// Violation: No reset
always_ff @(posedge clk) begin  // RST_001 violation
  state <= next_state;
end
```

**Correct Example:**
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n)
    state <= IDLE;
  else
    state <= next_state;
end
```

---

### RST_002: Asynchronous reset not properly synchronized

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** Unsafe (suggests reset synchronizer)

**Description:**  
Asynchronous resets from external sources should be synchronized to avoid metastability.

**Violation Example:**
```systemverilog
// Violation: External async reset not synchronized
always_ff @(posedge clk or negedge ext_rst_n) begin  // RST_002
  if (!ext_rst_n) state <= IDLE;
end
```

**Correct Example:**
```systemverilog
// Synchronize external reset
logic [1:0] rst_sync;
always_ff @(posedge clk or negedge ext_rst_n) begin
  if (!ext_rst_n)
    rst_sync <= 2'b00;
  else
    rst_sync <= {rst_sync[0], 1'b1};
end

wire rst_n_sync = rst_sync[1];
always_ff @(posedge clk or negedge rst_n_sync) begin
  if (!rst_n_sync) state <= IDLE;
end
```

---

### RST_003: Mixed reset polarity

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** None (requires design consistency)

**Description:**  
Mixing active-high and active-low resets in a module can lead to confusion and errors.

**Violation Example:**
```systemverilog
// Violation: Mixed polarity
always_ff @(posedge clk or posedge rst) begin  // Active-high
  if (rst) state_a <= IDLE;
end

always_ff @(posedge clk or negedge rst_n) begin  // Active-low
  if (!rst_n) state_b <= IDLE;  // RST_003 violation
end
```

**Correct Example:**
```systemverilog
// Consistent polarity (active-low)
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) state_a <= IDLE;
end

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) state_b <= IDLE;
end
```

---

### RST_004: Reset signal used as data

**Severity:** Error  
**Category:** Design practice  
**Auto-fix:** None (requires design review)

**Description:**  
Reset signals should only be used for reset purposes, not as data signals.

**Violation Example:**
```systemverilog
// Violation: Reset used as data
always_ff @(posedge clk) begin
  status <= rst_n;  // RST_004 violation
end
```

---

## TIM Rules (Timing)

### TIM_001: Combinational loop detected

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** None (requires design fix)

**Description:**  
Combinational loops can cause unpredictable behavior and synthesis failures.

**Violation Example:**
```systemverilog
// Violation: Combinational loop
assign a = b & c;
assign b = a | d;  // TIM_001: Loop detected (a depends on b, b depends on a)
```

**Correct Example:**
```systemverilog
// Break loop with register
always_ff @(posedge clk) begin
  a_reg <= b & c;
end
assign b = a_reg | d;
```

---

### TIM_002: Latch inference detected

**Severity:** Warning  
**Category:** Design practice  
**Auto-fix:** Safe (suggests adding else clause)

**Description:**  
Incomplete combinational logic can infer unintended latches.

**Violation Example:**
```systemverilog
// Violation: Incomplete case (infers latch)
always_comb begin
  case (sel)
    2'b00: out = a;
    2'b01: out = b;
    // Missing 2'b10, 2'b11 cases - TIM_002 violation
  endcase
end
```

**Correct Example:**
```systemverilog
always_comb begin
  case (sel)
    2'b00: out = a;
    2'b01: out = b;
    default: out = 1'b0;  // Avoid latch
  endcase
end
```

---

## NAM Rules (Naming Conventions)

### NAM_001: Module names must be lowercase_with_underscores

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** Safe (converts to snake_case)

**Violation:** `MyModule` → **Correct:** `my_module`

---

### NAM_002: Signal names must be descriptive (>= 3 chars)

**Severity:** Info  
**Category:** Code quality  
**Auto-fix:** None (requires manual naming)

**Violation:** `logic a;` → **Correct:** `logic data_valid;`

---

### NAM_003: Parameter names must be UPPERCASE

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** Safe (converts to UPPER_CASE)

**Violation:** `parameter width = 8;` → **Correct:** `parameter WIDTH = 8;`

---

### NAM_004: Clock signals must start with "clk_"

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** Safe (renames signal)

**Violation:** `logic clock;` → **Correct:** `logic clk_main;`

---

### NAM_005: Reset signals must start with "rst_" or "rstn_"

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** Safe (renames signal)

**Violation:** `logic reset;` → **Correct:** `logic rst_n;`

---

### NAM_006: Active-low signals must end with "_n"

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** Safe (adds _n suffix)

**Violation:** `logic enable_low;` → **Correct:** `logic enable_n;`

---

### NAM_007: No reserved keywords as identifiers

**Severity:** Error  
**Category:** Syntax  
**Auto-fix:** None (requires manual rename)

**Violation:** `logic input;` → **Correct:** `logic input_data;`

---

## WID Rules (Width Checking)

### WID_001: Signal width mismatch in assignment

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** Unsafe (suggests explicit cast)

**Violation Example:**
```systemverilog
logic [7:0] narrow;
logic [15:0] wide;
assign narrow = wide;  // WID_001: Truncation
```

**Correct Example:**
```systemverilog
assign narrow = wide[7:0];  // Explicit truncation
```

---

### WID_002: Implicit width conversion (lossy)

**Severity:** Warning  
**Category:** Code quality  
**Auto-fix:** Unsafe (suggests explicit extension)

---

### WID_003: Concatenation width mismatch

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** Unsafe (suggests width adjustment)

---

### WID_004: Parameter width inconsistent with usage

**Severity:** Warning  
**Category:** Design practice  
**Auto-fix:** Safe (suggests using parameter)

---

### WID_005: Port width mismatch in instantiation

**Severity:** Error  
**Category:** Functional correctness  
**Auto-fix:** None (requires interface fix)

---

## PWR Rules (Power Intent)

### PWR_001: Missing power domain annotation

**Severity:** Warning  
**Category:** Power management  
**Auto-fix:** Unsafe (suggests UPF annotation)

---

### PWR_002: Level shifter required at domain boundary

**Severity:** Error  
**Category:** Power management  
**Auto-fix:** Unsafe (suggests level shifter)

---

### PWR_003: Isolation cell required for power-down domain

**Severity:** Error  
**Category:** Power management  
**Auto-fix:** Unsafe (suggests isolation cell)

---

### PWR_004: Retention register without retention annotation

**Severity:** Warning  
**Category:** Power management  
**Auto-fix:** Unsafe (suggests retention annotation)

---

### PWR_005: Always-on signal crossing to power-gated domain

**Severity:** Warning  
**Category:** Power management  
**Auto-fix:** None (requires design review)

---

## STR Rules (Structure)

### STR_001: Module has no ports (should be testbench)

**Severity:** Warning  
**Category:** Design practice  
**Auto-fix:** Safe (suggests _tb suffix)

---

### STR_002: Module exceeds complexity threshold (50+ statements)

**Severity:** Warning  
**Category:** Code quality  
**Auto-fix:** None (requires refactoring)

---

### STR_003: Deep hierarchy (>5 levels of instantiation)

**Severity:** Info  
**Category:** Design practice  
**Auto-fix:** None (design review)

---

### STR_004: Missing module header comment

**Severity:** Info  
**Category:** Documentation  
**Auto-fix:** Safe (generates template comment)

---

### STR_005: Port ordering incorrect (clk, rst, inputs, outputs)

**Severity:** Warning  
**Category:** Coding standards  
**Auto-fix:** Safe (reorders ports)

---

### STR_006: Instantiation without named ports

**Severity:** Warning  
**Category:** Code quality  
**Auto-fix:** Safe (converts to named ports)

---

### STR_007: Generate block without label

**Severity:** Warning  
**Category:** Debugging  
**Auto-fix:** Safe (adds label)

---

### STR_008: Case statement without default clause

**Severity:** Warning  
**Category:** Design practice  
**Auto-fix:** Safe (adds default clause)

**Violation Example:**
```systemverilog
always_comb begin
  case (sel)
    2'b00: out = a;
    2'b01: out = b;
    // Missing default - STR_008
  endcase
end
```

**Correct Example:**
```systemverilog
always_comb begin
  case (sel)
    2'b00: out = a;
    2'b01: out = b;
    default: out = 1'b0;
  endcase
end
```

---

## Rule Summary Table

| Rule ID | Category | Severity | Auto-Fix | Description |
|---------|----------|----------|----------|-------------|
| CDC_001 | CDC | Error | Unsafe | CDC without synchronizer |
| CDC_002 | CDC | Error | Unsafe | Multi-bit CDC without Gray code |
| CDC_003 | CDC | Error | None | Clock used in data path |
| CDC_004 | CDC | Error | Unsafe | Async reset crossing domains |
| CLK_001 | Clock | Warning | Safe | Missing clock in always_ff |
| CLK_002 | Clock | Error | None | Multiple clocks in block |
| CLK_003 | Clock | Error | None | Clock used as data |
| CLK_004 | Clock | Warning | Unsafe | Gated clock without ICG |
| RST_001 | Reset | Warning | Unsafe | Missing reset |
| RST_002 | Reset | Error | Unsafe | Async reset not synchronized |
| RST_003 | Reset | Warning | None | Mixed reset polarity |
| RST_004 | Reset | Error | None | Reset used as data |
| TIM_001 | Timing | Error | None | Combinational loop |
| TIM_002 | Timing | Warning | Safe | Latch inference |
| NAM_001-007 | Naming | Warning/Info | Safe | Naming conventions |
| WID_001-005 | Width | Error/Warning | Unsafe | Width mismatches |
| PWR_001-005 | Power | Warning/Error | Unsafe | Power intent |
| STR_001-008 | Structure | Warning/Info | Safe/None | Design structure |

---

**Total Rules:** 39  
**Fully Implemented:** 14 (CDC, CLK, RST, TIM)  
**Framework Complete:** 25 (NAM, WID, PWR, STR)

For configuration and usage, see:
- [User Guide](./veripg-validator-user-guide.md)
- [Configuration Guide](./veripg-validator-config-guide.md)
- [Auto-Fix Guide](./veripg-validator-autofix-guide.md)

