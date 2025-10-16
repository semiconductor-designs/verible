// Test case for NAM_004: Clock/reset signal naming conventions
module nam_clock_reset_naming_violation;
  logic clock;      // NAM_004: Should use standard 'clk' prefix
  logic my_reset;   // NAM_004: Should use standard 'rst' prefix
  
  logic clk;        // OK: standard clock naming
  logic rst_n;      // OK: standard reset naming
  logic clk_div2;   // OK: clock with description
endmodule

