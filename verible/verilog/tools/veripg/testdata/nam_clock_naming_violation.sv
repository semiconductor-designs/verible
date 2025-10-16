// Test file for NAM_004: Clock signals should start with "clk_"

module nam_clock_naming_violation(
  input wire clock,          // Violation: should be "clk_clock" or "clk"
  input wire system_clk,     // Violation: should be "clk_system"
  input wire clk_valid,      // OK: starts with "clk_"
  input wire data
);
  logic internal_clock;      // Violation: should be "clk_internal"
  logic clk_core;            // OK
  
  always_ff @(posedge clock) begin
    clk_core <= clk_valid;
  end
endmodule

