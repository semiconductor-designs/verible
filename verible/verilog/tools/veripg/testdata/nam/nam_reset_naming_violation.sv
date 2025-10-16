// Test file for NAM_005: Reset signals should start with "rst_" or "rstn_"

module nam_reset_naming_violation(
  input wire reset,          // Violation: should be "rst_reset" or "rst"
  input wire async_reset,    // Violation: should be "rst_async"
  input wire rst_valid,      // OK: starts with "rst_"
  input wire rstn_async,     // OK: starts with "rstn_"
  input wire data
);
  logic internal_reset;      // Violation: should be "rst_internal"
  logic rst_core;            // OK
  
  always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
      rst_core <= 1'b0;
    end else begin
      rst_core <= rst_valid;
    end
  end
endmodule

