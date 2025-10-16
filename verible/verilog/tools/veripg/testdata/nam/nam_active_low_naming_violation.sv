// Test file for NAM_006: Active-low signals should end with "_n"

module nam_active_low_naming_violation(
  input wire enable_low,     // Violation: should be "enable_n"
  input wire valid_bar,      // Violation: should be "valid_n"
  input wire ready_n,        // OK: ends with "_n"
  input wire data
);
  logic chip_select_low;     // Violation: should be "chip_select_n"
  logic output_enable_n;     // OK
  
  assign output_enable_n = ready_n & enable_low;
endmodule

