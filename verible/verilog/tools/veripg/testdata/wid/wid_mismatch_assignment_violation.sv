// Test case for WID_001: Width mismatch in assignment
module wid_mismatch_assignment_violation;
  logic [7:0] data_8bit;
  logic [15:0] data_16bit;
  
  // WID_001: Width mismatch - assigning 16-bit to 8-bit
  assign data_8bit = data_16bit;  // Truncation warning
  
  // OK: Same width
  logic [7:0] data_8bit_2;
  assign data_8bit_2 = data_8bit;
endmodule

