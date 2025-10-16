// Test case for STR_004: Missing module header comment
// STR_004: Module without documentation header

module str_missing_header_violation (
  input logic clk,
  output logic data
);
  // Module implementation without header comment
  assign data = clk;
endmodule

// Good example with header
//-----------------------------------------------------------------------------
// Module: good_header_example
// Description: This module demonstrates proper header documentation
// Parameters: None
// Ports: clk (input), data (output)
//-----------------------------------------------------------------------------
module good_header_example (
  input logic clk,
  output logic data
);
  assign data = clk;
endmodule

