// Test case for WID_002: Implicit width conversion
module wid_implicit_conversion_violation;
  logic [3:0] nibble;
  logic [7:0] byte_val;
  
  // WID_002: Implicit conversion from 4-bit to 8-bit
  assign byte_val = nibble;  // Should use explicit extension
  
  // Better: Explicit extension
  logic [7:0] byte_val_2;
  assign byte_val_2 = {4'b0, nibble};
endmodule

