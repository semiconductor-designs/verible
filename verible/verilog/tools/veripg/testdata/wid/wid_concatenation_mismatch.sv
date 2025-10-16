// Test file for WID_003: Concatenation width mismatch

module wid_concatenation_mismatch;
  logic [7:0] result8;
  logic [15:0] result16;
  logic [3:0] nibble1, nibble2;
  logic [7:0] byte1;
  
  initial begin
    result8 = {nibble1, nibble2};   // OK: 4+4=8
    result16 = {byte1, result8};    // OK: 8+8=16
    result8 = {byte1, nibble1};     // Violation: 8+4=12 into 8-bit (truncation)
    result16 = {result8, byte1, nibble1}; // Violation: 8+8+4=20 into 16-bit
  end
endmodule

