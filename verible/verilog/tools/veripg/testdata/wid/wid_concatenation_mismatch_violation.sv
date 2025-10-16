// Test case for WID_003: Concatenation width mismatch
module wid_concatenation_mismatch_violation;
  logic [3:0] a;
  logic [3:0] b;
  logic [7:0] result;
  
  // WID_003: Concatenation creates 8 bits, but result expects different width
  logic [9:0] result_10bit;
  assign result_10bit = {a, b};  // {4, 4} = 8 bits, but assigned to 10-bit
  
  // OK: Widths match
  assign result = {a, b};  // 8 bits = 8 bits
endmodule

