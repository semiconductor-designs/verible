// Test file: Uses macros from 3-level deep includes
`include "level1.svh"

module test_deep_nesting;
  int x, y, z, val;
  
  initial begin
    x = `LEVEL3_MACRO;    // From level 3 (deepest)
    y = `LEVEL2_MACRO;    // From level 2
    z = `LEVEL1_MACRO;    // From level 1
    val = `DEEP_MACRO;    // From level 3
  end
endmodule
