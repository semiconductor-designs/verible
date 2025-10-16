// Test file for WID_002: Implicit width conversion (lossy)

module wid_implicit_conversion;
  logic [7:0] data8;
  logic [15:0] data16;
  logic [31:0] data32;
  
  initial begin
    data8 = data16[15:8];  // OK: explicit slice
    data8 = data16;        // Violation: implicit truncation from 16 to 8
    data32 = data16;       // OK: zero-extension
    data16 = data32;       // Violation: implicit truncation from 32 to 16
  end
endmodule

