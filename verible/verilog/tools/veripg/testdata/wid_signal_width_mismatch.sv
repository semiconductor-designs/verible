// Test file for WID_001: Signal width mismatch in assignment

module wid_signal_width_mismatch;
  logic [7:0] data8;
  logic [3:0] data4;
  logic [15:0] data16;
  
  initial begin
    data4 = data8;   // Violation: 8-bit assigned to 4-bit (truncation)
    data16 = data4;  // OK: 4-bit assigned to 16-bit (zero-extension)
    data8 = data8;   // OK: same width
  end
endmodule

