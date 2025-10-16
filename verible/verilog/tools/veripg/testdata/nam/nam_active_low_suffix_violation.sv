// Test case for NAM_005: Active-low signals missing _n suffix
module nam_active_low_suffix_violation;
  logic enable_low;   // NAM_005: Active-low should use _n suffix (enable_n)
  logic reset;        // NAM_005: If active-low, should be reset_n
  
  logic enable_n;     // OK: _n suffix for active-low
  logic rst_n;        // OK: standard active-low naming
endmodule

