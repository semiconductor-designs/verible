// Test case: Pattern-based filtering
module ignore_patterns (
  input logic clk
);
  
  // OK: Should be ignored by pattern "unused_*"
  logic unused_intentional;
  logic unused_for_debug;
  logic unused_reserved;
  
  // OK: Should be ignored by pattern "*_debug"
  logic signal_debug;
  logic temp_debug;
  
  // OK: Should be ignored by pattern "*_reserved"
  logic future_reserved;
  
  // ERROR: Should NOT be ignored (doesn't match patterns)
  logic actually_unused_signal;
  
endmodule

