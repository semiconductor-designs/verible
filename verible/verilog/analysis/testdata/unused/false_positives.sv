// Test case: Common false positives (should be filtered)
module false_positives (
  // OK: Input ports can be unused (filtered if ignore_inputs = true)
  input logic unused_input_port,
  input logic clk,
  
  // OK: Output ports can be write-only (filtered if ignore_outputs = true)
  output logic write_only_output
);
  
  // OK: Signals with "unused_" prefix are intentionally unused
  logic unused_debug_signal;
  logic unused_for_future_use;
  
  // OK: This output port is write-only, which is acceptable
  assign write_only_output = clk;
  
  // OK: Test/debug signals
  logic debug_probe;
  assign debug_probe = clk;
  
endmodule

