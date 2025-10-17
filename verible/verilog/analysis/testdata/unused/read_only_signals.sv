// Test case: Read-only signals (never written - undriven)
module read_only_signals (
  output logic data_out
);
  
  // WARNING: read_only is read but never written (undriven)
  logic read_only;  // No driver!
  assign data_out = read_only;  // Reading undriven signal
  
  // WARNING: undriven_signal has no driver
  logic undriven_signal;
  logic consumer;
  assign consumer = undriven_signal;  // Reads undefined value
  
  // OK: properly_driven has both driver and reader
  logic properly_driven;
  assign properly_driven = 1'b1;  // Driver
  logic result;
  assign result = properly_driven;  // Reader
  
endmodule

