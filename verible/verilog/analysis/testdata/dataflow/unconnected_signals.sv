// Signals with no drivers or readers (edge case)
module unconnected_signals (
  input  logic a,
  output logic b
);
  
  // Undriven signal (no writers)
  logic undriven_signal;
  
  // Unread signal (no readers)
  logic unread_signal;
  assign unread_signal = a;
  
  // Write-only signal
  logic write_only;
  assign write_only = a;
  // write_only is never read
  
  // Read-only signal (uses undriven_signal which has no driver)
  assign b = undriven_signal;
  
endmodule

