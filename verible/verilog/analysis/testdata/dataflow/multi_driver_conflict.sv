// Multiple drivers causing conflicts
module multi_driver_conflict (
  input  logic clk,
  input  logic a,
  input  logic b,
  output logic conflict_signal
);
  
  // ERROR: conflict_signal has two drivers (multi-driver conflict)
  
  // Driver 1: continuous assignment
  assign conflict_signal = a;
  
  // Driver 2: always block
  always_ff @(posedge clk) begin
    conflict_signal <= b;
  end
  
  // This should be detected as a multi-driver conflict
  
endmodule

