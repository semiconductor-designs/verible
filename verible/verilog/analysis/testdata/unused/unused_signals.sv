// Test case: Completely unused signals
module unused_signals (
  input logic clk,
  input logic rst_n
);
  
  // ERROR: completely_unused never read or written
  logic completely_unused;
  
  // ERROR: another_unused never referenced
  logic another_unused;
  
  // ERROR: unused_wire never connected
  wire unused_wire;
  
  // OK: used_signal is both written and read
  logic used_signal;
  always_ff @(posedge clk) begin
    used_signal <= rst_n;
  end
  
  logic consumer;
  assign consumer = used_signal;
  
endmodule

