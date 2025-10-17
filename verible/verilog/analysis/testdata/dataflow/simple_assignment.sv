// Simple data flow: basic wire assignments
module simple_assignment (
  input  logic clk,
  input  logic a,
  output logic b,
  output logic c
);
  
  // Simple continuous assignment: a drives b
  assign b = a;
  
  // Chained assignment: b drives c
  assign c = b;
  
endmodule

