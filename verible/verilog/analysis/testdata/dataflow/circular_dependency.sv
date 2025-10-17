// Circular dependency (combinational loop - ERROR)
module circular_dependency (
  input  logic a,
  output logic result
);
  
  logic b, c;
  
  // ERROR: Combinational loop (circular dependency)
  assign b = c & a;     // b depends on c
  assign c = b | a;     // c depends on b
  
  // This creates a circular dependency: b -> c -> b
  
  assign result = b;
  
endmodule

