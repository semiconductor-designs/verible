// Multi-level dependency chains
module chained_assignments (
  input  logic a,
  output logic b,
  output logic c,
  output logic d,
  output logic e
);
  
  // Chain: a -> b -> c -> d -> e
  assign b = a;
  assign c = b;
  assign d = c;
  assign e = d;
  
  // e transitively depends on: a, b, c, d
  
endmodule

