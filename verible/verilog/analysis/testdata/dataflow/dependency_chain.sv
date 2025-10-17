// Transitive dependency chains
module dependency_chain (
  input  logic a,
  input  logic b,
  output logic result
);
  
  logic intermediate1, intermediate2, intermediate3;
  
  // Build dependency chain
  assign intermediate1 = a & b;        // depends on: a, b
  assign intermediate2 = intermediate1 | a;  // depends on: intermediate1, a -> transitively: a, b
  assign intermediate3 = intermediate2 ^ b;  // depends on: intermediate2, b -> transitively: a, b
  assign result = intermediate3;       // depends on: intermediate3 -> transitively: a, b
  
  // result transitively depends on: a, b, intermediate1, intermediate2, intermediate3
  
endmodule

