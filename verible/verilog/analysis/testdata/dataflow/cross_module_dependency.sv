// Data flow across module boundaries
module child_module (
  input  logic in,
  output logic out
);
  assign out = ~in;
endmodule

module cross_module_dependency (
  input  logic a,
  output logic result
);
  
  logic intermediate;
  
  // Data flows: a -> child -> intermediate -> result
  child_module u_child (
    .in(a),
    .out(intermediate)
  );
  
  assign result = intermediate & a;
  
endmodule

