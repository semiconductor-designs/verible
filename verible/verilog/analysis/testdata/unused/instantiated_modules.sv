// Test case: Modules that ARE instantiated (should NOT be flagged)
module child_module (
  input logic clk,
  input logic data,
  output logic result
);
  assign result = data & clk;
endmodule

module another_child (
  input logic a,
  output logic b
);
  assign b = ~a;
endmodule

// Parent module that instantiates the above modules
module parent_module (
  input logic clk,
  input logic in1,
  input logic in2,
  output logic out1,
  output logic out2
);
  
  // Both child modules are instantiated
  child_module u_child1 (
    .clk(clk),
    .data(in1),
    .result(out1)
  );
  
  another_child u_child2 (
    .a(in2),
    .b(out2)
  );
  
endmodule

