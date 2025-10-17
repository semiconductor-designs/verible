// Test case: Module definitions never instantiated
// WARNING: unused_module is defined but never instantiated
module unused_module (
  input logic clk,
  output logic data_out
);
  assign data_out = clk;
endmodule

// WARNING: another_unused_module is also not instantiated
module another_unused_module (
  input logic a,
  input logic b,
  output logic c
);
  assign c = a & b;
endmodule

// OK: used_module IS instantiated below
module used_module (
  input logic x,
  output logic y
);
  assign y = ~x;
endmodule

// Top-level module that uses used_module
module top_with_instance (
  input logic in,
  output logic out
);
  
  // This instantiates used_module, so it should NOT be flagged
  used_module u_inst (
    .x(in),
    .y(out)
  );
  
endmodule

