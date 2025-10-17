// Test file: Module that instantiates non-existent module
// Should generate error about missing module

module parent_with_missing (
  input logic clk,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  
  logic [7:0] from_missing;
  
  // This module doesn't exist - should be detected as error
  non_existent_module u_missing (
    .clk(clk),
    .data_in(data_in),
    .data_out(from_missing)
  );
  
  assign data_out = from_missing;
  
endmodule

