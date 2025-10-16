// Copyright 2025 The Verible Authors.
// Edge case: External names (DPI-C)

module str_edge_external_names (
  input wire clk,
  input wire rst_n,
  input wire [31:0] input_value,
  output logic [31:0] output_value
);

  // DPI-C import for external C function
  import "DPI-C" function int external_compute(input int value);
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      output_value <= 32'h0;
    end else begin
      // Call external C function
      output_value <= external_compute(input_value);
    end
  end

endmodule

