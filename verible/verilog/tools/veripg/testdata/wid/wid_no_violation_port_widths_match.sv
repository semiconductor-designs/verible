// Copyright 2025 The Verible Authors.
// Negative test: Port widths match in instantiation - NO violation

module wid_submodule (
  input wire clk,
  input wire [7:0] data_in,
  output logic [15:0] data_out
);
  always_ff @(posedge clk) begin
    data_out <= {data_in, data_in};
  end
endmodule

module wid_no_violation_port_widths_match (
  input wire clk,
  input wire rst_n,
  input wire [7:0] input_data,
  output logic [15:0] output_data
);

  logic [7:0] internal_data;
  logic [15:0] internal_result;
  
  assign internal_data = input_data;
  
  // Port widths match exactly
  wid_submodule u_sub (
    .clk(clk),
    .data_in(internal_data),    // 8-bit to 8-bit ✓
    .data_out(internal_result)  // 16-bit to 16-bit ✓
  );
  
  assign output_data = internal_result;

endmodule

