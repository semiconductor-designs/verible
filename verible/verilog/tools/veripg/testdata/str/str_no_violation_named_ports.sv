// Copyright 2025 The Verible Authors.
// Negative test: Named port connections - NO violation

module submodule (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) data_out <= 8'h00;
    else data_out <= data_in;
  end
endmodule

module str_no_violation_named_ports (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Named port connections (good practice)
  submodule u_sub (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in),
    .data_out(data_out)
  );

endmodule

