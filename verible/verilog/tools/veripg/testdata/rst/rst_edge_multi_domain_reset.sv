// Copyright 2025 The Verible Authors.
// Edge case: Multiple independent reset domains

module rst_edge_multi_domain_reset (
  input wire clk_a,
  input wire clk_b,
  input wire rst_domain_a_n,
  input wire rst_domain_b_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out_a,
  output logic [7:0] data_out_b
);

  // Domain A with its own reset
  always_ff @(posedge clk_a or negedge rst_domain_a_n) begin
    if (!rst_domain_a_n)
      data_out_a <= 8'h00;
    else
      data_out_a <= data_in;
  end
  
  // Domain B with its own independent reset
  always_ff @(posedge clk_b or negedge rst_domain_b_n) begin
    if (!rst_domain_b_n)
      data_out_b <= 8'h00;
    else
      data_out_b <= data_in;
  end

endmodule

