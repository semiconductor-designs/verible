// Copyright 2025 The Verible Authors.
// Edge case: Bind directive for assertions

module dut (
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

module assertions (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  input wire [7:0] data_out
);
  // Assertion: data_out should follow data_in after one cycle
  property p_data_follows;
    @(posedge clk) disable iff (!rst_n)
    ##1 (data_out == $past(data_in));
  endproperty
  
  assert property (p_data_follows);
endmodule

module str_edge_bind_directive (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  dut u_dut (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in),
    .data_out(data_out)
  );
  
  // Bind assertions to DUT
  bind dut assertions u_assertions (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in),
    .data_out(data_out)
  );

endmodule

