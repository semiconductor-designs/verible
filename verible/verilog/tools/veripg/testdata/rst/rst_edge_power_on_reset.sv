// Copyright 2025 The Verible Authors.
// Edge case: Power-on reset (POR) - special reset type

module rst_edge_power_on_reset (
  input wire clk,
  input wire por_n,  // Power-On Reset
  input wire [7:0] data_in,
  output logic [7:0] data_out,
  output logic system_ready
);

  logic [3:0] por_counter;
  
  // POR deasserts after a delay
  always_ff @(posedge clk or negedge por_n) begin
    if (!por_n) begin
      por_counter <= 4'h0;
      system_ready <= 1'b0;
      data_out <= 8'h00;
    end else begin
      if (por_counter < 4'hF) begin
        por_counter <= por_counter + 1'b1;
      end else begin
        system_ready <= 1'b1;
        data_out <= data_in;
      end
    end
  end

endmodule

