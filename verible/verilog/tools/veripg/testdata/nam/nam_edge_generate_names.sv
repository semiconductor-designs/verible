// Copyright 2025 The Verible Authors.
// Edge case: Generated block names

module edge_generate_names #(
  parameter int NUM_CHANNELS = 4
)(
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in [NUM_CHANNELS-1:0],
  output logic [7:0] data_out [NUM_CHANNELS-1:0]
);

  // Generate blocks with proper labels
  genvar i;
  generate
    for (i = 0; i < NUM_CHANNELS; i++) begin : gen_channel_pipeline
      logic [7:0] stage1_data;
      logic [7:0] stage2_data;
      
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          stage1_data <= 8'h00;
          stage2_data <= 8'h00;
          data_out[i] <= 8'h00;
        end else begin
          stage1_data <= data_in[i];
          stage2_data <= stage1_data;
          data_out[i] <= stage2_data;
        end
      end
    end
  endgenerate

endmodule

