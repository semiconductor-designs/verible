// Copyright 2025 The Verible Authors.
// Edge case: Module with package imports

package config_pkg;
  parameter int FIFO_DEPTH = 16;
  parameter int DATA_WIDTH = 32;
  typedef struct packed {
    logic [DATA_WIDTH-1:0] data;
    logic valid;
  } data_packet_t;
endpackage

module str_edge_package_import (
  input wire clk,
  input wire rst_n,
  input config_pkg::data_packet_t packet_in,
  output config_pkg::data_packet_t packet_out
);

  import config_pkg::*;
  
  data_packet_t pipeline [FIFO_DEPTH-1:0];
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < FIFO_DEPTH; i++) begin
        pipeline[i] <= '0;
      end
      packet_out <= '0;
    end else begin
      pipeline[0] <= packet_in;
      for (int i = 1; i < FIFO_DEPTH; i++) begin
        pipeline[i] <= pipeline[i-1];
      end
      packet_out <= pipeline[FIFO_DEPTH-1];
    end
  end

endmodule

