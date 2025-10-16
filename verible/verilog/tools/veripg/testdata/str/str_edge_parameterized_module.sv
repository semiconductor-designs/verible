// Copyright 2025 The Verible Authors.
// Edge case: Heavily parameterized module

module str_edge_parameterized_module #(
  parameter int DATA_WIDTH = 32,
  parameter int ADDR_WIDTH = 16,
  parameter int DEPTH = 1024,
  parameter int PIPELINE_STAGES = 4,
  parameter bit USE_RESET = 1,
  parameter bit USE_OUTPUT_REG = 1,
  parameter string MODE = "NORMAL"
) (
  input wire clk,
  input wire rst_n,
  input wire [DATA_WIDTH-1:0] data_in,
  input wire [ADDR_WIDTH-1:0] addr,
  input wire write_enable,
  output logic [DATA_WIDTH-1:0] data_out
);

  logic [DATA_WIDTH-1:0] memory [DEPTH-1:0];
  logic [DATA_WIDTH-1:0] pipeline [PIPELINE_STAGES-1:0];
  
  generate
    if (USE_RESET) begin : gen_with_reset
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          for (int i = 0; i < PIPELINE_STAGES; i++) pipeline[i] <= '0;
        end else begin
          pipeline[0] <= memory[addr];
          for (int i = 1; i < PIPELINE_STAGES; i++) pipeline[i] <= pipeline[i-1];
        end
      end
    end else begin : gen_no_reset
      always_ff @(posedge clk) begin
        pipeline[0] <= memory[addr];
        for (int i = 1; i < PIPELINE_STAGES; i++) pipeline[i] <= pipeline[i-1];
      end
    end
    
    if (USE_OUTPUT_REG) begin : gen_output_reg
      always_ff @(posedge clk) data_out <= pipeline[PIPELINE_STAGES-1];
    end else begin : gen_output_comb
      assign data_out = pipeline[PIPELINE_STAGES-1];
    end
  endgenerate
  
  always_ff @(posedge clk) begin
    if (write_enable) memory[addr] <= data_in;
  end

endmodule

