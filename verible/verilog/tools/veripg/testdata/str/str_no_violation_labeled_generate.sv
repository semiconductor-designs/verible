// Copyright 2025 The Verible Authors.
// Negative test: Labeled generate blocks - NO violation

module str_no_violation_labeled_generate (
  input wire clk,
  input wire rst_n,
  input wire [31:0] data_in,
  output logic [31:0] data_out
);

  logic [31:0] pipeline [3:0];
  
  // Labeled generate block (good practice)
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_pipeline_stages
      if (i == 0) begin : gen_first_stage
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n) pipeline[i] <= 32'h0;
          else pipeline[i] <= data_in;
        end
      end else begin : gen_other_stages
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n) pipeline[i] <= 32'h0;
          else pipeline[i] <= pipeline[i-1];
        end
      end
    end
  endgenerate
  
  assign data_out = pipeline[3];

endmodule

