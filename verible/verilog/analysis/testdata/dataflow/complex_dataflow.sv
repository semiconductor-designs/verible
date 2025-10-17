// Complex real-world data flow scenario
module complex_dataflow (
  input  logic clk,
  input  logic rst_n,
  input  logic [7:0] data_in,
  input  logic enable,
  input  logic select,
  output logic [7:0] data_out,
  output logic valid
);
  
  // Multiple signals with complex dependencies
  logic [7:0] stage1, stage2, stage3;
  logic stage1_valid, stage2_valid;
  
  // Stage 1: Input processing
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      stage1 <= 8'h00;
      stage1_valid <= 1'b0;
    end else if (enable) begin
      stage1 <= data_in;
      stage1_valid <= 1'b1;
    end
  end
  
  // Stage 2: Processing
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      stage2 <= 8'h00;
      stage2_valid <= 1'b0;
    end else if (stage1_valid) begin
      stage2 <= stage1 ^ 8'hAA;
      stage2_valid <= 1'b1;
    end
  end
  
  // Stage 3: Conditional output
  always_comb begin
    if (select)
      stage3 = stage2 & 8'h0F;
    else
      stage3 = stage2 | 8'hF0;
  end
  
  // Output assignment
  assign data_out = stage3;
  assign valid = stage2_valid;
  
  // Dependencies:
  // data_out depends on: data_in, enable, stage1, stage1_valid, stage2, select
  // valid depends on: stage1_valid, rst_n, clk
  
endmodule

