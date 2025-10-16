// Copyright 2025 The Verible Authors.
// Edge case: Substrate/body biasing for power optimization

module pwr_edge_substrate_biasing (
  input wire clk,
  input wire rst_n,
  input wire [1:0] bias_mode,  // 00=none, 01=FBB, 10=RBB, 11=adaptive
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Body biasing control (external voltage control)
  // FBB (Forward Body Bias): Increases speed, increases leakage
  // RBB (Reverse Body Bias): Reduces leakage, reduces speed
  
  logic [7:0] processing_stage;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      processing_stage <= 8'h00;
      data_out <= 8'h00;
    end else begin
      // Processing assumes body bias is managed externally
      processing_stage <= data_in ^ 8'hAA;
      data_out <= processing_stage;
    end
  end
  
  // Body bias mode is typically controlled by external voltage regulators
  // This is a power management technique at transistor level

endmodule

