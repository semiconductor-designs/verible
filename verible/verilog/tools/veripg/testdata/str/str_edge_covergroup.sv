// Copyright 2025 The Verible Authors.
// Edge case: Covergroup for functional coverage

module str_edge_covergroup (
  input wire clk,
  input wire rst_n,
  input wire [2:0] state,
  input wire [7:0] data,
  output logic [7:0] result
);

  // Covergroup for functional coverage
  covergroup cg_state @(posedge clk);
    state_cp: coverpoint state {
      bins idle = {3'b000};
      bins active = {3'b001, 3'b010, 3'b011};
      bins error = {3'b111};
      bins transitions = (3'b000 => 3'b001), (3'b001 => 3'b010);
    }
    
    data_cp: coverpoint data {
      bins low = {[0:63]};
      bins mid = {[64:191]};
      bins high = {[192:255]};
    }
    
    cross_cp: cross state_cp, data_cp {
      ignore_bins invalid = binsof(state_cp.error);
    }
  endgroup
  
  cg_state cg_inst;
  
  initial begin
    cg_inst = new();
  end
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      result <= 8'h00;
    end else begin
      result <= data;
      cg_inst.sample();
    end
  end

endmodule

