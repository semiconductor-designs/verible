// Copyright 2025 The Verible Authors.
// Edge case: Union width (max of members)

module wid_edge_union_width (
  input wire clk,
  input wire rst_n,
  input wire sel
);

  typedef union packed {
    logic [31:0] word;
    logic [15:0] half [2];
    logic [7:0] byte [4];
  } data_union_t;  // Width = max(32, 32, 32) = 32 bits
  
  data_union_t data_reg;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_reg.word <= 32'h0;
    end else if (sel) begin
      data_reg.word <= 32'hDEADBEEF;
    end else begin
      data_reg.byte[0] <= 8'hAA;
      data_reg.byte[1] <= 8'hBB;
    end
  end

endmodule

