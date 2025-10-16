// Copyright 2025 The Verible Authors.
// Edge case: Mixed but documented conventions (acceptable with comments)

module edge_mixed_conventions (
  // Standard interface signals (lowercase_with_underscores)
  input wire clk_sys,
  input wire rst_n,
  
  // AXI-style naming (industry standard)
  input wire AWVALID,
  input wire AWREADY,
  input wire [31:0] AWADDR,
  input wire WVALID,
  input wire WREADY,
  input wire [31:0] WDATA,
  
  // Legacy interface (documented compatibility)
  input wire CS_N,      // Chip Select (active-low)
  input wire WR_N,      // Write Enable (active-low)
  input wire RD_N,      // Read Enable (active-low)
  
  // Modern SystemVerilog style
  output logic transaction_complete,
  output logic error_detected
);

  // Internal signals follow project convention
  logic state_machine_active;
  logic data_buffer_valid;
  
  always_ff @(posedge clk_sys or negedge rst_n) begin
    if (!rst_n) begin
      transaction_complete <= 1'b0;
      error_detected <= 1'b0;
    end
  end

endmodule

