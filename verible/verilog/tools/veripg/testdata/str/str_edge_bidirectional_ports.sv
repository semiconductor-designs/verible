// Copyright 2025 The Verible Authors.
// Edge case: Bidirectional (inout) ports

module str_edge_bidirectional_ports (
  input wire clk,
  input wire rst_n,
  input wire oe,  // Output enable
  inout wire [7:0] data_bus,  // Bidirectional bus
  output logic [7:0] data_captured
);

  logic [7:0] data_to_drive;
  
  // Drive bus when output enable is high
  assign data_bus = oe ? data_to_drive : 8'hZZ;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_to_drive <= 8'h00;
      data_captured <= 8'h00;
    end else begin
      if (oe) begin
        data_to_drive <= data_to_drive + 8'h01;
      end else begin
        data_captured <= data_bus;
      end
    end
  end

endmodule

