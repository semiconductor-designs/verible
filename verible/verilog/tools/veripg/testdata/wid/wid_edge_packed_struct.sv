// Copyright 2025 The Verible Authors.
// Edge case: Packed struct width calculations

module wid_edge_packed_struct (
  input wire clk,
  input wire rst_n
);

  typedef struct packed {
    logic [7:0] header;
    logic [15:0] payload;
    logic [3:0] checksum;
  } packet_t;  // Total: 8+16+4 = 28 bits
  
  packet_t tx_packet;
  logic [27:0] raw_data;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_packet <= '0;
      raw_data <= '0;
    end else begin
      // Packed struct has defined width
      raw_data <= tx_packet;  // 28-bit = 28-bit
    end
  end

endmodule

