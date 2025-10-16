// Copyright 2025 The Verible Authors.
// Edge case: Struct member naming

module edge_struct_member_names (
  input wire clk,
  input wire rst_n
);

  typedef struct packed {
    logic [7:0] header_type;
    logic [15:0] packet_length;
    logic [31:0] source_address;
    logic [31:0] destination_address;
    logic [7:0] protocol_id;
    logic valid_flag;
  } packet_header_t;
  
  packet_header_t current_packet;
  packet_header_t next_packet;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_packet <= '0;
    end else begin
      current_packet <= next_packet;
    end
  end

endmodule

