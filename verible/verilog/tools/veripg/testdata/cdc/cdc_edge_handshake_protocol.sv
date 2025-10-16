// Copyright 2025 The Verible Authors.
// Edge case: REQ/ACK handshake CDC protocol

module cdc_edge_handshake_protocol (
  input wire clk_src,
  input wire clk_dst,
  input wire rst_n,
  input wire req_in,
  output logic ack_out,
  output logic data_valid
);

  // Source domain: Toggle-based request
  logic req_toggle;
  always_ff @(posedge clk_src or negedge rst_n) begin
    if (!rst_n) req_toggle <= 1'b0;
    else if (req_in) req_toggle <= ~req_toggle;
  end
  
  // Destination domain: Synchronize toggle signal
  logic req_sync1, req_sync2, req_sync3;
  always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) begin
      req_sync1 <= 1'b0;
      req_sync2 <= 1'b0;
      req_sync3 <= 1'b0;
    end else begin
      req_sync1 <= req_toggle;
      req_sync2 <= req_sync1;
      req_sync3 <= req_sync2;
    end
  end
  
  // Edge detection for handshake
  assign data_valid = req_sync2 ^ req_sync3;
  
  // Synchronize acknowledgment back
  logic ack_toggle;
  always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) ack_toggle <= 1'b0;
    else if (data_valid) ack_toggle <= ~ack_toggle;
  end
  
  logic ack_sync1, ack_sync2;
  always_ff @(posedge clk_src or negedge rst_n) begin
    if (!rst_n) begin
      ack_sync1 <= 1'b0;
      ack_sync2 <= 1'b0;
    end else begin
      ack_sync1 <= ack_toggle;
      ack_sync2 <= ack_sync1;
    end
  end
  
  assign ack_out = ack_sync2;

endmodule

