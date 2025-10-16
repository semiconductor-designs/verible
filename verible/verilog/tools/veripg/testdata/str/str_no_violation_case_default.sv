// Copyright 2025 The Verible Authors.
// Negative test: Case statements with default - NO violation

module str_no_violation_case_default (
  input wire clk,
  input wire rst_n,
  input wire [2:0] state,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'h00;
    end else begin
      // Case statement with default clause
      case (state)
        3'b000: data_out <= data_in;
        3'b001: data_out <= data_in + 8'h01;
        3'b010: data_out <= data_in + 8'h02;
        3'b011: data_out <= data_in + 8'h04;
        3'b100: data_out <= data_in + 8'h08;
        default: data_out <= 8'hFF;  // Good: default case present
      endcase
    end
  end

endmodule

