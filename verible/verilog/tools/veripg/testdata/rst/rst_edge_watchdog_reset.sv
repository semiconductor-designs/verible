// Copyright 2025 The Verible Authors.
// Edge case: Watchdog timer reset

module rst_edge_watchdog_reset (
  input wire clk,
  input wire rst_n,
  input wire watchdog_kick,
  output logic watchdog_rst
);

  logic [7:0] watchdog_counter;
  
  // Watchdog generates reset if not kicked in time
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      watchdog_counter <= 8'h00;
      watchdog_rst <= 1'b0;
    end else if (watchdog_kick) begin
      watchdog_counter <= 8'h00;
      watchdog_rst <= 1'b0;
    end else if (watchdog_counter == 8'hFF) begin
      watchdog_rst <= 1'b1;  // Timeout - assert reset
    end else begin
      watchdog_counter <= watchdog_counter + 1'b1;
    end
  end

endmodule

