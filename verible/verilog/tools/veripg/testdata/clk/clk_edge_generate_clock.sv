// Copyright 2025 The Verible Authors.
// Edge case: Generated clock from logic (documented special case)

module clk_edge_generate_clock (
  input wire clk_ref,
  input wire rst_n,
  input wire enable,
  output logic clk_generated
);

  // Generated clock: derived from reference clock
  // Special case that should be documented and analyzed carefully
  // Used in clock generation circuits
  
  logic [3:0] counter;
  
  always_ff @(posedge clk_ref or negedge rst_n) begin
    if (!rst_n) begin
      counter <= 4'h0;
      clk_generated <= 1'b0;
    end else if (enable) begin
      if (counter == 4'h3) begin
        clk_generated <= ~clk_generated;  // Toggle every 4 cycles
        counter <= 4'h0;
      end else begin
        counter <= counter + 1'b1;
      end
    end
  end

endmodule

