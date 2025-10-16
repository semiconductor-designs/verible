// Copyright 2025 The Verible Authors.
// Edge case: DVFS (Dynamic Voltage and Frequency Scaling)

module pwr_edge_dvfs (
  input wire clk_variable,  // Frequency can change
  input wire rst_n,
  input wire [1:0] performance_mode,  // 00=low, 01=med, 10=high, 11=turbo
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // DVFS: Voltage and frequency scaled based on performance mode
  // Voltage controller adjusts VDD externally
  // Clock frequency adjusted by PLL/clock controller
  
  logic [7:0] processing_buffer;
  
  always_ff @(posedge clk_variable or negedge rst_n) begin
    if (!rst_n) begin
      processing_buffer <= 8'h00;
      data_out <= 8'h00;
    end else begin
      // Processing adapts to current frequency/voltage
      case (performance_mode)
        2'b00: processing_buffer <= data_in;           // Low power
        2'b01: processing_buffer <= data_in + 8'h01;   // Medium
        2'b10: processing_buffer <= data_in + 8'h02;   // High
        2'b11: processing_buffer <= data_in + 8'h04;   // Turbo
      endcase
      data_out <= processing_buffer;
    end
  end

endmodule

