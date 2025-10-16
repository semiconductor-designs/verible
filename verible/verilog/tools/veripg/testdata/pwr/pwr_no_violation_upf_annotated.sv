// Copyright 2025 The Verible Authors.
// Negative test: Proper UPF annotations - NO violation

// UPF annotations (comments for demonstration)
// set_design_top top_module
// create_power_domain PD_CORE -elements {core_logic}
// create_power_domain PD_PERIPHERAL -elements {peripheral_block}

module pwr_no_violation_upf_annotated (
  input wire clk_core,
  input wire clk_peripheral,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] core_output,
  output logic [7:0] peripheral_output
);

  // Power domain: PD_CORE
  logic [7:0] core_logic;
  
  always_ff @(posedge clk_core or negedge rst_n) begin
    if (!rst_n)
      core_logic <= 8'h00;
    else
      core_logic <= data_in;
  end
  
  assign core_output = core_logic;
  
  // Power domain: PD_PERIPHERAL
  logic [7:0] peripheral_block;
  
  always_ff @(posedge clk_peripheral or negedge rst_n) begin
    if (!rst_n)
      peripheral_block <= 8'h00;
    else
      peripheral_block <= data_in;
  end
  
  assign peripheral_output = peripheral_block;

endmodule

