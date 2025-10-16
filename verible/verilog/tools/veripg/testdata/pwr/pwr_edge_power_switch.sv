// Copyright 2025 The Verible Authors.
// Edge case: Power switch cells

module power_switch_cell (
  input wire power_enable,
  output logic vdd_switched
);
  // Power switch: controls VDD to domain
  assign vdd_switched = power_enable;
endmodule

module pwr_edge_power_switch (
  input wire clk,
  input wire rst_n,
  input wire domain_power_enable,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  logic vdd_domain;
  
  // Power switch for switchable domain
  power_switch_cell u_pwr_switch (
    .power_enable(domain_power_enable),
    .vdd_switched(vdd_domain)
  );
  
  // Logic in switchable domain
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else if (vdd_domain)
      data_out <= data_in;
  end

endmodule

