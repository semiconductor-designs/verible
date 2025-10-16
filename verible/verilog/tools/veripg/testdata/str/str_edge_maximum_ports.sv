// Copyright 2025 The Verible Authors.
// Edge case: Module with many ports (stress test)

module str_edge_maximum_ports (
  // Clocks
  input wire clk0, clk1, clk2, clk3,
  // Resets
  input wire rst0_n, rst1_n, rst2_n, rst3_n,
  // Data inputs (32 ports)
  input wire [7:0] din0, din1, din2, din3, din4, din5, din6, din7,
  input wire [7:0] din8, din9, din10, din11, din12, din13, din14, din15,
  input wire [7:0] din16, din17, din18, din19, din20, din21, din22, din23,
  input wire [7:0] din24, din25, din26, din27, din28, din29, din30, din31,
  // Control signals
  input wire en0, en1, en2, en3, en4, en5, en6, en7,
  input wire sel0, sel1, sel2, sel3, sel4, sel5, sel6, sel7,
  // Data outputs (32 ports)
  output logic [7:0] dout0, dout1, dout2, dout3, dout4, dout5, dout6, dout7,
  output logic [7:0] dout8, dout9, dout10, dout11, dout12, dout13, dout14, dout15,
  output logic [7:0] dout16, dout17, dout18, dout19, dout20, dout21, dout22, dout23,
  output logic [7:0] dout24, dout25, dout26, dout27, dout28, dout29, dout30, dout31,
  // Status signals
  output logic err0, err1, err2, err3, ready0, ready1, ready2, ready3
);

  // Simple pass-through logic
  always_ff @(posedge clk0 or negedge rst0_n) begin
    if (!rst0_n) {dout0, dout1, dout2, dout3} <= '0;
    else {dout0, dout1, dout2, dout3} <= {din0, din1, din2, din3};
  end
  
  always_ff @(posedge clk1 or negedge rst1_n) begin
    if (!rst1_n) {dout4, dout5, dout6, dout7} <= '0;
    else {dout4, dout5, dout6, dout7} <= {din4, din5, din6, din7};
  end
  
  always_ff @(posedge clk2 or negedge rst2_n) begin
    if (!rst2_n) {dout8, dout9, dout10, dout11} <= '0;
    else {dout8, dout9, dout10, dout11} <= {din8, din9, din10, din11};
  end
  
  always_ff @(posedge clk3 or negedge rst3_n) begin
    if (!rst3_n) {dout12, dout13, dout14, dout15} <= '0;
    else {dout12, dout13, dout14, dout15} <= {din12, din13, din14, din15};
  end
  
  assign {dout16, dout17, dout18, dout19} = {din16, din17, din18, din19};
  assign {dout20, dout21, dout22, dout23} = {din20, din21, din22, din23};
  assign {dout24, dout25, dout26, dout27} = {din24, din25, din26, din27};
  assign {dout28, dout29, dout30, dout31} = {din28, din29, din30, din31};
  
  assign {err0, err1, err2, err3} = {en0, en1, en2, en3};
  assign {ready0, ready1, ready2, ready3} = {sel0, sel1, sel2, sel3};

endmodule

