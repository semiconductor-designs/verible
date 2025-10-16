// Copyright 2025 The Verible Authors.
// Edge case: Virtual interface (for UVM-style testbenches)

interface vif_example;
  logic [7:0] data;
  logic valid;
endinterface

module str_edge_virtual_interface (
  input wire clk,
  input wire rst_n,
  vif_example vif
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      vif.data <= 8'h00;
      vif.valid <= 1'b0;
    end else begin
      vif.data <= vif.data + 8'h01;
      vif.valid <= 1'b1;
    end
  end

endmodule

// Testbench with virtual interface
module testbench;
  logic clk, rst_n;
  vif_example vif_inst();
  
  str_edge_virtual_interface dut (
    .clk(clk),
    .rst_n(rst_n),
    .vif(vif_inst)
  );
  
  // Virtual interface handle for dynamic access
  virtual vif_example vif_handle;
  
  initial begin
    vif_handle = vif_inst;
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  initial begin
    rst_n = 0;
    #20 rst_n = 1;
    #100 $finish;
  end
endmodule

