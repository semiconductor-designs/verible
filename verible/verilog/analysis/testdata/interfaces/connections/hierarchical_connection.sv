// Hierarchical interface connections
interface ctrl_intf;
  logic enable;
  logic [3:0] mode;
endinterface

module leaf_module(ctrl_intf ctrl);
  always_comb begin
    if (ctrl.enable) begin
      // Process based on mode
    end
  end
endmodule

module middle_module(ctrl_intf ctrl);
  leaf_module leaf(.ctrl(ctrl));
endmodule

module top;
  ctrl_intf control();
  
  middle_module mid(.ctrl(control));
  
  initial begin
    control.enable = 1'b1;
    control.mode = 4'b0001;
  end
endmodule

