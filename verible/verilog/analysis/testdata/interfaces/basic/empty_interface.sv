// Empty interface (edge case)
interface empty_intf;
  // No signals
endinterface

module test_empty(empty_intf intf);
  // Module using empty interface
endmodule

module top;
  empty_intf empty();
  test_empty te(.intf(empty));
endmodule

