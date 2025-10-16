// Test file for STR_003: Deep hierarchy (>5 levels of instantiation)

module level_6(input wire a, output wire b);
  assign b = a;
endmodule

module level_5(input wire a, output wire b);
  level_6 u6(.a(a), .b(b));
endmodule

module level_4(input wire a, output wire b);
  level_5 u5(.a(a), .b(b));
endmodule

module level_3(input wire a, output wire b);
  level_4 u4(.a(a), .b(b));
endmodule

module level_2(input wire a, output wire b);
  level_3 u3(.a(a), .b(b));
endmodule

module level_1(input wire a, output wire b);
  level_2 u2(.a(a), .b(b));
endmodule

module str_deep_hierarchy(input wire a, output wire b);
  // Violation: 6 levels deep (this -> level_1 -> level_2 -> level_3 -> level_4 -> level_5 -> level_6)
  level_1 u1(.a(a), .b(b));
endmodule

