// Test case for NAM_007: Inconsistent naming patterns
module nam_inconsistent_pattern_violation;
  // Inconsistent: mixing camelCase and snake_case
  logic dataBus;      // camelCase
  logic addr_bus;     // snake_case - inconsistent with dataBus
  logic control_sig;  // snake_case
  
  // Consistent pattern (all snake_case) would be better
endmodule

