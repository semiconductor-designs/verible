// Test case for NAM_003: Parameter naming (should be UPPER_CASE)
module nam_parameter_naming_violation;
  parameter width = 8;        // NAM_003: Should be WIDTH (UPPER_CASE)
  parameter DataWidth = 16;   // NAM_003: Should be DATA_WIDTH
  
  parameter ADDR_WIDTH = 32;  // OK: UPPER_CASE with underscores
  parameter MAX_COUNT = 100;  // OK
endmodule

