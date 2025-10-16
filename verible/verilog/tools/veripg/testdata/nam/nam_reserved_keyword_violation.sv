// Test case for NAM_006: Reserved keyword usage (SystemVerilog keywords)
module nam_reserved_keyword_violation;
  // NAM_006: Using 'always' as signal name (reserved keyword)
  // Note: This won't parse, but we test the warning mechanism
  
  // Instead test similar names that are discouraged
  logic task_signal;    // NAM_006: Contains reserved word 'task'
  logic module_id;      // NAM_006: Contains reserved word 'module'
  
  logic user_data;      // OK: no reserved keywords
endmodule

