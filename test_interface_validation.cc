// Quick test to verify interface validation is working
#include <iostream>
#include "verible/verilog/analysis/interface-validator.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/symbol-table.h"

int main() {
  // Test code with missing modport error
  const char* code = R"(
interface test_intf;
  logic data;
  modport existing (input data);
endinterface

module user(test_intf.nonexistent intf);
  logic local;
  always_comb begin
    local = intf.data;
  end
endmodule
)";

  // Parse the code
  verilog::VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  if (!status.ok()) {
    std::cerr << "Parse error: " << status.message() << std::endl;
    return 1;
  }

  // Build symbol table
  verilog::SymbolTable symbol_table(nullptr);
  symbol_table.Build(analyzer.Data().SyntaxTree().get());

  // Create validator
  verilog::analysis::InterfaceValidator validator(&symbol_table);
  
  // Validate
  auto result = validator.ValidateAllInterfaces();
  
  // Check results
  const auto& errors = validator.GetErrors();
  std::cout << "Found " << errors.size() << " errors:" << std::endl;
  for (const auto& error : errors) {
    std::cout << "  - " << error << std::endl;
  }
  
  if (errors.empty()) {
    std::cout << "ERROR: Expected validation errors but got none!" << std::endl;
    return 1;
  }
  
  std::cout << "SUCCESS: Validation is working!" << std::endl;
  return 0;
}

