# VeriPG Integration

## Overview

Enhanced semantic validation for VeriPG workflows, providing deep type checking and structure validation beyond standard linting.

## Features

- **Type Validation** - Deep semantic type checking
- **Naming Conventions** - VeriPG-specific naming rules
- **Module Structure** - Architectural validation
- **Enhanced Error Messages** - Detailed diagnostics

## Integration

The VeriPGValidator is integrated into Verible's existing tools and provides VeriPG-specific checks.

## Usage

```cpp
#include "verible/verilog/tools/veripg/veripg-validator.h"

VeriPGValidator validator(type_checker);
auto result = validator.Validate(symbol_table);

if (result.passed) {
  std::cout << "Validation passed!\n";
} else {
  for (const auto& error : result.error_messages) {
    std::cout << "Error: " << error << "\n";
  }
}
```

## Development Status

**Version:** 0.1.0  
**Test Coverage:** 15/15 tests passing

Framework complete. Full validation rules in development.

## See Also

- [Type Checker](../../analysis/type-checker.h)
- [Symbol Table](../../analysis/symbol-table.h)

