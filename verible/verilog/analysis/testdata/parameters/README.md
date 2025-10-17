# Parameter Tracking Test Data

This directory contains SystemVerilog test files for validating the ParameterTracker component.

## Directory Structure

### basic/
Basic parameter usage scenarios:
- `basic_param.sv` - Simple parameter declaration and usage
- `localparam.sv` - Local parameters (cannot be overridden)
- `multi_param.sv` - Multiple parameters in one module

### override/
Parameter override scenarios:
- `param_override.sv` - Parameter override in module instantiation
- `param_hier.sv` - Hierarchical parameter usage
- `param_default.sv` - Using default parameter values

### types/
Different parameter types and values:
- `param_types.sv` - Integer, string, real parameters
- `param_expr.sv` - Parameter expressions and calculations
- `param_range.sv` - Parameters used in bit ranges
- `param_array.sv` - Array parameters

### errors/
Error scenarios that should be detected:
- `param_error_type.sv` - Type mismatch in parameter override
- `param_error_missing.sv` - Missing required parameter
- `param_error_localparam.sv` - Attempt to override localparam

## Test Coverage

These tests cover:
- ✅ Parameter declaration extraction
- ✅ Parameter type detection
- ✅ Default value tracking
- ✅ Override detection in instantiation
- ✅ Hierarchical parameter propagation
- ✅ Error detection (type mismatches, invalid overrides)
- ✅ Localparam vs parameter distinction
- ✅ Expression evaluation in parameters

## Usage

Tests are used by `parameter-tracker_test.cc` to verify the ParameterTracker implementation.

