# Port Connection Test Data

This directory contains SystemVerilog test files for port connection validation testing.

## Directory Structure

- `basic/` - Simple port connection tests
- `direction/` - Port direction validation tests
- `type/` - Port type compatibility tests
- `width/` - Port width matching tests
- `advanced/` - Complex scenarios (arrays, parameters, expressions)

## Test Coverage

### Basic Port Tests (basic/)
- Simple input/output/inout ports
- Empty modules
- Single-port modules

### Port Direction Tests (direction/)
- Input-to-output connections (valid)
- Output-to-input connections (valid)
- Input-to-input connections (invalid)
- Output-to-output connections (invalid)
- Inout port connections

### Port Type Tests (type/)
- Matching types (logic to logic)
- Type mismatches (logic to reg)
- Wire to logic conversions
- Struct port connections
- Enum port connections

### Port Width Tests (width/)
- Matching widths [7:0] to [7:0]
- Width mismatches [7:0] to [3:0]
- Implicit vs explicit widths
- Parameter-based widths

### Advanced Tests (advanced/)
- Packed array ports
- Unpacked array ports
- Multi-dimensional arrays
- Port expressions (concatenations, replications)
- Part-selects
- Named vs positional connections

## Usage

These test files are used by `port-connection-validator_test.cc` to validate
the PortConnectionValidator implementation.

Each test file is designed to test specific aspects of port connection
validation, with clear examples of both valid and invalid connections.

