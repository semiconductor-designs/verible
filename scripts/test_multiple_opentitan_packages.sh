#!/bin/bash
# Test package context with multiple OpenTitan packages
# Risk Assessment P0 Item #1

set -e

OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
VERIBLE_SYNTAX="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
UVM_PATH="$(pwd)/third_party/uvm/src"

# Comprehensive include paths
INCLUDE_PATHS="${UVM_PATH}"
INCLUDE_PATHS="${INCLUDE_PATHS},${OPENTITAN_ROOT}/hw/dv/sv"
INCLUDE_PATHS="${INCLUDE_PATHS},${OPENTITAN_ROOT}/hw/dv/sv/dv_utils"
INCLUDE_PATHS="${INCLUDE_PATHS},${OPENTITAN_ROOT}/hw/dv/sv/cip_lib"
INCLUDE_PATHS="${INCLUDE_PATHS},${OPENTITAN_ROOT}/hw/dv/sv/dv_base_reg"
INCLUDE_PATHS="${INCLUDE_PATHS},${OPENTITAN_ROOT}/hw/dv/sv/csr_utils"

echo "================================================================"
echo "Testing Package Context with Multiple OpenTitan Packages"
echo "================================================================"
echo ""

PASS=0
FAIL=0

# Test 1: dv_base_reg_pkg
echo "Test 1: dv_base_reg_pkg.sv"
OUTPUT=$($VERIBLE_SYNTAX \
  --include_paths="$INCLUDE_PATHS" \
  --package_context="${OPENTITAN_ROOT}/hw/dv/sv/dv_base_reg/dv_base_reg_pkg.sv" \
  "${OPENTITAN_ROOT}/hw/dv/sv/dv_base_reg/dv_base_reg_block.sv" \
  2>&1 | grep "Loaded package context" || echo "FAILED")
echo "  Result: $OUTPUT"
if [[ "$OUTPUT" == *"macro"* ]]; then ((PASS++)); else ((FAIL++)); fi
echo ""

# Test 2: dv_utils_pkg
echo "Test 2: dv_utils_pkg.sv"
OUTPUT=$($VERIBLE_SYNTAX \
  --include_paths="$INCLUDE_PATHS" \
  --package_context="${OPENTITAN_ROOT}/hw/dv/sv/dv_utils/dv_utils_pkg.sv" \
  "${OPENTITAN_ROOT}/hw/dv/sv/dv_utils/dv_utils_pkg.sv" \
  2>&1 | grep "Loaded package context" || echo "FAILED")
echo "  Result: $OUTPUT"
if [[ "$OUTPUT" == *"macro"* ]]; then ((PASS++)); else ((FAIL++)); fi
echo ""

# Test 3: csr_utils_pkg
echo "Test 3: csr_utils_pkg.sv"
OUTPUT=$($VERIBLE_SYNTAX \
  --include_paths="$INCLUDE_PATHS" \
  --package_context="${OPENTITAN_ROOT}/hw/dv/sv/csr_utils/csr_utils_pkg.sv" \
  "${OPENTITAN_ROOT}/hw/dv/sv/csr_utils/csr_utils_pkg.sv" \
  2>&1 | grep "Loaded package context" || echo "FAILED")
echo "  Result: $OUTPUT"
if [[ "$OUTPUT" == *"macro"* ]]; then ((PASS++)); else ((FAIL++)); fi
echo ""

# Test 4: Multiple packages combined
echo "Test 4: dv_utils + csr_utils (multiple packages)"
OUTPUT=$($VERIBLE_SYNTAX \
  --include_paths="$INCLUDE_PATHS" \
  --package_context="${OPENTITAN_ROOT}/hw/dv/sv/dv_utils/dv_utils_pkg.sv,${OPENTITAN_ROOT}/hw/dv/sv/csr_utils/csr_utils_pkg.sv" \
  "${OPENTITAN_ROOT}/hw/dv/sv/csr_utils/csr_utils_pkg.sv" \
  2>&1 | grep "Loaded package context" || echo "FAILED")
echo "  Result: $OUTPUT"
if [[ "$OUTPUT" == *"macro"* ]]; then ((PASS++)); else ((FAIL++)); fi
echo ""

# Test 5: mem_bkdr_if package
if [ -f "${OPENTITAN_ROOT}/hw/dv/sv/mem_bkdr_if/mem_bkdr_if_pkg.sv" ]; then
  echo "Test 5: mem_bkdr_if_pkg.sv"
  OUTPUT=$($VERIBLE_SYNTAX \
    --include_paths="$INCLUDE_PATHS" \
    --package_context="${OPENTITAN_ROOT}/hw/dv/sv/mem_bkdr_if/mem_bkdr_if_pkg.sv" \
    "${OPENTITAN_ROOT}/hw/dv/sv/mem_bkdr_if/mem_bkdr_if_pkg.sv" \
    2>&1 | grep "Loaded package context" || echo "FAILED")
  echo "  Result: $OUTPUT"
  if [[ "$OUTPUT" == *"macro"* ]]; then ((PASS++)); else ((FAIL++)); fi
  echo ""
fi

# Test 6: dv_lib package
if [ -f "${OPENTITAN_ROOT}/hw/dv/sv/dv_lib/dv_lib_pkg.sv" ]; then
  echo "Test 6: dv_lib_pkg.sv"
  OUTPUT=$($VERIBLE_SYNTAX \
    --include_paths="$INCLUDE_PATHS" \
    --package_context="${OPENTITAN_ROOT}/hw/dv/sv/dv_lib/dv_lib_pkg.sv" \
    "${OPENTITAN_ROOT}/hw/dv/sv/dv_lib/dv_lib_pkg.sv" \
    2>&1 | grep "Loaded package context" || echo "FAILED")
  echo "  Result: $OUTPUT"
  if [[ "$OUTPUT" == *"macro"* ]]; then ((PASS++)); else ((FAIL++)); fi
  echo ""
fi

echo "================================================================"
echo "Results: $PASS passed, $FAIL failed"
echo "================================================================"

if [ $FAIL -eq 0 ]; then
  echo "✅ All packages tested successfully!"
  exit 0
else
  echo "⚠️  Some packages had issues"
  exit 1
fi

