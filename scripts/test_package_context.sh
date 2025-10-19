#!/bin/bash
# Feature 3 (v5.4.0): Package Context Mode Validation
# Tests --package-context flag with OpenTitan UVM files

set -e

OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
VERIBLE_SYNTAX="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"

echo "=========================================="
echo "Feature 3: Package Context Mode Validation"
echo "=========================================="
echo ""

# Test 1: Simple package context
echo "Test 1: Basic package context with macro..."
$VERIBLE_SYNTAX \
  --package_context="${OPENTITAN_ROOT}/hw/dv/sv/dv_base_reg/dv_base_reg_pkg.sv" \
  "${OPENTITAN_ROOT}/hw/dv/sv/dv_base_reg/dv_base_reg_block.sv" \
  2>&1 | head -3

if [ $? -eq 0 ]; then
  echo "✅ Test 1 PASSED"
else
  echo "❌ Test 1 FAILED"
fi
echo ""

# Test 2: cip_base_env_cfg with package context
echo "Test 2: cip_base_env_cfg with cip_lib package..."
$VERIBLE_SYNTAX \
  --package_context="${OPENTITAN_ROOT}/hw/dv/sv/cip_lib/cip_base_pkg.sv" \
  "${OPENTITAN_ROOT}/hw/dv/sv/cip_lib/cip_base_env_cfg.sv" \
  2>&1 | head -3

if [ $? -eq 0 ]; then
  echo "✅ Test 2 PASSED"
else
  echo "❌ Test 2 FAILED"
fi
echo ""

# Test 3: Multiple package context files
echo "Test 3: Multiple packages (dv_utils + cip_lib)..."
$VERIBLE_SYNTAX \
  --package_context="${OPENTITAN_ROOT}/hw/dv/sv/dv_utils/dv_utils_pkg.sv,${OPENTITAN_ROOT}/hw/dv/sv/cip_lib/cip_base_pkg.sv" \
  "${OPENTITAN_ROOT}/hw/dv/sv/cip_lib/cip_base_env.sv" \
  2>&1 | head -3

if [ $? -eq 0 ]; then
  echo "✅ Test 3 PASSED"
else
  echo "❌ Test 3 FAILED"
fi
echo ""

echo "=========================================="
echo "Package Context Validation Complete"
echo "=========================================="

