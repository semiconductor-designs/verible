#!/bin/bash
# Quick OpenTitan validation with progress monitoring
# Tests the 14 previously failing files to verify deep nesting fix

set -e

OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
VERIBLE_PARSER="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"

# The 14 files that were failing due to deep nesting / macro issues
FAILING_FILES=(
  "hw/dv/sv/cip_lib/cip_base_env_cfg.sv"
  "hw/dv/sv/csr_utils/csr_excl_item.sv"
  "hw/ip/aes/dv/env/aes_env_cfg.sv"
  "hw/ip/csrng/dv/env/csrng_env_cfg.sv"
  "hw/ip/entropy_src/dv/env/entropy_src_env_cfg.sv"
  "hw/ip/hmac/dv/env/hmac_env_cfg.sv"
  "hw/ip/keymgr/dv/env/keymgr_env_cfg.sv"
  "hw/ip/kmac/dv/env/kmac_app_agent/kmac_app_host_driver.sv"
  "hw/ip/kmac/dv/env/kmac_env_cfg.sv"
  "hw/ip/otbn/dv/uvm/env/otbn_env_cfg.sv"
  "hw/ip/otp_ctrl/dv/env/otp_ctrl_env_cfg.sv"
  "hw/ip/pwrmgr/dv/env/pwrmgr_env_cfg.sv"
  "hw/ip/rv_dm/dv/env/rv_dm_env_cfg.sv"
  "hw/ip/spi_device/dv/env/spi_device_env_cfg.sv"
)

TOTAL=${#FAILING_FILES[@]}
PASS=0
FAIL=0

# Include paths for OpenTitan + UVM
# Note: We need to add the directories containing dv_macros.svh and cip_macros.svh
UVM_PATH="$(pwd)/third_party/uvm/src"
INCLUDE_PATHS="${UVM_PATH},${OPENTITAN_ROOT}/hw/dv/sv/dv_utils,${OPENTITAN_ROOT}/hw/dv/sv/cip_lib,${OPENTITAN_ROOT}/hw/dv/sv"

echo "=========================================="
echo "OpenTitan Quick Validation"
echo "Testing 14 Previously Failing Files"
echo "=========================================="
echo ""

for i in "${!FAILING_FILES[@]}"; do
  FILE="${OPENTITAN_ROOT}/${FAILING_FILES[$i]}"
  NUM=$((i + 1))
  
  printf "[%2d/%2d] %s\n" "$NUM" "$TOTAL" "${FAILING_FILES[$i]}"
  
  # Test with preprocessing and include paths
  if "${VERIBLE_PARSER}" \
      --preprocess=true \
      --include_paths="${INCLUDE_PATHS}" \
      "$FILE" >/dev/null 2>&1; then
    echo "        ✅ PASS"
    ((PASS++))
  else
    # Show error
    ERROR=$("${VERIBLE_PARSER}" \
      --preprocess=true \
      --include_paths="${INCLUDE_PATHS}" \
      "$FILE" 2>&1 | head -3)
    echo "        ❌ FAIL"
    echo "        Error: ${ERROR}"
    ((FAIL++))
  fi
  echo ""
done

echo "=========================================="
echo "RESULTS"
echo "=========================================="
echo "Total:   ${TOTAL}"
echo "Passed:  ${PASS}"
echo "Failed:  ${FAIL}"
echo "Rate:    $(awk "BEGIN {printf \"%.1f%%\", ($PASS/$TOTAL)*100}")"
echo "=========================================="

if [ "$PASS" -eq "$TOTAL" ]; then
  echo "🎉 SUCCESS: 100% of previously failing files now pass!"
  exit 0
else
  echo "⚠️  Some files still failing"
  exit 1
fi

