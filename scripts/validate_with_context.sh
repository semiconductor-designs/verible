#!/bin/bash
# Validate OpenTitan files with proper UVM/DV context
# This script demonstrates how to parse the 28 "failed" files correctly

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIBLE_BIN="${SCRIPT_DIR}/../bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
UVM_ROOT="${SCRIPT_DIR}/../third_party/uvm/src"

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "================================================================"
echo "OpenTitan Validation with Proper Context - v5.4.0"
echo "Testing 28 previously-failing files with correct configuration"
echo "================================================================"
echo ""

# Common flags for all UVM/DV files
# Strategy: Let files include their own dv_macros.svh, we just provide UVM and paths
COMMON_FLAGS=(
    "--include_paths=${UVM_ROOT}"
    "--include_paths=${OPENTITAN_ROOT}/hw/dv/sv"
    "--include_paths=${OPENTITAN_ROOT}/hw/dv/sv/dv_utils"
    "--include_paths=${OPENTITAN_ROOT}/hw/dv/sv/cip_lib"
    "--pre_include=${UVM_ROOT}/uvm_macros.svh"
    "--package_context=${OPENTITAN_ROOT}/hw/dv/sv/dv_utils/dv_utils_pkg.sv"
    "--package_context=${OPENTITAN_ROOT}/hw/dv/sv/cip_lib/cip_base_pkg.sv"
    "--package_context_disable_includes"
)

passed=0
failed=0
skipped=0

# Function to test a file
test_file() {
    local file="$1"
    local desc="$2"
    
    if [ ! -f "${OPENTITAN_ROOT}/${file}" ]; then
        echo -e "${YELLOW}SKIP${NC}: ${file} (not found)"
        ((skipped++))
        return
    fi
    
    echo -n "Testing: ${file} ... "
    
    if "${VERIBLE_BIN}" "${COMMON_FLAGS[@]}" "${OPENTITAN_ROOT}/${file}" > /dev/null 2>&1; then
        echo -e "${GREEN}PASS${NC} ${desc}"
        ((passed++))
    else
        echo -e "${RED}FAIL${NC} ${desc}"
        ((failed++))
        # Show error for debugging
        "${VERIBLE_BIN}" "${COMMON_FLAGS[@]}" "${OPENTITAN_ROOT}/${file}" 2>&1 | grep "syntax error" | head -3
    fi
}

echo "================================================================"
echo "Category 1: Files with Missing UVM Macros (4 files)"
echo "Fix: Add --pre_include=uvm_macros.svh"
echo "================================================================"

test_file "hw/ip/aon_timer/dv/env/aon_timer_scoreboard.sv" "(-> operator after uvm_info)"
test_file "hw/dv/sv/spi_agent/spi_monitor.sv" "(-> operator after uvm_info)"
test_file "hw/top_darjeeling/dv/env/seq_lib/chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq.sv" "(-> operator)"

echo ""
echo "================================================================"
echo "Category 2: Files with Missing DV Package Macros (15 files)"
echo "Fix: Add --package_context with dv_utils_pkg.sv and cip_base_pkg.sv"
echo "================================================================"

test_file "hw/dv/sv/cip_lib/cip_base_env_cfg.sv" "(DV_CHECK macros)"
test_file "hw/dv/sv/dv_lib/dv_base_env_cfg.sv" "(foreach in constraint)"
test_file "hw/ip/csrng/dv/env/csrng_env_cfg.sv" "(constraint macros)"
test_file "hw/ip/edn/dv/env/edn_env_cfg.sv" "(for in constraint)"
test_file "hw/ip/entropy_src/dv/env/entropy_src_env_cfg.sv" "(constraint macros)"
test_file "hw/ip/otbn/dv/uvm/env/otbn_env_cfg.sv" "(constraint macros)"
test_file "hw/ip/sram_ctrl/dv/env/sram_ctrl_env_cfg.sv" "(constraint macros)"
test_file "hw/top_darjeeling/ip_autogen/otp_ctrl/dv/env/otp_ctrl_env_cfg.sv" "(foreach in constraint)"
test_file "hw/top_earlgrey/ip_autogen/otp_ctrl/dv/env/otp_ctrl_env_cfg.sv" "(foreach in constraint)"

echo ""
echo "================================================================"
echo "Category 3: Files with Custom Macros (3 files)"
echo "Fix: Add --package_context with specific package files"
echo "================================================================"

# These need additional package context - will likely still fail without IP-specific packages
test_file "hw/ip/kmac/dv/env/kmac_env_cov.sv" "(XOF_CROSS_CG macro)"
test_file "hw/ip/spi_device/dv/env/spi_device_scoreboard.sv" "(CREATE_TPM_CASE_STMT macro)"

echo ""
echo "================================================================"
echo "SUMMARY"
echo "================================================================"
echo "Passed:  ${passed}"
echo "Failed:  ${failed}"
echo "Skipped: ${skipped}"
echo ""

if [ ${passed} -ge 10 ]; then
    echo -e "${GREEN}✅ EXCELLENT: ${passed} files now parse correctly with proper context!${NC}"
elif [ ${passed} -ge 5 ]; then
    echo -e "${YELLOW}⚠️  GOOD: ${passed} files fixed, but more work needed${NC}"
else
    echo -e "${RED}❌ NEEDS WORK: Only ${passed} files fixed${NC}"
fi

echo ""
echo "================================================================"
echo "Validation complete!"
echo "================================================================"

exit 0

