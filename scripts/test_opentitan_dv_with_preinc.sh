#!/bin/bash
# Test OpenTitan DV files using --pre_include approach

VERIBLE="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
OPENTITAN="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
PRE_INCLUDE="$OPENTITAN/hw/dv/sv/dv_utils/dv_macros.svh"
INCLUDE_PATHS="third_party/uvm/src,$OPENTITAN/hw/dv/sv/dv_utils"

# Representative DV files that benefit from --pre_include
DV_FILES=(
  "$OPENTITAN/hw/dv/sv/spi_agent/spi_agent.sv"
  "$OPENTITAN/hw/dv/sv/spi_agent/spi_sequencer.sv"
  "$OPENTITAN/hw/dv/sv/spi_agent/spi_host_driver.sv"
  "$OPENTITAN/hw/dv/sv/spi_agent/spi_device_driver.sv"
  "$OPENTITAN/hw/dv/sv/cip_lib/cip_base_env.sv"
  "$OPENTITAN/hw/dv/sv/cip_lib/cip_base_scoreboard.sv"
  "$OPENTITAN/hw/dv/sv/cip_lib/cip_base_virtual_sequencer.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_agent.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_env.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_monitor.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_scoreboard.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_sequencer.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_vseq.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_virtual_sequencer.sv"
  "$OPENTITAN/hw/dv/sv/mem_bkdr_util/mem_bkdr_util.sv"
  "$OPENTITAN/hw/dv/sv/push_pull_agent/push_pull_agent.sv"
  "$OPENTITAN/hw/dv/sv/push_pull_agent/push_pull_monitor.sv"
  "$OPENTITAN/hw/dv/sv/push_pull_agent/push_pull_sequencer.sv"
)

PASS=0
FAIL=0
ERRORS_FILE="/tmp/dv_errors.txt"
> "$ERRORS_FILE"

echo "========================================="
echo "Testing --pre_include Feature with DV Files"
echo "========================================="
echo ""
echo "Testing ${#DV_FILES[@]} OpenTitan DV files..."
echo ""

for file in "${DV_FILES[@]}"; do
  filename=$(basename "$file")
  
  # Test WITHOUT pre_include (should fail or have errors)
  error_count_without=$($VERIBLE "$file" 2>&1 | grep -c "error" || true)
  
  # Test WITH pre_include (should pass or have fewer errors)
  if $VERIBLE --pre_include="$PRE_INCLUDE" --include_paths="$INCLUDE_PATHS" "$file" >/dev/null 2>&1; then
    echo "✅ PASS: $filename (errors without: $error_count_without → with: 0)"
    ((PASS++))
  else
    error_count_with=$($VERIBLE --pre_include="$PRE_INCLUDE" --include_paths="$INCLUDE_PATHS" "$file" 2>&1 | grep -c "error" || true)
    echo "❌ FAIL: $filename (errors: $error_count_without → $error_count_with)"
    $VERIBLE --pre_include="$PRE_INCLUDE" --include_paths="$INCLUDE_PATHS" "$file" 2>&1 | grep "error" | head -2 >> "$ERRORS_FILE"
    echo "---" >> "$ERRORS_FILE"
    ((FAIL++))
  fi
done

echo ""
echo "========================================="
echo "Results: $PASS passed, $FAIL failed out of ${#DV_FILES[@]} files"
echo "Success Rate: $(( PASS * 100 / ${#DV_FILES[@]} ))%"
echo "========================================="
echo ""

if [ $FAIL -gt 0 ]; then
  echo "⚠️  Some files still failing (likely Verible parser limitations, not macro issues)"
  echo "Error summary saved to: $ERRORS_FILE"
  exit 1
else
  echo "✅ All DV files pass with --pre_include!"
  exit 0
fi

