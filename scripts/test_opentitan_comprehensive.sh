#!/bin/bash
# Comprehensive OpenTitan testing with proper context per directory
# Part of v5.5.0 short-term validation

set -e

SYNTAX_TOOL="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
RESULTS_LOG="opentitan_comprehensive_results.txt"

if [ ! -f "$SYNTAX_TOOL" ]; then
  echo "Error: $SYNTAX_TOOL not found. Please build first."
  exit 1
fi

if [ ! -d "$OPENTITAN_ROOT" ]; then
  echo "Error: OpenTitan root not found: $OPENTITAN_ROOT"
  exit 1
fi

echo "=== Comprehensive OpenTitan Testing ===" | tee "$RESULTS_LOG"
echo "Date: $(date)" | tee -a "$RESULTS_LOG"
echo "" | tee -a "$RESULTS_LOG"

# Test RTL files (no special context needed)
echo "Testing RTL files..." | tee -a "$RESULTS_LOG"
RTL_FILES_TOTAL=$(find "$OPENTITAN_ROOT/hw" -path "*/rtl/*.sv" -o -path "*/ip*/rtl/*.sv" 2>/dev/null | wc -l | tr -d ' ')
RTL_FILES=0
RTL_PASS=0

if [ "$RTL_FILES_TOTAL" -gt 0 ]; then
  for file in $(find "$OPENTITAN_ROOT/hw" -path "*/rtl/*.sv" -o -path "*/ip*/rtl/*.sv" 2>/dev/null | head -100); do
    ((RTL_FILES++))
    if $SYNTAX_TOOL "$file" &>/dev/null; then
      ((RTL_PASS++))
    fi
  done
  if [ "$RTL_FILES" -gt 0 ]; then
    RTL_PCT=$((100 * RTL_PASS / RTL_FILES))
    echo "RTL: $RTL_PASS / $RTL_FILES tested ($(( 100 * RTL_FILES / RTL_FILES_TOTAL))% of $RTL_FILES_TOTAL total) - $RTL_PCT% success" | tee -a "$RESULTS_LOG"
  fi
else
  echo "RTL: No files found" | tee -a "$RESULTS_LOG"
fi

# Test DV files (with proper context)
echo "" | tee -a "$RESULTS_LOG"
echo "Testing DV files (with context)..." | tee -a "$RESULTS_LOG"
DV_FILES_TOTAL=$(find "$OPENTITAN_ROOT/hw" -path "*/dv/*.sv" 2>/dev/null | wc -l | tr -d ' ')
DV_FILES=0
DV_PASS=0

if [ "$DV_FILES_TOTAL" -gt 0 ]; then
  for file in $(find "$OPENTITAN_ROOT/hw" -path "*/dv/*.sv" 2>/dev/null | head -100); do
    ((DV_FILES++))
    if $SYNTAX_TOOL \
      --pre_include="$OPENTITAN_ROOT/hw/dv/sv/dv_utils/dv_macros.svh" \
      --include_paths="third_party/uvm/src,$OPENTITAN_ROOT/hw/dv/sv/dv_utils" \
      "$file" &>/dev/null 2>&1; then
      ((DV_PASS++))
    fi
  done
  
  if [ "$DV_FILES" -gt 0 ]; then
    DV_PCT=$((100 * DV_PASS / DV_FILES))
    echo "DV: $DV_PASS / $DV_FILES tested ($(( 100 * DV_FILES / DV_FILES_TOTAL))% of $DV_FILES_TOTAL total) - $DV_PCT% success" | tee -a "$RESULTS_LOG"
  fi
else
  echo "DV: No files found" | tee -a "$RESULTS_LOG"
fi

# Summary
echo "" | tee -a "$RESULTS_LOG"
echo "=== Summary ===" | tee -a "$RESULTS_LOG"
TOTAL_FILES=$((RTL_FILES + DV_FILES))
TOTAL_PASS=$((RTL_PASS + DV_PASS))

if [ "$TOTAL_FILES" -gt 0 ]; then
  TOTAL_PCT=$((100 * TOTAL_PASS / TOTAL_FILES))
  echo "Total: $TOTAL_PASS / $TOTAL_FILES passed ($TOTAL_PCT%)" | tee -a "$RESULTS_LOG"
  
  if [ "$TOTAL_PCT" -ge 99 ]; then
    echo "✅ Excellent: Success rate >= 99%" | tee -a "$RESULTS_LOG"
  elif [ "$TOTAL_PCT" -ge 95 ]; then
    echo "🟢 Good: Success rate >= 95%" | tee -a "$RESULTS_LOG"
  elif [ "$TOTAL_PCT" -ge 90 ]; then
    echo "🟡 Acceptable: Success rate >= 90%" | tee -a "$RESULTS_LOG"
  else
    echo "⚠️  Warning: Success rate < 90%" | tee -a "$RESULTS_LOG"
  fi
else
  echo "No files found to test" | tee -a "$RESULTS_LOG"
fi

echo "" | tee -a "$RESULTS_LOG"
echo "Results saved to: $RESULTS_LOG"

