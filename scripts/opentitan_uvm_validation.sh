#!/bin/bash
# Week 10: OpenTitan UVM Validation Script
# Tests Verible parser on OpenTitan UVM verification files

set -e

OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
VERIBLE_PARSER="bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
OUTPUT_DIR="validation_results"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_FILE="${OUTPUT_DIR}/opentitan_phase2_${TIMESTAMP}.txt"

# Ensure parser is built
echo "Building Verible parser..."
bazel build //verible/verilog/tools/syntax:verible-verilog-syntax

# Create output directory
mkdir -p "${OUTPUT_DIR}"

# Find all UVM-related files
echo "Finding OpenTitan UVM files..."
UVM_FILES=$(find "${OPENTITAN_ROOT}" -name "*.sv" \( \
  -path "*/dv/env/*" -o \
  -path "*/dv/agent/*" -o \
  -path "*/dv/seq_lib/*" -o \
  -name "*_agent*.sv" -o \
  -name "*_seq*.sv" -o \
  -name "*_item*.sv" -o \
  -name "*_driver*.sv" -o \
  -name "*_monitor*.sv" -o \
  -name "*_scoreboard*.sv" -o \
  -name "*_env*.sv" -o \
  -name "*_base_test*.sv" -o \
  -name "*_vseq*.sv" \
\) 2>/dev/null | sort -u)

TOTAL_FILES=$(echo "$UVM_FILES" | wc -l | tr -d ' ')
echo "Found ${TOTAL_FILES} UVM files"

# Initialize counters
PASS=0
FAIL=0
ERRORS=0

# Results header
echo "================================" | tee "${RESULTS_FILE}"
echo "OpenTitan UVM Validation - Phase 2" | tee -a "${RESULTS_FILE}"
echo "Date: $(date)" | tee -a "${RESULTS_FILE}"
echo "Total Files: ${TOTAL_FILES}" | tee -a "${RESULTS_FILE}"
echo "================================" | tee -a "${RESULTS_FILE}"
echo "" | tee -a "${RESULTS_FILE}"

# Test each file
COUNTER=1
while IFS= read -r file; do
  REL_PATH=$(echo "$file" | sed "s|${OPENTITAN_ROOT}/||")
  printf "[%3d/%3d] Testing: %s\n" "$COUNTER" "$TOTAL_FILES" "$REL_PATH"
  
  # Run parser
  if "${VERIBLE_PARSER}" "$file" >/dev/null 2>&1; then
    echo "  ✅ PASS" | tee -a "${RESULTS_FILE}"
    ((PASS++))
  else
    # Capture error
    ERROR_MSG=$("${VERIBLE_PARSER}" "$file" 2>&1 | head -5 | sed 's/^/    /')
    echo "  ❌ FAIL" | tee -a "${RESULTS_FILE}"
    echo "  Error: ${ERROR_MSG}" >> "${RESULTS_FILE}"
    ((FAIL++))
  fi
  
  ((COUNTER++))
done <<< "$UVM_FILES"

# Summary
echo "" | tee -a "${RESULTS_FILE}"
echo "================================" | tee -a "${RESULTS_FILE}"
echo "SUMMARY" | tee -a "${RESULTS_FILE}"
echo "================================" | tee -a "${RESULTS_FILE}"
echo "Total Files:  ${TOTAL_FILES}" | tee -a "${RESULTS_FILE}"
echo "Passed:       ${PASS}" | tee -a "${RESULTS_FILE}"
echo "Failed:       ${FAIL}" | tee -a "${RESULTS_FILE}"
echo "Success Rate: $(awk "BEGIN {printf \"%.1f%%\", ($PASS/$TOTAL_FILES)*100}")" | tee -a "${RESULTS_FILE}"
echo "================================" | tee -a "${RESULTS_FILE}"

# Phase 2 Target: ≥70 of 89 files (79%)
TARGET_FILES=70
if [ "$PASS" -ge "$TARGET_FILES" ]; then
  echo "✅ Phase 2 Target ACHIEVED (≥${TARGET_FILES} files)" | tee -a "${RESULTS_FILE}"
else
  echo "⚠️  Phase 2 Target NOT MET (${PASS} < ${TARGET_FILES})" | tee -a "${RESULTS_FILE}"
fi

echo ""
echo "Results saved to: ${RESULTS_FILE}"

