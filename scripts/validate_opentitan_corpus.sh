#!/bin/bash
# Comprehensive OpenTitan corpus validation for v5.4.0
# Tests all SystemVerilog files in OpenTitan

set -e

OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
VERIBLE_SYNTAX="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"

echo "================================================================"
echo "OpenTitan Corpus Validation - v5.4.0"
echo "================================================================"
echo ""

# Find all .sv files
echo "Finding all SystemVerilog files..."
ALL_FILES=$(find "$OPENTITAN_ROOT" -name "*.sv" -type f 2>/dev/null | sort)
TOTAL=$(echo "$ALL_FILES" | wc -l | tr -d ' ')

echo "Found $TOTAL SystemVerilog files"
echo ""

PASS=0
FAIL=0
SYNTAX_ERROR=0
PREPROCESSOR_ERROR=0

RESULTS_FILE="opentitan_validation_v540_$(date +%Y%m%d_%H%M%S).txt"

echo "================================================================" | tee "$RESULTS_FILE"
echo "OpenTitan Validation Results - v5.4.0" | tee -a "$RESULTS_FILE"
echo "Date: $(date)" | tee -a "$RESULTS_FILE"
echo "Total Files: $TOTAL" | tee -a "$RESULTS_FILE"
echo "================================================================" | tee -a "$RESULTS_FILE"
echo "" | tee -a "$RESULTS_FILE"

COUNTER=0
while IFS= read -r file; do
  ((COUNTER++))
  
  # Show progress every 100 files
  if [ $((COUNTER % 100)) -eq 0 ]; then
    echo "Progress: $COUNTER/$TOTAL files processed..."
  fi
  
  # Try to parse the file
  OUTPUT=$($VERIBLE_SYNTAX "$file" 2>&1)
  EXIT_CODE=$?
  
  if [ $EXIT_CODE -eq 0 ]; then
    ((PASS++))
  else
    ((FAIL++))
    
    # Categorize the error
    if echo "$OUTPUT" | grep -q "syntax error"; then
      ((SYNTAX_ERROR++))
      ERROR_TYPE="SYNTAX_ERROR"
    elif echo "$OUTPUT" | grep -q "preprocessing error\|Preprocessor error"; then
      ((PREPROCESSOR_ERROR++))
      ERROR_TYPE="PREPROCESSOR_ERROR"
    else
      ERROR_TYPE="OTHER_ERROR"
    fi
    
    # Log the failure
    REL_PATH=$(echo "$file" | sed "s|$OPENTITAN_ROOT/||")
    echo "FAIL: $REL_PATH ($ERROR_TYPE)" >> "$RESULTS_FILE"
    
    # Show first error for context
    FIRST_ERROR=$(echo "$OUTPUT" | grep -E "error:" | head -1)
    echo "  $FIRST_ERROR" >> "$RESULTS_FILE"
  fi
done <<< "$ALL_FILES"

echo "" | tee -a "$RESULTS_FILE"
echo "================================================================" | tee -a "$RESULTS_FILE"
echo "Summary:" | tee -a "$RESULTS_FILE"
echo "  Total files:           $TOTAL" | tee -a "$RESULTS_FILE"
echo "  Passed:                $PASS ($(awk "BEGIN {printf \"%.1f\", ($PASS/$TOTAL)*100}")%)" | tee -a "$RESULTS_FILE"
echo "  Failed:                $FAIL ($(awk "BEGIN {printf \"%.1f\", ($FAIL/$TOTAL)*100}")%)" | tee -a "$RESULTS_FILE"
echo "    - Syntax errors:     $SYNTAX_ERROR" | tee -a "$RESULTS_FILE"
echo "    - Preprocessor:      $PREPROCESSOR_ERROR" | tee -a "$RESULTS_FILE"
echo "    - Other:             $((FAIL - SYNTAX_ERROR - PREPROCESSOR_ERROR))" | tee -a "$RESULTS_FILE"
echo "================================================================" | tee -a "$RESULTS_FILE"
echo "" | tee -a "$RESULTS_FILE"
echo "Full results saved to: $RESULTS_FILE"
echo ""

# Show success rate
SUCCESS_RATE=$(awk "BEGIN {printf \"%.1f\", ($PASS/$TOTAL)*100}")
if (( $(echo "$SUCCESS_RATE >= 95.0" | bc -l) )); then
  echo "✅ SUCCESS RATE: $SUCCESS_RATE% (Excellent!)"
elif (( $(echo "$SUCCESS_RATE >= 90.0" | bc -l) )); then
  echo "✅ SUCCESS RATE: $SUCCESS_RATE% (Good)"
elif (( $(echo "$SUCCESS_RATE >= 80.0" | bc -l) )); then
  echo "⚠️  SUCCESS RATE: $SUCCESS_RATE% (Acceptable)"
else
  echo "❌ SUCCESS RATE: $SUCCESS_RATE% (Needs improvement)"
fi

exit 0

