#!/bin/bash
# Full OpenTitan corpus validation - all 3,911 files
# v5.4.0 final validation

OPENTITAN_ROOT="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
VERIBLE_SYNTAX="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
RESULTS_FILE="opentitan_full_validation_$(date +%Y%m%d_%H%M%S).txt"

echo "================================================================"
echo "OpenTitan Full Corpus Validation - v5.4.0"
echo "================================================================"
echo ""
echo "This will test all SystemVerilog files in OpenTitan"
echo "Expected time: 10-20 minutes"
echo ""

# Count files
TOTAL=$(find "$OPENTITAN_ROOT" -name "*.sv" -type f 2>/dev/null | wc -l | tr -d ' ')
echo "Total files to test: $TOTAL"
echo ""

# Initialize counters
PASS=0
FAIL=0
COUNTER=0

# Start results file
{
  echo "================================================================"
  echo "OpenTitan Full Validation Results - v5.4.0"
  echo "Date: $(date)"
  echo "Total Files: $TOTAL"
  echo "================================================================"
  echo ""
  echo "FAILED FILES:"
  echo ""
} > "$RESULTS_FILE"

# Process all files
find "$OPENTITAN_ROOT" -name "*.sv" -type f 2>/dev/null | while read file; do
  ((COUNTER++))
  
  # Show progress every 50 files
  if [ $((COUNTER % 50)) -eq 0 ]; then
    PCT=$((COUNTER * 100 / TOTAL))
    echo "Progress: $COUNTER/$TOTAL ($PCT%) - Pass: $PASS, Fail: $FAIL"
  fi
  
  # Test the file
  if $VERIBLE_SYNTAX "$file" >/dev/null 2>&1; then
    ((PASS++))
  else
    ((FAIL++))
    # Log failure with relative path
    REL_PATH=$(echo "$file" | sed "s|$OPENTITAN_ROOT/||")
    echo "FAIL: $REL_PATH" >> "$RESULTS_FILE"
    
    # Get first error line for context
    ERROR=$($VERIBLE_SYNTAX "$file" 2>&1 | grep "syntax error\|error:" | head -1)
    echo "  $ERROR" >> "$RESULTS_FILE"
    echo "" >> "$RESULTS_FILE"
  fi
done

# Wait for background jobs
wait

# Calculate final statistics
TOTAL_ACTUAL=$(find "$OPENTITAN_ROOT" -name "*.sv" -type f 2>/dev/null | wc -l | tr -d ' ')
PASS_FINAL=$(grep -c "^FAIL:" "$RESULTS_FILE" || echo "0")
FAIL_FINAL=$PASS_FINAL
PASS_FINAL=$((TOTAL_ACTUAL - FAIL_FINAL))
SUCCESS_RATE=$(awk "BEGIN {printf \"%.2f\", ($PASS_FINAL/$TOTAL_ACTUAL)*100}")

# Write summary
{
  echo ""
  echo "================================================================"
  echo "SUMMARY"
  echo "================================================================"
  echo "Total files:      $TOTAL_ACTUAL"
  echo "Passed:           $PASS_FINAL ($SUCCESS_RATE%)"
  echo "Failed:           $FAIL_FINAL"
  echo ""
  echo "Success rate:     $SUCCESS_RATE%"
  echo "================================================================"
} | tee -a "$RESULTS_FILE"

echo ""
echo "Full results saved to: $RESULTS_FILE"
echo ""

# Show verdict
if (( $(echo "$SUCCESS_RATE >= 95.0" | bc -l) )); then
  echo "✅ EXCELLENT: $SUCCESS_RATE% success rate!"
elif (( $(echo "$SUCCESS_RATE >= 90.0" | bc -l) )); then
  echo "✅ GOOD: $SUCCESS_RATE% success rate"
elif (( $(echo "$SUCCESS_RATE >= 85.0" | bc -l) )); then
  echo "✅ ACCEPTABLE: $SUCCESS_RATE% success rate"
else
  echo "⚠️  NEEDS REVIEW: $SUCCESS_RATE% success rate"
fi

echo ""
echo "Validation complete!"

