#!/bin/bash
# Continuous monitoring of Verible parse statistics
# Part of v5.5.0 production monitoring system

SYNTAX_TOOL="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
LOG_FILE="build/verible_monitoring.log"
TEST_CORPUS="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan/hw"

mkdir -p build

echo "Verible Production Monitoring System"
echo "Log file: $LOG_FILE"
echo "Test corpus: $TEST_CORPUS"
echo ""

while true; do
  echo "=== $(date) ===" | tee -a "$LOG_FILE"
  
  # Run on test corpus with stats
  find "$TEST_CORPUS" -name "*.sv" | head -100 | while read file; do
    $SYNTAX_TOOL "$file" &>/dev/null
  done
  
  # Get aggregated stats
  find "$TEST_CORPUS" -name "*.sv" | head -100 | \
    xargs $SYNTAX_TOOL --show_stats 2>&1 | tee -a "$LOG_FILE"
  
  # Check for failures
  FAIL_COUNT=$(grep "Failed:" "$LOG_FILE" | tail -1 | awk '{print $2}')
  if [ -n "$FAIL_COUNT" ] && [ "$FAIL_COUNT" -gt 5 ]; then
    echo "⚠️  ALERT: High failure count: $FAIL_COUNT" | tee -a "$LOG_FILE"
  fi
  
  # Check for arrow syntax errors
  ARROW_ERRORS=$(grep "arrow_syntax_error" "$LOG_FILE" | tail -1 | awk '{print $2}')
  if [ -n "$ARROW_ERRORS" ] && [ "$ARROW_ERRORS" -gt 0 ]; then
    echo "⚠️  ALERT: Arrow syntax errors detected: $ARROW_ERRORS" | tee -a "$LOG_FILE"
  fi
  
  echo "" | tee -a "$LOG_FILE"
  echo "Next monitoring cycle in 1 hour..." | tee -a "$LOG_FILE"
  echo "Press Ctrl+C to stop" | tee -a "$LOG_FILE"
  
  sleep 3600  # Run hourly
done

