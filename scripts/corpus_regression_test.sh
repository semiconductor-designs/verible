#!/bin/bash
# Corpus Regression Test Framework
# Run before each release to ensure no regressions
# Part of v5.5.0 comprehensive testing

set -e

BASELINE_RESULTS="corpus_baseline.txt"
CURRENT_RESULTS="corpus_current.txt"
DIFF_FILE="corpus_diff.txt"

echo "=== Corpus Regression Testing ==="
echo ""

# Check if test corpus exists
if [ ! -d "test_corpus" ]; then
  echo "⚠️  Test corpus not found. Running setup..."
  ./scripts/setup_test_corpus.sh
fi

# Run current version
echo "Running broader corpus tests..."
./scripts/test_broader_corpus.sh > "$CURRENT_RESULTS" 2>&1

# Extract success rates
CURRENT_RATE=$(grep "Total:.*passed" "$CURRENT_RESULTS" | tail -1 | grep -o "[0-9]*%" || echo "0%")

echo ""
echo "Current results: $CURRENT_RATE success rate"

# Compare with baseline if it exists
if [ -f "$BASELINE_RESULTS" ]; then
  echo ""
  echo "Comparing with baseline..."
  
  BASELINE_RATE=$(grep "Total:.*passed" "$BASELINE_RESULTS" | tail -1 | grep -o "[0-9]*%" || echo "0%")
  echo "Baseline results: $BASELINE_RATE success rate"
  
  diff "$BASELINE_RESULTS" "$CURRENT_RESULTS" > "$DIFF_FILE" 2>&1 || true
  
  if [ -s "$DIFF_FILE" ]; then
    echo ""
    echo "⚠️  WARNING: Corpus results changed!"
    echo ""
    echo "Changes detected:"
    cat "$DIFF_FILE" | head -20
    echo ""
    
    # Check if success rate decreased
    CURRENT_NUM=$(echo "$CURRENT_RATE" | tr -d '%')
    BASELINE_NUM=$(echo "$BASELINE_RATE" | tr -d '%')
    
    if [ "$CURRENT_NUM" -lt "$BASELINE_NUM" ]; then
      echo "❌ REGRESSION: Success rate decreased from $BASELINE_RATE to $CURRENT_RATE"
      echo ""
      echo "To update baseline (if changes are intentional):"
      echo "  cp $CURRENT_RESULTS $BASELINE_RESULTS"
      exit 1
    elif [ "$CURRENT_NUM" -gt "$BASELINE_NUM" ]; then
      echo "✅ IMPROVEMENT: Success rate increased from $BASELINE_RATE to $CURRENT_RATE"
      echo ""
      echo "Consider updating baseline:"
      echo "  cp $CURRENT_RESULTS $BASELINE_RESULTS"
    else
      echo "⚠️  Changes detected but success rate unchanged"
      echo ""
      echo "Review changes and update baseline if intentional:"
      echo "  cp $CURRENT_RESULTS $BASELINE_RESULTS"
    fi
  else
    echo "✅ No regressions detected (results match baseline)"
  fi
else
  echo ""
  echo "No baseline found. Creating baseline..."
  cp "$CURRENT_RESULTS" "$BASELINE_RESULTS"
  echo "✅ Baseline created: $BASELINE_RESULTS"
  echo ""
  echo "Future runs will compare against this baseline."
fi

echo ""
echo "=== Regression Test Complete ==="

