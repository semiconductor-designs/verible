#!/bin/bash
# Analyze failure patterns across different projects
# Part of v5.5.0 comprehensive testing framework

SYNTAX_TOOL="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
CORPUS_DIR="test_corpus"
FAILURE_LOG="corpus_failures.log"

if [ ! -f "$SYNTAX_TOOL" ]; then
  echo "Error: $SYNTAX_TOOL not found."
  exit 1
fi

if [ ! -d "$CORPUS_DIR" ]; then
  echo "Error: Test corpus not found."
  exit 1
fi

echo "=== Analyzing Corpus Failures ===" > "$FAILURE_LOG"
echo "Analysis date: $(date)" >> "$FAILURE_LOG"
echo "" >> "$FAILURE_LOG"

# Analyze Ibex
if [ -d "$CORPUS_DIR/ibex" ]; then
  echo "Project: Ibex RISC-V Core" >> "$FAILURE_LOG"
  echo "------------------------" >> "$FAILURE_LOG"
  
  FILE_COUNT=0
  FAIL_COUNT=0
  for file in $(find "$CORPUS_DIR/ibex" -name "*.sv" -o -name "*.svh" 2>/dev/null | head -50); do
    ((FILE_COUNT++))
    ERROR=$($SYNTAX_TOOL "$file" 2>&1 | grep -i "error\|syntax" || true)
    if [ -n "$ERROR" ]; then
      ((FAIL_COUNT++))
      echo "File: $file" >> "$FAILURE_LOG"
      echo "$ERROR" | head -3 >> "$FAILURE_LOG"
      echo "" >> "$FAILURE_LOG"
    fi
  done
  echo "Ibex: $FAIL_COUNT failures out of $FILE_COUNT files analyzed" >> "$FAILURE_LOG"
  echo "" >> "$FAILURE_LOG"
fi

# Analyze PULPino
if [ -d "$CORPUS_DIR/pulpino" ]; then
  echo "Project: PULPino" >> "$FAILURE_LOG"
  echo "----------------" >> "$FAILURE_LOG"
  
  FILE_COUNT=0
  FAIL_COUNT=0
  for file in $(find "$CORPUS_DIR/pulpino" -name "*.sv" 2>/dev/null | head -50); do
    ((FILE_COUNT++))
    ERROR=$($SYNTAX_TOOL "$file" 2>&1 | grep -i "error\|syntax" || true)
    if [ -n "$ERROR" ]; then
      ((FAIL_COUNT++))
      echo "File: $file" >> "$FAILURE_LOG"
      echo "$ERROR" | head -3 >> "$FAILURE_LOG"
      echo "" >> "$FAILURE_LOG"
    fi
  done
  echo "PULPino: $FAIL_COUNT failures out of $FILE_COUNT files analyzed" >> "$FAILURE_LOG"
  echo "" >> "$FAILURE_LOG"
fi

# Analyze OpenTitan
if [ -d "$CORPUS_DIR/opentitan" ]; then
  echo "Project: OpenTitan" >> "$FAILURE_LOG"
  echo "------------------" >> "$FAILURE_LOG"
  
  FILE_COUNT=0
  FAIL_COUNT=0
  for file in $(find "$CORPUS_DIR/opentitan/hw" -name "*.sv" 2>/dev/null | head -50); do
    ((FILE_COUNT++))
    ERROR=$($SYNTAX_TOOL "$file" 2>&1 | grep -i "error\|syntax" || true)
    if [ -n "$ERROR" ]; then
      ((FAIL_COUNT++))
      echo "File: $file" >> "$FAILURE_LOG"
      echo "$ERROR" | head -3 >> "$FAILURE_LOG"
      echo "" >> "$FAILURE_LOG"
    fi
  done
  echo "OpenTitan: $FAIL_COUNT failures out of $FILE_COUNT files analyzed" >> "$FAILURE_LOG"
  echo "" >> "$FAILURE_LOG"
fi

# Summarize common error patterns
echo "=== Common Error Patterns ===" >> "$FAILURE_LOG"
grep "syntax error at token" "$FAILURE_LOG" | sed 's/.*syntax error at token/syntax error at token/' | sort | uniq -c | sort -rn | head -10 >> "$FAILURE_LOG"

echo "" >> "$FAILURE_LOG"
echo "=== Error Type Summary ===" >> "$FAILURE_LOG"
grep -i "include file not found" "$FAILURE_LOG" | wc -l | xargs echo "Include not found:" >> "$FAILURE_LOG"
grep -i "macro.*not defined" "$FAILURE_LOG" | wc -l | xargs echo "Undefined macro:" >> "$FAILURE_LOG"
grep -i "syntax error" "$FAILURE_LOG" | wc -l | xargs echo "Syntax errors:" >> "$FAILURE_LOG"

echo ""
echo "✅ Analysis complete! Results saved to: $FAILURE_LOG"
echo ""
cat "$FAILURE_LOG"

