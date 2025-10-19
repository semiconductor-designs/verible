#!/bin/bash
# Test Verible against broader corpus (Ibex, PULPino, OpenTitan)
# Part of v5.5.0 comprehensive testing framework

set -e

SYNTAX_TOOL="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
CORPUS_DIR="test_corpus"

if [ ! -f "$SYNTAX_TOOL" ]; then
  echo "Error: $SYNTAX_TOOL not found. Please build first:"
  echo "  bazel build //verible/verilog/tools/syntax:verible-verilog-syntax"
  exit 1
fi

if [ ! -d "$CORPUS_DIR" ]; then
  echo "Error: Test corpus not found. Please run:"
  echo "  ./scripts/setup_test_corpus.sh"
  exit 1
fi

echo "=== Broader Corpus Testing ==="
echo "Using: $SYNTAX_TOOL"
echo ""

# Test Ibex
echo "Testing Ibex RISC-V Core..."
IBEX_FILES=$(find "$CORPUS_DIR/ibex" -name "*.sv" -o -name "*.svh" 2>/dev/null | wc -l | tr -d ' ')
IBEX_PASS=0
if [ "$IBEX_FILES" -gt 0 ]; then
  for file in $(find "$CORPUS_DIR/ibex" -name "*.sv" -o -name "*.svh" 2>/dev/null); do
    if $SYNTAX_TOOL "$file" &>/dev/null; then
      ((IBEX_PASS++))
    fi
  done
  IBEX_PCT=$((100 * IBEX_PASS / IBEX_FILES))
  echo "Ibex: $IBEX_PASS / $IBEX_FILES passed ($IBEX_PCT%)"
else
  echo "Ibex: No files found"
  IBEX_FILES=0
fi

# Test PULPino
echo ""
echo "Testing PULPino..."
PULP_FILES=$(find "$CORPUS_DIR/pulpino" -name "*.sv" 2>/dev/null | wc -l | tr -d ' ')
PULP_PASS=0
if [ "$PULP_FILES" -gt 0 ]; then
  for file in $(find "$CORPUS_DIR/pulpino" -name "*.sv" 2>/dev/null); do
    if $SYNTAX_TOOL "$file" &>/dev/null; then
      ((PULP_PASS++))
    fi
  done
  PULP_PCT=$((100 * PULP_PASS / PULP_FILES))
  echo "PULPino: $PULP_PASS / $PULP_FILES passed ($PULP_PCT%)"
else
  echo "PULPino: No files found"
  PULP_FILES=0
fi

# Test full OpenTitan (sample 100 files)
echo ""
echo "Testing OpenTitan (sampling 100 files)..."
OT_FILES=$(find "$CORPUS_DIR/opentitan/hw" -name "*.sv" 2>/dev/null | head -100 | wc -l | tr -d ' ')
OT_PASS=0
if [ "$OT_FILES" -gt 0 ]; then
  for file in $(find "$CORPUS_DIR/opentitan/hw" -name "*.sv" 2>/dev/null | head -100); do
    # Try with pre_include for DV files
    if [[ "$file" == */dv/* ]]; then
      if $SYNTAX_TOOL \
        --pre_include="$CORPUS_DIR/opentitan/hw/dv/sv/dv_utils/dv_macros.svh" \
        --include_paths="third_party/uvm/src,$CORPUS_DIR/opentitan/hw/dv/sv/dv_utils" \
        "$file" &>/dev/null; then
        ((OT_PASS++))
      fi
    else
      if $SYNTAX_TOOL "$file" &>/dev/null; then
        ((OT_PASS++))
      fi
    fi
  done
  OT_PCT=$((100 * OT_PASS / OT_FILES))
  echo "OpenTitan: $OT_PASS / $OT_FILES passed ($OT_PCT%)"
else
  echo "OpenTitan: No files found"
  OT_FILES=0
fi

# Summary
echo ""
echo "=== Summary ==="
TOTAL_FILES=$((IBEX_FILES + PULP_FILES + OT_FILES))
TOTAL_PASS=$((IBEX_PASS + PULP_PASS + OT_PASS))
if [ "$TOTAL_FILES" -gt 0 ]; then
  TOTAL_PCT=$((100 * TOTAL_PASS / TOTAL_FILES))
  echo "Total: $TOTAL_PASS / $TOTAL_FILES passed ($TOTAL_PCT%)"
  
  if [ "$TOTAL_PCT" -lt 80 ]; then
    echo "⚠️  Warning: Success rate below 80%"
    exit 1
  elif [ "$TOTAL_PCT" -lt 90 ]; then
    echo "⚠️  Success rate below 90%, consider investigating"
  else
    echo "✅ Good success rate!"
  fi
else
  echo "❌ No files found in corpus"
  exit 1
fi

