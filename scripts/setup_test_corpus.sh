#!/bin/bash
# Setup test corpus for broader Verible validation
# Clones 3 additional open-source projects: Ibex, PULPino, OpenTitan

set -e

CORPUS_DIR="test_corpus"

echo "=== Setting up Test Corpus ==="
echo "Target directory: $CORPUS_DIR"
echo ""

mkdir -p "$CORPUS_DIR"
cd "$CORPUS_DIR"

# Project 1: Ibex RISC-V Core
if [ ! -d "ibex" ]; then
  echo "Cloning Ibex RISC-V Core..."
  git clone --depth 1 https://github.com/lowRISC/ibex.git
  cd ibex
  echo "Ibex cloned at commit: $(git rev-parse HEAD)"
  cd ..
else
  echo "✅ Ibex already exists"
fi

# Project 2: PULPino
if [ ! -d "pulpino" ]; then
  echo ""
  echo "Cloning PULPino..."
  git clone --depth 1 https://github.com/pulp-platform/pulpino.git
  cd pulpino
  echo "PULPino cloned at commit: $(git rev-parse HEAD)"
  cd ..
else
  echo "✅ PULPino already exists"
fi

# Project 3: LowRISC OpenTitan (full, not just DV)
if [ ! -d "opentitan" ]; then
  echo ""
  echo "Cloning OpenTitan (this may take a few minutes)..."
  git clone --depth 1 https://github.com/lowRISC/opentitan.git
  cd opentitan
  echo "OpenTitan cloned at commit: $(git rev-parse HEAD)"
  cd ..
else
  echo "✅ OpenTitan already exists"
fi

cd ../..

echo ""
echo "=== Corpus Statistics ==="
IBEX_FILES=$(find "$CORPUS_DIR/ibex" -name "*.sv" -o -name "*.svh" 2>/dev/null | wc -l)
PULP_FILES=$(find "$CORPUS_DIR/pulpino" -name "*.sv" 2>/dev/null | wc -l)
OT_FILES=$(find "$CORPUS_DIR/opentitan/hw" -name "*.sv" 2>/dev/null | wc -l)

echo "Ibex files: $IBEX_FILES"
echo "PULPino files: $PULP_FILES"
echo "OpenTitan files: $OT_FILES"
echo "Total: $((IBEX_FILES + PULP_FILES + OT_FILES)) SystemVerilog files"
echo ""
echo "✅ Test corpus setup complete!"

