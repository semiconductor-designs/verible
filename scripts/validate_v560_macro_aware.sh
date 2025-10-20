#!/bin/bash
# v5.6.0 Week 9-10: Comprehensive corpus validation script
# Tests all three disambiguation modes against OpenTitan, Ibex, and PULPino

set -e

# Configuration
SYNTAX_TOOL="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
OUTPUT_DIR="v560_validation_output"
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "╔══════════════════════════════════════════════════════════════════╗"
echo "║         v5.6.0 Corpus Validation - Macro-Aware Context          ║"
echo "╚══════════════════════════════════════════════════════════════════╝"
echo ""

# Check if syntax tool exists
if [ ! -f "$SYNTAX_TOOL" ]; then
    echo -e "${RED}Error: Syntax tool not found at $SYNTAX_TOOL${NC}"
    echo "Please build it first:"
    echo "  bazel build //verible/verilog/tools/syntax:verible-verilog-syntax -c opt"
    exit 1
fi

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Function to test a corpus
test_corpus() {
    local corpus_name=$1
    local corpus_path=$2
    local mode=$3
    local output_file="$OUTPUT_DIR/${corpus_name}_${mode}_${TIMESTAMP}.log"
    
    echo -e "${YELLOW}Testing $corpus_name with $mode mode...${NC}"
    
    if [ ! -d "$corpus_path" ]; then
        echo -e "${RED}  Corpus not found: $corpus_path${NC}"
        echo "0" > "$OUTPUT_DIR/${corpus_name}_${mode}_count.txt"
        return
    fi
    
    local file_count=0
    local success_count=0
    local fail_count=0
    
    # Find all .sv and .svh files
    while IFS= read -r file; do
        ((file_count++))
        
        if $SYNTAX_TOOL --arrow_disambiguation_mode="$mode" "$file" > /dev/null 2>&1; then
            ((success_count++))
        else
            ((fail_count++))
            echo "FAIL: $file" >> "$output_file"
        fi
    done < <(find "$corpus_path" -type f \( -name "*.sv" -o -name "*.svh" \) 2>/dev/null)
    
    # Calculate success rate
    local success_rate=0
    if [ $file_count -gt 0 ]; then
        success_rate=$(awk "BEGIN {printf \"%.2f\", ($success_count/$file_count)*100}")
    fi
    
    # Save results
    echo "$file_count" > "$OUTPUT_DIR/${corpus_name}_${mode}_total.txt"
    echo "$success_count" > "$OUTPUT_DIR/${corpus_name}_${mode}_success.txt"
    echo "$fail_count" > "$OUTPUT_DIR/${corpus_name}_${mode}_fail.txt"
    echo "$success_rate" > "$OUTPUT_DIR/${corpus_name}_${mode}_rate.txt"
    
    # Print summary
    if (( $(echo "$success_rate >= 95" | bc -l) )); then
        echo -e "${GREEN}  ✓ $success_count/$file_count files ($success_rate%)${NC}"
    elif (( $(echo "$success_rate >= 90" | bc -l) )); then
        echo -e "${YELLOW}  ⚠ $success_count/$file_count files ($success_rate%)${NC}"
    else
        echo -e "${RED}  ✗ $success_count/$file_count files ($success_rate%)${NC}"
    fi
    
    if [ $fail_count -gt 0 ]; then
        echo -e "    Failed files logged to: $output_file"
    fi
}

# Test each corpus with each mode
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Mode 1: macro_aware (baseline)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
test_corpus "opentitan" "test_corpus/opentitan" "macro_aware"
test_corpus "ibex" "test_corpus/ibex" "macro_aware"
test_corpus "pulpino" "test_corpus/pulpino" "macro_aware"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Mode 2: enhanced_heuristic (experimental)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
test_corpus "opentitan" "test_corpus/opentitan" "enhanced_heuristic"
test_corpus "ibex" "test_corpus/ibex" "enhanced_heuristic"
test_corpus "pulpino" "test_corpus/pulpino" "enhanced_heuristic"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Mode 3: both (A/B testing)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
test_corpus "opentitan" "test_corpus/opentitan" "both"

echo ""
echo "╔══════════════════════════════════════════════════════════════════╗"
echo "║                      FINAL SUMMARY                               ║"
echo "╚══════════════════════════════════════════════════════════════════╝"

# Generate summary
generate_summary() {
    local mode=$1
    echo ""
    echo "━━━━━ $mode mode ━━━━━"
    
    for corpus in opentitan ibex pulpino; do
        if [ -f "$OUTPUT_DIR/${corpus}_${mode}_total.txt" ]; then
            local total=$(cat "$OUTPUT_DIR/${corpus}_${mode}_total.txt")
            local success=$(cat "$OUTPUT_DIR/${corpus}_${mode}_success.txt")
            local rate=$(cat "$OUTPUT_DIR/${corpus}_${mode}_rate.txt")
            
            printf "%-12s: %5s/%5s (%6s%%)\n" "$corpus" "$success" "$total" "$rate"
        fi
    done
}

generate_summary "macro_aware"
generate_summary "enhanced_heuristic"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Results saved to: $OUTPUT_DIR"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

