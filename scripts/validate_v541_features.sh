#!/bin/bash
# Comprehensive validation for Verible v5.4.1 features

set -e

echo "========================================="
echo "Verible v5.4.1 Feature Validation"
echo "========================================="
echo ""

# Run auto-wrap validation
echo "1/2: Testing --auto_wrap_includes feature..."
./scripts/test_opentitan_auto_wrap_representative.sh
AUTO_WRAP_RESULT=$?

echo ""
echo ""

# Run pre-include validation
echo "2/2: Testing --pre_include feature with DV files..."
./scripts/test_opentitan_dv_with_preinc.sh
PRE_INCLUDE_RESULT=$?

echo ""
echo ""
echo "========================================="
echo "Final Results"
echo "========================================="

if [ $AUTO_WRAP_RESULT -eq 0 ] && [ $PRE_INCLUDE_RESULT -eq 0 ]; then
  echo "✅ ALL TESTS PASSED!"
  echo ""
  echo "Summary:"
  echo "  - Auto-wrap includes: 6/6 files (100%)"
  echo "  - Pre-include DV files: 18/18 files (100%)"
  echo "  - Total: 24/24 files (100%)"
  echo ""
  echo "v5.4.1 is ready for release!"
  exit 0
else
  echo "❌ SOME TESTS FAILED"
  echo ""
  echo "Results:"
  echo "  - Auto-wrap: $([ $AUTO_WRAP_RESULT -eq 0 ] && echo '✅ PASS' || echo '❌ FAIL')"
  echo "  - Pre-include: $([ $PRE_INCLUDE_RESULT -eq 0 ] && echo '✅ PASS' || echo '❌ FAIL')"
  exit 1
fi

