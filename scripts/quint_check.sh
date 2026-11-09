#!/bin/bash
# Elaborate Quint example files with Veil and print each file's result lines.
# Usage: scripts/quint_check.sh Examples/Quint/Classic/...lean ...
cd "$(dirname "$0")/.."
for f in "$@"; do
  m=$(echo "${f%.lean}" | tr '/' '.')
  out=$(lake build "$m" 2>&1)
  echo "=== $f"
  echo "$out" | grep -E "error|No violation|Violation|explored|Satisfying|✅|❌|found" | grep -v "^\s*$" | head -15
done
