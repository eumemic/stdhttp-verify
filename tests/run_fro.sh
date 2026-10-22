#!/bin/bash
# Usage: run_fro.sh <lake project dir> <test dir>  — runs each test file, prints PASS/FAIL per file.
proj="$1"; dir="$(cd "$2" && pwd)"
cd "$proj" || exit 1
pass=0; fail=0
for f in "$dir"/*.lean; do
  start=$(date +%s)
  out=$(lake env lean "$f" 2>&1); code=$?
  if [ $code -eq 0 ] && ! grep -q -E '(^|: )error' <<<"$out"; then pass=$((pass+1)); s=PASS; else fail=$((fail+1)); s=FAIL; fi
  echo "$s $(basename "$f") ($(( $(date +%s) - start ))s)"
  [ $s = FAIL ] && grep -E 'error' <<<"$out" | head -3 | sed 's/^/      /'
done
echo "TOTAL pass=$pass fail=$fail"
