#!/bin/bash
# Full documentation build for this repository: InformationTheory + its whole Mathlib closure.
set -u
cd /Users/haruka/dev/lean-projects
BENCH=$PWD/docs/doc-gen-bench/raw
export DOCGEN_TIMING=$BENCH/full-build.jsonl
rm -f "$DOCGEN_TIMING"
df -k . | tail -1 > "$BENCH/full-build-summary.txt"
start=$(date +%s)
/usr/bin/time -l lake build InformationTheory:docs > "$BENCH/full-build.log" 2>&1
rc=$?
end=$(date +%s)
echo "rc=$rc wall_seconds=$((end-start))" >> "$BENCH/full-build-summary.txt"
df -k . | tail -1 >> "$BENCH/full-build-summary.txt"
du -sk .lake/build/api-docs.db .lake/build/doc .lake/build/doc-data >> "$BENCH/full-build-summary.txt" 2>/dev/null
