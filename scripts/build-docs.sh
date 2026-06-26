#!/usr/bin/env bash
#
# Build HTML API documentation for the InformationTheory library only.
# Mathlib is intentionally excluded: only InformationTheory.* modules are
# analyzed into the SQLite DB, and `fromDb` (no module args) emits HTML for
# exactly the modules present in that DB.
#
# Usage:
#   scripts/build-docs.sh          # (re)generate docs into .lake/build/doc
#   scripts/build-docs.sh serve    # build, then serve on http://<lan-ip>:8000
#
# Env:
#   PORT=8000                      # port for `serve` (default 8000)
#
# Note: source links point to `#` (the fast bulk-analyze path carries no
# sourceUrl). The docs themselves render fully. See .claude/handoff history
# for the per-module GitHub source-link variant if needed.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DOCGEN="$ROOT/.lake/packages/doc-gen4/.lake/build/bin/doc-gen4"
DOC_OUT="$ROOT/.lake/build/doc"
PORT="${PORT:-8000}"

echo "==> [1/4] doc-gen4 executable (no-op if current)"
lake build doc-gen4/doc-gen4

echo "==> [2/4] InformationTheory oleans (no-op if current)"
lake build InformationTheory

echo "==> [3/4] Analyze InformationTheory.* into api-docs.db (db path is relative to .lake/build)"
rm -f .lake/build/api-docs.db .lake/build/api-docs.db-wal .lake/build/api-docs.db-shm
lake env "$DOCGEN" genCore InformationTheory api-docs.db

echo "==> [4/4] Generate HTML (DB holds InformationTheory only -> Mathlib excluded)"
rm -rf "$DOC_OUT"
lake env "$DOCGEN" fromDb --build .lake/build .lake/build/api-docs.db

count="$(find "$DOC_OUT" -name '*.html' | wc -l | tr -d ' ')"
echo "==> Done: $count HTML files in $DOC_OUT"

if [ "${1:-}" = "serve" ]; then
  ip="$(ipconfig getifaddr en0 2>/dev/null || true)"
  echo "==> Serving at http://localhost:$PORT${ip:+   (same Wi-Fi: http://$ip:$PORT)}"
  exec python3 -m http.server -d "$DOC_OUT" "$PORT"
else
  echo "    View: python3 -m http.server -d $DOC_OUT $PORT  then open http://localhost:$PORT"
fi
