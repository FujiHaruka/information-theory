#!/usr/bin/env bash
# PostToolUse(Edit|Write) gate: InformationTheory/**.lean のコード表面規約を編集直後に検査する。
#
# Why: docstring 規約の違反は「書かれた瞬間」に誰も見ていないため再発する (docs/rules/docstrings.md
# 乖離表 / docstring-tidyup-plan.md Phase 4 → 6 が同じ再発を 2 度記録している)。git フックは
# コミット時、CI はさらに後 — どちらも「溜まってから一括スイープ」に戻ってしまう。ここで exit 2 +
# stderr を返すと Claude Code が理由を差し戻すので、同一ターン内で直る。
#
# 判定本体は scripts/lean_doc_lint.ts (実装 SoT、pre-commit / CI からも同じものを呼ぶ)。
# 規約の定義は docs/rules/ 側。
set -u

file="$(jq -r '.tool_input.file_path // empty' 2>/dev/null)"
[ -z "$file" ] && exit 0
case "$file" in
  *InformationTheory/*.lean) : ;;
  *) exit 0 ;;
esac

root="${CLAUDE_PROJECT_DIR:-$(git rev-parse --show-toplevel 2>/dev/null)}"
[ -z "$root" ] && exit 0
command -v deno >/dev/null 2>&1 || exit 0

cd "$root" || exit 0
out="$(deno run -A scripts/lean_doc_lint.ts --hook "$file" 2>&1)"
status=$?
if [ "$status" -eq 2 ] && [ -n "$out" ]; then
  printf '%s\n' "$out" >&2
  exit 2
fi
exit 0
