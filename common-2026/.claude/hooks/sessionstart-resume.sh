#!/usr/bin/env bash
# SessionStart(matcher=clear) hook.
#
# ユーザーがリフレッシュを承認した直後の /clear のときだけ、新セッションへ
# 「handoff.md から再開せよ」を additionalContext として注入する。
# 素の /clear (sentinel 無し) では何も出力しないので通常挙動を壊さない。
#
# sentinel は claude-refresh.sh が touch する。
set -euo pipefail

# .claude ディレクトリをスクリプト位置から解決 (.claude/hooks/<this>)
HOOK_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLAUDE_DIR="$(dirname "$HOOK_DIR")"
SENTINEL="$CLAUDE_DIR/.resume-pending"

[ -f "$SENTINEL" ] || exit 0
rm -f "$SENTINEL"

cat <<'JSON'
{"hookSpecificOutput":{"hookEventName":"SessionStart","additionalContext":"このセッションは直前にユーザーがリフレッシュを承認してクリアされたものです。新規セッションではありません。resume スキルに従って `.claude/handoff.md` を読み、前セッションの作業を再開してください: Task list を復元 → 次の一手を宣言 → オーケストレーターとして自走。ユーザーへの確認は不要、そのまま着手して構いません。"}}
JSON
