#!/usr/bin/env bash
# セッションリフレッシュを実行する。
#
#   1. sentinel (.resume-pending) を立てる
#        → 直後の /clear で SessionStart フックが自動再開を注入する
#   2. tmux 内なら /clear をペインに送る (現ターン終了後 idle になってから発火)
#      tmux 外なら sentinel だけ立てて、ユーザーに手動 /clear を促す
#
# 呼び出し元:
#   - Claude (handoff スキル) が Bash ツールで実行 → $TMUX_PANE を継承
#   - tmux keybind (任意) が `#{pane_id}` を $1 で渡して実行
set -euo pipefail

HOOK_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLAUDE_DIR="$(dirname "$HOOK_DIR")"
touch "$CLAUDE_DIR/.resume-pending"

# 対象ペイン: 明示引数優先、無ければ継承した $TMUX_PANE
PANE="${1:-${TMUX_PANE:-}}"

if [ -n "${TMUX:-}" ] && [ -n "$PANE" ] && command -v tmux >/dev/null 2>&1; then
  # 現ターンが終わって prompt が idle に戻ってから /clear を送る。
  # 親 (Bash ツール) をブロックしないよう detach + fd を閉じる。
  ( sleep 2; tmux send-keys -t "$PANE" '/clear' Enter ) >/dev/null 2>&1 &
  disown 2>/dev/null || true
  echo "REFRESH_SCHEDULED"
else
  echo "REFRESH_PENDING_MANUAL_CLEAR"
fi
