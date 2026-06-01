#!/usr/bin/env bash
# 教科書パイロットサイトを build → surge にデプロイする。
# 使い方:  ./deploy.sh
#
# - Deno でビルド（数式を KaTeX でサーバー側レンダリング）し dist/ を生成。
# - surge にデプロイ。ログイン済み (~/.netrc) なら非対話。未ログインなら
#   surge-credentials.txt の email/password で自動ログイン（expect 経由）。
# - このマシンの /usr/local/bin/node は署名が壊れて起動不可のため Deno を使う。
set -euo pipefail

DENO="${DENO:-/opt/homebrew/bin/deno}"
[ -x "$DENO" ] || DENO="$(command -v deno || true)"
[ -n "$DENO" ] && [ -x "$DENO" ] || { echo "deno が見つかりません" >&2; exit 127; }

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR"

CRED="$DIR/surge-credentials.txt"
[ -f "$CRED" ] || { echo "$CRED がありません" >&2; exit 1; }
EMAIL=$(grep '^email='    "$CRED" | cut -d= -f2-)
PW=$(   grep '^password=' "$CRED" | cut -d= -f2-)
DOMAIN=$(grep '^domain='  "$CRED" | cut -d= -f2-)
[ -n "$DOMAIN" ] || { echo "domain が surge-credentials.txt に無い" >&2; exit 1; }

echo "==> build (deno)"
"$DENO" run -A build.mjs

echo "==> deploy to $DOMAIN"
EXP="$(mktemp)"
trap 'rm -f "$EXP"' EXIT
cat > "$EXP" <<'EXPEOF'
set timeout 300
set email  [lindex $argv 0]
set pw     [lindex $argv 1]
set domain [lindex $argv 2]
set deno   [lindex $argv 3]
set ok 0
spawn $deno run -A npm:surge ./dist $domain
# ログイン済みなら email/password プロンプトは出ず直接 Success に進む。
# 未ログインなら email: / password: に答える。両対応。
expect {
  -re "email:"     { send -- "$email\r"; exp_continue }
  -re "password:"  { send -- "$pw\r";    exp_continue }
  -re "Success!"   { set ok 1 }
  -re "Aborted|denied|Forbidden|not available" { set ok 0 }
  timeout          { puts "\nTIMEOUT"; exit 2 }
  eof              { }
}
catch { expect eof }
exit [expr {$ok ? 0 : 1}]
EXPEOF

if expect "$EXP" "$EMAIL" "$PW" "$DOMAIN" "$DENO"; then
  echo "==> done"
  echo "https://$DOMAIN"
else
  rc=$?
  echo "==> deploy failed (rc=$rc)" >&2
  exit "$rc"
fi
