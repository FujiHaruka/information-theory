#!/usr/bin/env bash
# 教科書サイトを build → site ブランチへ push する。Netlify がそのブランチを配信する。
# 使い方:  ./deploy.sh
#
# - Deno でビルド（数式を MathJax + AMS Euler でサーバー側レンダリング）し dist/ を生成。
# - dist/ の中身だけを載せた孤立ブランチ site に force-push する。Netlify 側は
#   「ビルドコマンド無し・公開ディレクトリ = ルート」で、push された中身をそのまま配信する。
#   認証は origin への push に使う既存の SSH 鍵だけで、デプロイ専用の資格情報は要らない。
# - 履歴は毎回作り直す（site は常に 1 コミット）。1 回ぶんが 25MB あるので、積み上げると
#   public リポジトリの clone が重くなる。
# - push は使い捨ての一時リポジトリから行う。本体の作業ツリーにも .git/index.lock にも
#   触れないようにするためで、git 2.42 以降なら `git worktree add --orphan` でも同じことが
#   できる（このマシンの git は 2.39）。
# - このマシンの /usr/local/bin/node は署名が壊れて起動不可のため Deno を使う。
set -euo pipefail

# 公開 URL。Netlify の Site name を変えたらここも直す。
SITE_URL="https://information-theory-textbook.netlify.app"

DENO="${DENO:-/opt/homebrew/bin/deno}"
[ -x "$DENO" ] || DENO="$(command -v deno || true)"
[ -n "$DENO" ] && [ -x "$DENO" ] || { echo "deno が見つかりません" >&2; exit 127; }

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR"

BRANCH="${SITE_BRANCH:-site}"
REMOTE="$(git remote get-url origin)"
SRC="$(git rev-parse --short HEAD)"

echo "==> build (deno)"
"$DENO" run -A build.mjs

[ -f dist/index.html ] || { echo "dist/index.html がありません（ビルド失敗）" >&2; exit 1; }

echo "==> push to $BRANCH ($(find dist -type f | wc -l | tr -d ' ') files)"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
cp -R dist/. "$STAGE/"
git -C "$STAGE" init -q
git -C "$STAGE" add -A
git -C "$STAGE" commit -q -m "textbook site build (source $SRC)"
git -C "$STAGE" push -q --force "$REMOTE" "HEAD:refs/heads/$BRANCH"

echo "==> done"
echo "$SITE_URL"
