# 教科書パイロット 静的サイト (surge.sh)

公開 URL: https://common2026-ch2.surge.sh （デプロイ済み）

`docs/textbook/*.md` を **KaTeX でサーバー側レンダリング**した静的 HTML に変換し、
surge.sh にホストする。数式はビルド時に HTML 化されるためクライアント JS 不要で、
モバイルでも確実に表示される（GitHub ネイティブ math の不安定さを回避）。

認証情報は `surge-credentials.txt`（平文・git 管理、ユーザー明示了承）。

> **注意**: このマシンの `/usr/local/bin/node` は署名が壊れていて起動できない
> （SIGKILL）。そのため **Deno** でビルド・デプロイする。

## ビルド

```bash
cd docs/textbook/site
deno run -A build.mjs       # → dist/index.html を生成
```

ビルド対象ページは `build.mjs` の `pages` 配列で管理（現状 `ch02-entropy.md`
のみ）。新しい章を足すときはここに `{ slug, title, src }` を追加する。

## デプロイ (surge)

build と deploy を 1 つにしたスクリプトがある。いつでもこれ一発：

```bash
cd docs/textbook/site
./deploy.sh
```

`deploy.sh` の動作：
- Deno で `build.mjs` を実行し `dist/` を再生成。
- surge にデプロイ。**ログイン済み (`~/.netrc`) なら非対話**。未ログインなら
  `surge-credentials.txt` の email/password で自動ログイン（expect 経由）。
- デプロイ先ドメインは `surge-credentials.txt` の `domain=` で決まる
  （現状 common2026-ch2.surge.sh）。変えたいときはこの行を編集。

成功すると末尾に公開 URL を表示する。

> 手動で叩く場合（スクリプトを使わないとき）:
> `deno run -A npm:surge ./dist <domain>` 。初回はログイン済みでなければ
> email/password を聞かれる。`SURGE_LOGIN` / `SURGE_TOKEN` 環境変数でも可。

## 公開範囲の注意

surge にデプロイしたサイトは **誰でも閲覧できる公開ページ**になる
（URL を知っていればアクセス可能）。リポジトリはプライベートだが、ここに置いた
原稿は公開される点に留意する。
