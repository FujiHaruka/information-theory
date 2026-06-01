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

ビルド対象ページは `build.mjs` の `pages` 配列で管理（現状 `ch02-entropy-rewrite.md`
のみ）。新しい章を足すときはここに `{ slug, title, src }` を追加する。

## デプロイ (surge)

surge は初回にメール/パスワードでアカウント作成・ログインが必要（対話入力）。
**この最終コマンドは自分のターミナルで実行する**：

```bash
cd docs/textbook/site
deno run -A npm:surge ./dist common2026-ch2.surge.sh
```

- 初回は email / password を聞かれる（アカウントが無ければその場で作成される）。
- ドメイン `common2026-ch2.surge.sh` は好きな名前に変えてよい（surge 全体で一意）。
- 2 回目以降は同じコマンドで再デプロイ（上書き）。
- ログイン済みなら非対話。トークン運用なら `SURGE_LOGIN` / `SURGE_TOKEN` 環境変数。

公開後の URL: `https://common2026-ch2.surge.sh`（指定したドメイン）。

## 公開範囲の注意

surge にデプロイしたサイトは **誰でも閲覧できる公開ページ**になる
（URL を知っていればアクセス可能）。リポジトリはプライベートだが、ここに置いた
原稿は公開される点に留意する。
