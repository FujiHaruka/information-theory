# 教科書レビュー用 静的サイト (surge.sh)

公開 URL: https://common2026-ch2.surge.sh （デプロイ済み・全章の目次がトップ）

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

ビルド対象は `build.mjs` の `chapters` 配列で管理する。章には 2 つの形がある。

- **1 章 1 ページ**（第2〜5章）— `{ slug, num, title, src, status }` を足す。
- **節ごとにページを分ける**（第1章）— `src` の代わりに `intro`（章トビラの本文）と
  `sections` 配列を持たせる。各節は `{ slug, num, title, src }`。原稿は
  `docs/textbook/ch01/` のように章ごとのディレクトリに 1 節 1 ファイルで置く。

目次 (`index.html`)・章トビラの節一覧・全ページを貫く前後ナビゲーションは、いずれも
この配列順から自動生成される（節分割された章は「章トビラ → 各節」の順に展開される）。

生成物は目次 `dist/index.html` + ページごとの `dist/<slug>.html`。

### 節ページの書き方

節を独立したページとして読めるよう、各節ファイルは **文脈と動機の段落から始める**
（`## 動機` のような見出しは置かない）。ファイル内の見出しレベルは、節タイトルが `#`、
その下位が `##`。

### 数式記法について

原稿には 2 通りの数式記法が混在している。

- `ch01/*.md` — `$ ... $` / `$$ ... $$`
- `ch02` 以降 — LaTeX 括弧デリミタ `\( ... \)` / `\[ ... \]`

markdown-it-katex は `$` 記法しか解さないため、`build.mjs` の `normalizeMath()` が
括弧デリミタを `$` 記法へ寄せてから渡している。コードフェンスとインラインコードの
中身は退避して保護するので、Lean コードは変換の影響を受けない。

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
