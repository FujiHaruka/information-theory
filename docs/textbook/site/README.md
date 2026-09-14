# 教科書レビュー用 静的サイト (Netlify)

`docs/textbook/` の原稿を **MathJax でサーバー側レンダリング**した静的 HTML に変換し、
Netlify にホストする。数式はビルド時に HTML 化されるためクライアント JS 不要で、
モバイルでも確実に表示される（GitHub ネイティブ math の不安定さを回避）。

書体は 3 系統に分けている。**和文は BIZ UDGothic**（モリサワの UD ゴシック）、
**欧文と数字はシステムのサンセリフ**（SF Pro / Segoe UI）、**数式は AMS Euler**
（OpenType 版の Neo Euler）、**等幅は Inconsolata**。

- 和文を UD ゴシックにしたのは読みやすさのため（明朝・教科書体を試して却下した経緯が git にある）。
  Google Fonts から配信されるので端末を問わず同じ字面になる。プロポーショナル版
  (BIZ UDPGothic) ではなく等幅かな版を採るのは、原稿の句読点が「，．」だからである
  （執筆原則 §9）。プロポーショナルだと，．が詰まって文の切れ目が見えなくなる。
- 欧文と数字を和文書体に任せないのは、和文書体の欧文が数式の欧文と紛れるため。地の文の
  欧文をサンセリフにしておくと、Euler で組まれた数式がどこから始まるかが字面で分かる。
- 桁に収まらないディスプレイ数式は、その数式の中だけが横スクロールする（`displayOverflow: 'scroll'`）。
  MathJax の既定はページごと横に広げるので、狭い画面では本文まで横スクロールになる。
- Euler は MathJax の font extension としてしか配布されていない。数式エンジンが KaTeX では
  なく MathJax なのはそのためである。Euler が持たない大かっこ・根号・黒板太字は土台の
  New Computer Modern が埋める。

> **注意**: このマシンの `/usr/local/bin/node` は署名が壊れていて起動できない
> （SIGKILL）。そのため **Deno** でビルド・デプロイする。

## 使い方

```bash
cd docs/textbook/site
./deploy.sh                           # build → site ブランチへ push。末尾に公開 URL が出る
deno run -A build.mjs                 # ビルドだけ（→ dist/）
deno run -A build.mjs --audit-refs    # 参照・形式化ポインタの取りこぼしを目で確かめる
./vocab.ts <章スラッグ>                # 語彙の点検。新しい節を書いたら回す
```

ビルドは原稿の不備を `warn:` として挙げる。**warn 0 件を保つ**。何がなぜ warn なのかは、
その検査を書いた `build.mjs` のコメントと、そこが指す執筆原則の節が持つ。

## どこに何があるか

この README はポインタだけを置く。中身を写すと、写した先が変わったときに README だけが
古いまま残る。

| 知りたいこと | SoT |
|---|---|
| 原稿の書き方（前方参照・環境タグ・番号と相互参照・形式化ポインタ・数式・日本語） | [`.claude/rules/textbook-writing.md`](../../../.claude/rules/textbook-writing.md) |
| ビルド対象の章と節、その順序（目次と前後ナビはこの順）、章の足し方 | `build.mjs` の `chapters` 配列 |
| 各検査・自動リンクの挙動と、そうした理由 | `build.mjs` の該当節のコメント |
| 用語の採否と、その語を採った理由 | `terminology.mjs` |
| 数式エンジンと書体の組み立て | `build.mjs` の「数式エンジン」節のコメント |
| デプロイの仕組み（なぜ孤立ブランチに force-push するのか） | `deploy.sh` の冒頭コメント |
| 公開 URL | `deploy.sh` の `SITE_URL` |
| 章立てと進捗の管理 | [`docs/textbook-roadmap.md`](../../textbook-roadmap.md) |

## 公開の仕組み

`deploy.sh` はビルド結果 `dist/` の中身だけを孤立ブランチ **`site`** に force-push する。
Netlify はそのブランチを本番ブランチとして見ており（ビルドコマンド無し・公開ディレクトリ =
ルート）、push された中身をそのまま配信する。デプロイ専用の資格情報は無く、認証は origin へ
push できる SSH 鍵だけである。

`site` の履歴は毎回作り直す（常に 1 コミット）。1 回ぶんが 25MB あるので、積み上げると
clone が重くなる。

Netlify 側の設定は UI が持つ。ブランチ・ビルドコマンド・公開ディレクトリ・サイト名を変えたら、
`deploy.sh` の `BRANCH` と `SITE_URL` も合わせる。

## 公開範囲の注意

デプロイしたサイトは **誰でも閲覧できる公開ページ**になる。リポジトリ自体も public なので
原稿はいずれにせよ公開されるが、サイトのほうは URL を知っていれば誰でも読める。
