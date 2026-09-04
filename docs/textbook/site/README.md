# 教科書レビュー用 静的サイト (surge.sh)

`docs/textbook/` の原稿を **MathJax でサーバー側レンダリング**した静的 HTML に変換し、
surge.sh にホストする。数式はビルド時に HTML 化されるためクライアント JS 不要で、
モバイルでも確実に表示される（GitHub ネイティブ math の不安定さを回避）。

書体は 3 系統に分けている。**和文は教科書体**（UD デジタル教科書体 → 游教科書体 →
Klee One の順に端末にあるものを拾う）、**欧文と数字は Palatino**、**数式は AMS Euler**
（OpenType 版の Neo Euler）、**等幅は Inconsolata**。

- 和文を教科書体にしたのは読みやすさのため。ただし教科書体の欧文は手書きに寄っていて、
  1 が l に、0 が o に見える（「確率 1 でとる」「1948 年」が読めない）ので、欧文と数字は
  教科書体に任せず Palatino を先に置く。和文には無い字だけを拾うので和文は教科書体のまま残る。
- Palatino は Euler と同じ Zapf の設計で、LaTeX の eulervm + mathpazo と同じ組み合わせになる。
- Euler は MathJax の font extension としてしか配布されていない。数式エンジンが KaTeX では
  なく MathJax なのはそのためである。Euler が持たない大かっこ・根号・黒板太字は土台の
  New Computer Modern が埋める。

> **注意**: このマシンの `/usr/local/bin/node` は署名が壊れていて起動できない
> （SIGKILL）。そのため **Deno** でビルド・デプロイする。

## 使い方

```bash
cd docs/textbook/site
./deploy.sh                           # build → surge。末尾に公開 URL が出る
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
| デプロイの詳細（ログインの経路・ドメインの決まり方） | `deploy.sh` の冒頭コメント |
| 公開先ドメインと認証情報 | `surge-credentials.txt` |
| 章立てと進捗の管理 | [`docs/textbook-roadmap.md`](../../textbook-roadmap.md) |

## 公開範囲の注意

surge にデプロイしたサイトは **誰でも閲覧できる公開ページ**になる（URL を知っていれば
アクセス可能）。リポジトリはプライベートだが、ここに置いた原稿は公開される点に留意する。
認証情報 `surge-credentials.txt` は平文で git 管理している（ユーザー明示了承）。
