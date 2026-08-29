# `.claude/rules/`

このリポジトリの**成果物ごとの執筆・作成原則**を置く。ワークフロー規約（検証 honesty /
skeleton-driven 開発 / docs hygiene など）は `CLAUDE.md` が SoT で、そこと衝突したら
`CLAUDE.md` が勝つ。

| ファイル | 対象 |
|---|---|
| [`textbook-writing.md`](textbook-writing.md) | `docs/textbook/` の教科書原稿（読者前提・前方参照・章節構成・決まり文句・数式記法・形式化ポインタ・日本語の書き方） |

Lean コードの見た目（命名・docstring・モジュール分割・スタイル）は別系統で、
[`docs/rules/`](../../docs/rules/README.md) が SoT。

**育て方**: 各ファイルの先頭に「この文書を育てる」節を置き、作業中に下した判断・レビュー指摘を
その場で 1 項追加してから作業に戻る。暗黙のまま成果物に埋めた判断は次の章／次のファイルで
別の判断になる。
