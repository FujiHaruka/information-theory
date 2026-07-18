# コーディング規約 (Mathlib 由来)

このリポジトリの Lean コードのスタイル / 命名規約。**Mathlib 公式の規約を出典とし、本プロジェクトに適用できる形に取捨選択した** もの。

## 出典

- スタイル: <https://leanprover-community.github.io/contribute/style.html>
- 命名: <https://leanprover-community.github.io/contribute/naming.html>
- 機械規則の実体: `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean` / `TextBased.lean`（Mathlib 内の style linter 群。各規則は subjective として global では disabled だが、Mathlib 本体には適用される）

## このリポジトリでの位置づけ

- **`CLAUDE.md` が上位**。import 方針 / 検証 honesty / skeleton-driven 開発 / docs hygiene など「ワークフロー」規約は `CLAUDE.md` が SoT。本ディレクトリはそこが扱わない **Lean コードの見た目（命名・レイアウト・タクティク作法）** を埋める。両者が衝突したら `CLAUDE.md` が勝つ。
- **強制ではなく指針**。Mathlib 同様これらの多くは subjective であり、CI で機械強制はしていない（本プロジェクトに Mathlib の style linter は組み込まれていない）。新規コードを書くとき / レビューするときの共通の物差しとして使う。

## 構成

| ファイル | 内容 |
|---|---|
| [`lean-style.md`](lean-style.md) | フォーマット・レイアウト・タクティク作法・normal form・透明性 |
| [`naming.md`](naming.md) | 命名規約（大文字小文字・定理名の組み立て方・記号→語の対応表） |
| [`docstrings.md`](docstrings.md) | docstring 規約（宣言/module docstring の形・本リポジトリの乖離点・固有タグとの同居） |
| [`module-structure.md`](module-structure.md) | モジュール分割・ディレクトリ構造（ディレクトリ=主題・Defs/Basic 役割・import DAG・`Shannon/` 現状診断とターゲット形） |

## Mathlib 規約の採否一覧

本プロジェクトの実態（233 ファイル）に照らした採否。「読み替え」「非適用」は理由を明記する。

### 採用（adopt）— そのまま適用

- 1 行 100 文字以内 / 1 ファイル 1500 行以内 / 1 証明本体 200 行以内（目安。超えたら `have` ブロック等を `private` 補助補題へ）
- `:` `:=` 中置演算子の両側にスペース、binder の後にスペース
- 宣言内の空行は避ける（区切りたいならコメント）
- インデントは 2 スペース単位、複数行に渡る型シグネチャの継続行は 4 スペース
- すべての引数の型を明示する（推論可能でも書く）
- `λ` ではなく `fun`、`=>` ではなく `↦`、超単純関数は `·`（既に実態と一致: `fun` 211 / `λ` 23 ファイル）
- `by` は直前の行末に置く（単独行にしない）、サブゴールは focusing dot `·`
- `$` ではなく `<|`、ネストした括弧より `<|` / `|>`
- `calc` のレイアウト（関係記号を揃える、`_` を左寄せ）
- normal form を 1 つに固定する（`s.Nonempty` 等）。仮定は `x ≠ ⊥`、結論は `⊥ < x` を好む
- 定義の透明性（`def`=semireducible / `abbrev`=reducible）を意識した API 境界設計
- コメント種別の使い分け（`/-! -/` 見出し / `/- -/` 技術メモ / `--` 短文 / `/-- -/` docstring）
- docstring 規約一式（[`docstrings.md`](docstrings.md)）。数学的意味を述べる完全文・バッククォート識別子・宣言 docstring の継続行は字下げしない・named theorem のみ太字
- 命名規約一式（[`naming.md`](naming.md)）。既に実態と一致（例: `exp_decay_N_of_pos` の `_of_`、`DotEq` の UpperCamelCase）
- モジュール分割・ディレクトリ構造（[`module-structure.md`](module-structure.md)）。ディレクトリ=主題・階層は複合ファイル名でなくディレクトリで・Defs/Basic 役割・import は DAG（循環禁止）・1 ファイル 1500 行。`Shannon/` のフラット集中（205/233）は要改善で、現状診断とターゲット形を所収

### 読み替え（adapt）— 修正して適用

- **import**: Mathlib は「全 import を public/通常でグループ化しアルファベット順」。本プロジェクトは `import Mathlib` 禁止・必要モジュールのみ・`InformationTheory.lean` への登録（→ `CLAUDE.md` Import Policy が SoT）。**グループ内アルファベット順だけ軽い指針として採用**、残りは `CLAUDE.md` に従う。
- **module docstring**: Mathlib は copyright header の直後を必須とする。本プロジェクトは copyright header を置かない（下記）ので、**ファイル先頭の import 群の直後に `/-! # … -/` を置く**（既に実態と一致）。本文は英語で書く。
- **English / American English**: Mathlib は散文・綴りを米英語に統一。本プロジェクトも将来の Mathlib PR を見据え、**識別子も docstring / コメントの散文も英語・米綴り**に統一する（旧方針「散文は日本語可」から 2026-06-13 転換。移行 → [`../docstring-tidyup-plan.md`](../docstring-tidyup-plan.md)）。内部の plan / handoff（`docs/**/*.md`）は作業言語として日本語のままでよい。

### 非適用（skip）— 本プロジェクトには課さない。理由付き

- **Copyright header（Apache ライセンスヘッダ + `Authors:`）**: Mathlib は全ファイル必須だが、本プロジェクトは個人形式化リポジトリで実態 2/233。**課さない**。
- **`module` / `public import` モジュールシステム**: Mathlib の新モジュール機構。本プロジェクトは旧 import 方式（実態 0/233）。**課さない**。
- **`@[deprecated (since := "YYYY-MM-DD")]` の日付・`to_additive` 連動 deprecation**: Mathlib の後方互換運用フロー。個人リポジトリでは履歴は git で足り、**課さない**（必要時に通常の `@[deprecated]` を使う程度）。
- **`!bench` ベンチマーク基盤 / PR title linter / Mathlib CI 固有 linter**: Mathlib インフラ依存。**非適用**。
