# Lean スタイル規約

Mathlib スタイルガイド（<https://leanprover-community.github.io/contribute/style.html>）から本プロジェクトに適用する分。採否の全体像は [`README.md`](README.md)。命名は [`naming.md`](naming.md)。

## ファイル構成

```lean
import InformationTheory.Meta.EntryPoint   -- 必要なものだけ。import Mathlib は禁止 (CLAUDE.md)
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- グループ内はアルファベット順を指針とする

/-!
# ファイルのタイトル

何を定義/証明するか、主要な定理、表記法、設計判断の要約。
本文は 2 スペースインデント（markdown 要件）。英語で書く。
-/
```

- **copyright header は置かない**（本プロジェクトの方針 → `README.md`）。Mathlib と違いここがファイル先頭。
- module docstring `/-! … -/` は import 群の直後に置く。
- import の方針（何を import するか、`InformationTheory.lean` への登録）は `CLAUDE.md` Import Policy が SoT。

## 行・空白

- **1 行 100 文字以内。1 ファイル 1500 行以内。**
- **1 証明本体 200 行以内（目安）。** 超えたら意味のあるまとまり（`have` / `let` ブロック、独立したケース）を `private` 補助補題へ切り出す。厳格な上限ではなく「分割を検討せよ」のシグナル（Mathlib に機械 linter は無いが、長大な証明を補題へ分けるのは慣習）。切り出した補助補題は internal supporting lemma なので bare（docstring 不要、名前に意味を持たせる → [`docstrings.md`](docstrings.md) / [`naming.md`](naming.md)）。
- `:` `:=` および中置演算子の **両側にスペース**。binder の後にスペース。
- 演算子は **行末に置いて改行**する（次行頭に演算子を置かない）。
- `rw` / `simp` の引数前にスペース: `rw [h]`、左向き矢印 `rw [← add_comm a b]`。
- **宣言内の空行は避ける**（lint 対象）。区切りたいときはコメントで。宣言間は 1 空行。

## インデント

- 既定は **2 スペース単位**。「インデントする」= 2 スペース足す。
- top-level 宣言は flush-left。`namespace` / `section` の中身はインデントしない。
- 証明は定理文の **2 スペース下**。
- 定理文が複数行に渡るときは、**継続行を 4 スペース**下げる（証明本体は 6 ではなく 2 のまま）。
- 証明項が複数引数を取るときは、各引数を改行して 2 スペースずつ下げる。
- 括弧を孤立させない（引数と一緒に保つ）。

## 宣言

- **すべての引数の型を明示**する（Lean が推論できても書く）。戻り値型も明示。
- 短い宣言は 1 行可: `def square (x : Nat) : Nat := x * x`
- **コロンの左に引数を置く方を好む**（`∀` / `→` より）。例: `example (n : ℝ) (h : 1 < n) : 0 < n := by linarith`。本体でパターンマッチするときはコロンの右でも可。
- `instance` は `where` 構文で波括弧を避ける。各フィールドに docstring。

## 関数・binder

- **`λ` ではなく `fun`**。`fun (x : α) ↦ …` のように binder 型を明示。
- **`=>` ではなく `↦`**（`\mapsto`）。
- 超単純関数は中黒 `·`: 二乗は `(· ^ 2)`。

## タクティク (`by` ブロック)

- **`by` は直前の行末**に置く（単独行にしない）。中身はインデント。
- サブゴールは focusing dot `·`（`\.`）で、dot 自体はインデントしない。`case` で名前付きにしてもよい。
- 原則 **1 行 1 タクティク**。短い列はセミコロンで 1 行可: `cases bla; clear h` / `induction n; simp`。
- term モードと tactic モードの混在は可。
- 自明なゴールは `swap` / `pick_goal` で先に閉じ、無駄なインデントを避ける。
- **終端 `simp` を squeeze しない**（ゴールを閉じる / flexible タクティク（`ring` `field_simp` `aesop`）だけが続く `simp`）。性能問題や proof 破壊が無い限り `simp only […]` に展開しない（展開形は長く、lemma 名変更で壊れやすい）。

## `have` のレイアウト

- 短い justification は 1 行: `have h1 : n ≠ k := ne_of_lt h`
- 長い term justification は次行を 2 スペース下げる。
- tactic justification は長短に関わらず `by` を同じ行に置き、本体を次行以降にインデント。

## 演算子 `<|` / `|>`

- `$` は禁止（Mathlib では `<|` のシノニムだが使わない）。**`<|` を使う**。
- ネストした括弧より `<|`（右側全部を括る）/ `|>`（左側全部を括る）を好む。
  - `foo a |>.bar b |>.baz` は `((foo a).bar b).baz` の代わり。
  - `le_antisymm hxy <| le_of_forall_pos_le_add <| by …`

## `calc`

- `calc` は計算開始の前の行に置く。計算行はインデント。
- 関係記号（`=` `≤` 等）を行間で **揃える**。継続用の `_` を左寄せ。
- `:=` の整列は必須ではない（短ければ揃えてよい）。

## normal form（正規形）

- 同値な言明は **1 つの標準形に固定**する。例: `s.Nonempty`（「部分集合が空でない」ではなく）、`(a : Option α)`（`Some a` ではなく）。他の形は simp lemma で正規形に変換。
- **下端 `⊥` / 上端 `⊤`**:
  - 仮定は `hne : x ≠ ⊥` を好む（チェックが楽）。
  - 結論は `hlt : ⊥ < x` を好む（より強い）。
  - `hlt → hne` は簡単（`hlt.ne` / `hlt.ne'`）だが逆は長い。`⊤` も同様。

## 定義の透明性

- `def` は **semireducible**（`rw` / `simp` で通常展開されない。`rfl` / `erw` で展開可）。
- `abbrev` は **reducible**（常に展開、かつ `@[inline]`）。
- semireducible な定義に API を生やすときは `instance : Foo myDef := inferInstanceAs (Foo underlying)`、simp lemma は underlying 項で再利用。
- 完全に封じたい境界は `irreducible` より **type synonym structure**。`irreducible_def` はプロファイルで必要性が示せたときのみ。

## コメント・docstring

- `/-! … -/`: 見出し / セクション区切り（自動生成 doc に載る）。
- `/- … -/`: 技術コメント（TODO / 実装メモ）、証明中コメント。
- `--`: 短い / 行内コメント。
- `/-- … -/`: docstring。複数行でも継続行をインデントしない。
- 散文も**識別子も英語・米綴り**（→ [`naming.md`](naming.md)）。コード表面（`.lean`）の docstring / コメントは英語に統一。
