# LZ78 headline: `h_bdd_above` internal discharge サブ計画

**Status**: 🚧 OPEN — `h_bdd_above` は現 headline で genuinely open。
**SoT**: コード側 (`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean` の
`lz78_asymptotic_optimality_with_greedy_impl` 仮説引数)。詳細履歴は git。

> **Parent**: `docs/textbook-roadmap.md` §13 Ch.13 LZ78

## 要点

- 符号長 def-fix (commit `5d08566`、`lz78GreedyImplEncodingLength` を genuine
  longest-prefix parse 化) 後、headline は per-symbol rate
  `c · bitLength c |α| / n` の `IsBoundedUnder (·≤·)` を `h_bdd_above` 仮説で取る。
  def-fix で rate は `O(1)` (genuine Ziv `c·log c ≤ K·n` 依存) なので
  `h_bdd_above` は **TRUE-satisfiable な honest regularity precondition**
  (core-reconstruction test PASS、limit 値 entropyRate の情報を運ばないので
  load-bearing でない)。
- **ただし現 headline では discharge 未着手 = genuinely open**。internal 化には
  `c · bitLength c |α| / n ≤ 8·log(|α|+1)/log 2 + log₂|α| + 2` を示す必要があり、
  これは genuine Ziv 上界 (`lz78PhraseStrings_mul_log_le`、`ℕ`-値) を per-symbol
  rate (`ℝ`-値) の bound に翻訳する **`Nat.log↔Real.log` bridge** を要する。
  loogle Found 0 (`Nat.log` ↔ `Real.log` の直接 bridge 補題は Mathlib 不在) で
  self-build が要る点が discharge の crux。
- M3/M4 scope-out (genuine 研究級壁 `lz78GreedyImpl_achievability_ae` /
  `lz78GreedyImpl_converse_ae`) は本 plan の対象外、撤回しない。`h_bdd_above` を
  内製できても headline は M3/M4 壁経由で sorryAx 依存のまま (= type-check done、
  proof done ではない)。

## Approach

`Nat.log`-値の genuine Ziv 上界を `Real.log` per-symbol rate bound に持ち上げる
bridge 補題を self-build する。`bitLength c |α| = log₂(c+1) + log₂|α| + 2` の
`ℕ → ℝ` キャスト + `lz78PhraseStrings_mul_log_le` (`c·log c ≤ K·n`) から
`c · bitLength c |α| / n` の漸近 `O(1)` 上界を出し、`h_bdd_above` を内製
(`Filter.IsBoundedUnder` witness 構成)。

## Steps

1. `Nat.log 2 m` と `Real.logb 2 m` (= `Real.log m / Real.log 2`) の bridge 補題
   を self-build (`Nat.log` の単調性 + `Real.log` 単調性、`Nat.log_le` 系)。
   loogle Found 0 なので新規。
2. per-symbol rate `c · bitLength c |α| / n` の `ℝ`-値漸近上界を
   `lz78PhraseStrings_mul_log_le` + step 1 で導出。
3. `Filter.IsBoundedUnder (·≤·) atTop (rate)` の witness を構成し、headline の
   `h_bdd_above` を内部で供給 (引数から外す or `∀ᵐ` で内製)。
4. 検証: `lake env lean GreedyParsingImpl.lean` silent + `h_bdd_above` 削除後の
   `#print axioms` が M3/M4 壁 2本のみ sorryAx 依存 (h_bdd_above 由来の追加依存なし)。

## 注意

- 本 plan は **proof done を進めない** (M3/M4 壁が残る)。`h_bdd_above` を仮説から
  消して headline の表面積を縮小する honesty hygiene + precondition 内製。
- step 1 の bridge は LZ78 外でも再利用しうる汎用補題 (`Nat.log`↔`Real.log`)。
