# LZ78 headline: `h_bdd_above` internal discharge サブ計画

**Status**: ✅ CLOSED — `h_bdd_above` は内製 discharge 済 (commit `a1ae108`、独立監査 all OK)。
`h_bdd_above` は headline `lz78_asymptotic_optimality_with_greedy_impl` の
**signature 引数から除去された** (引数は `μ`, `p` のみ)。
**SoT**: コード側 (`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`)。詳細履歴は git。

> **Parent**: `docs/textbook-roadmap.md` §13 Ch.13 LZ78

## 要点 (CLOSED)

- 符号長 def-fix (commit `5d08566`、`lz78GreedyImplEncodingLength` を genuine
  longest-prefix parse 化) 後、per-symbol rate `c · bitLength c |α| / n` は
  `O(1)` (genuine Ziv `c·log c ≤ K·n` 依存)。この定数上界を内製して
  `h_bdd_above` (`IsBoundedUnder (·≤·)`) を proof body 内の `have` で供給し、
  headline の仮説引数から外した (commit `a1ae108`)。
- **crux 訂正**: 計画当初は `Nat.log↔Real.log` bridge を loogle Found 0 ゆえ
  self-build 必須と見ていたが、これは **誤判定**。Mathlib 既存
  `Real.natLog_le_logb` (`Mathlib.Analysis.SpecialFunctions.Log.Base`、前提なし)
  で解決した (self-build 不要)。in-file の bridge `lz78_impl_natLog_mul_log_two_le`
  はこの Mathlib 補題の薄い wrapper。
- M3/M4 scope-out (genuine 研究級壁 `lz78GreedyImpl_achievability_ae` /
  `lz78GreedyImpl_converse_ae`) は本 plan の対象外、撤回しない。`h_bdd_above` を
  内製しても headline は M3/M4 壁経由で sorryAx 依存のまま (= type-check done、
  proof done ではない)。

## Approach (履歴)

`O(1)` per-symbol rate 上界 `lz78_impl_rate_le_const`
(`C = (1 + 8·log(|α|+1)/log 2) + (log₂|α| + 2)`、∀ω∀n で成立、sorryAx-free) を
内製し、`Filter.isBoundedUnder_of` で `h_bdd_above` witness を構成 → headline の
proof body に `have` として埋め込み、仮説引数から除去。Ziv 核
`lz78PhraseStrings_mul_log_le` + `c ≤ n` + Mathlib `Real.natLog_le_logb` のみが
非自明入力。

## 結果 (commit `a1ae108` + 監査 `3e8a550`)

- headline 引数は `μ`, `p` のみ (`h_bdd_above` / `h_bdd_below` 共に proof body の
  `have` で内製)。
- 独立監査 all OK (4 観点 PASS: 非循環 / 非バンドル / 非退化 / sufficiency)、新規
  sorry なし、`lz78_impl_rate_le_const` / bridge は sorryAx-free。
- headline `#print axioms` の sorryAx は M3/M4 壁 2 本経由のみ
  (`lz78GreedyImpl_converse_ae` / `lz78GreedyImpl_achievability_ae`)。
