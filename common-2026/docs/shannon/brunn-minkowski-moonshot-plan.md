# T2-E Brunn-Minkowski (entropy form) — Moonshot Plan

Cover-Thomas Theorem 17.9.2 (Brunn-Minkowski inequality, entropy form) を
Lean 4 + Mathlib + Common2026 上で **statement-level pass-through publish** する。

## Context

- 親 roadmap: `docs/textbook-roadmap.md` §T2-E (Tier 2, Ch.17 Inequalities)
- 直接の前駆: T2-D **Entropy Power Inequality** (`EntropyPowerInequality.lean`,
  347 行, 2026-05-19 publish, L-EPI1+L-EPI2+L-EPI3 三本立て pass-through)
- 同 Tier 兄弟: T2-B Parallel Gaussian (`ParallelGaussian.lean`, 381 行) /
  T2-C Shannon-Hartley (`ShannonHartley.lean`, 327 行) / T2-F Fisher info
  (`FisherInfo.lean`, 236 行)
- 関連: T1 LoomisWhitney (`LoomisWhitney.lean`, 444 行, Han/Shearer 経由)
  — Brunn-Minkowski は LW と表裏 (Cover-Thomas Ch.17.9 ↔ Ch.17.4) で
  別系統 (連続側 vs 離散側)、本 plan は連続側を完成させる

## Goal Statement

**Cover-Thomas Theorem 17.9.2** (Brunn-Minkowski, entropy form):

独立な連続 RV `X, Y : Ω → ℝ^n` (`Fin n → ℝ` モデル, density on Lebesgue
measure) に対し、

```
exp ((2/n) · h(X + Y)) ≥ exp ((2/n) · h(X)) + exp ((2/n) · h(Y))
```

を Common2026 `Common2026/Shannon/BrunnMinkowski.lean` に publish。

**系 (Cover-Thomas Cor. 17.9.3)**: 凸体 `A, B ⊂ ℝ^n` (有限正測度) に対し
`X ∼ Uniform A`, `Y ∼ Uniform B` を取ると上記より

```
|A + B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}
```

(Minkowski の Brunn-Minkowski 不等式)。

## Approach

**全体の形**: EPI (T2-D, 347 行, 2026-05-19) と完全 parallel な
**hypothesis pass-through 三本立て** で着地する。EPI が `ℝ` 上の 1-dim
だったのに対し、Brunn-Minkowski は `Fin n → ℝ` 上の `n`-dim。

主鎖は

1. **§A — `entropyPower_nDim` 定義**: `Real.exp ((2/n) · h μ)` 形を
   `Measure (Fin n → ℝ)` 上に定義。EPI が `Real.exp (2 · h μ)` と
   等価係数 `2 = 2/1` だったのに対し、`n`-dim では係数 `2/n` を担う
   (Cover-Thomas Ch.17.9 conventions)。Common2026 には `n`-dim
   differential entropy が未定義のため、本 plan の `entropyPower_nDim`
   は `h : Measure (Fin n → ℝ) → ℝ` を **abstract scalar parameter
   として受け取る**: signature は将来の `differentialEntropy_nDim`
   定義に塞がない形にする。

2. **§B — L-BM1/2/3 撤退 predicates**:
   - `IsBrunnMinkowskiEntropyHypothesis n h X Y P` — EPI の n-dim 形
     結論をそのまま `Prop` 化 (L-EPI3 と同流儀、核心 retreat)
   - `IsUniformOnEntropyLogVolHypothesis n h μ vol` — uniform 分布の
     entropy が `log (vol)` に等しい hypothesis (系で利用)
   - `IsMinkowskiSumMeasurableHypothesis A B` — convex bodies の
     Minkowski sum `A + B` の可測性 hypothesis (系で利用)

3. **§C — 主定理 `brunn_minkowski_entropy_inequality`**: L-BM1 単独で
   `:= h_bm` の 1 行着地。EPI `entropy_power_inequality` と同型。

4. **§D — Convex body 系 `brunn_minkowski_convex_body`**: L-BM1 + L-BM2 +
   L-BM3 を combine。`X ∼ Uniform A`, `Y ∼ Uniform B` のときの h(X), h(Y),
   h(X+Y) を L-BM2 で `log |A|`, `log |B|`, `log |A+B|` に置換、
   L-BM1 で組合せ、`Real.exp_log` で `|A+B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}`
   形に変換。`Real.rpow` の `1/n` 形は `Real.exp ((1/n) log x)` 経由で展開。

5. **§E — 補助 corollary 群**:
   - `entropyPower_nDim_pos` — `Real.exp_pos` で 1 行 full discharge
   - `entropyPower_nDim_nonneg` — `.le` 派生
   - `entropyPower_nDim_eq_exp` — unfold lemma
   - `brunn_minkowski_entropy_inequality_exp_form` — Cover-Thomas
     露出形 (Real.exp 展開)

**EPI との関係**: EPI を **black-box** として hypothesis に塞ぐ
(`docs/shannon/brunn-minkowski-mathlib-inventory.md` の通り、本 plan は
EPI の真の証明本体は触らない)。EPI を `ℝ` 上で持つだけでは `Fin n → ℝ`
には自動的に上がらないため、本 plan の L-BM1 は EPI の n-dim 拡張 (Cover-Thomas
Theorem 17.7.3 の `ℝ^n` 形, 同 textbook で coordinate-wise から導出)
を直接 hypothesis 化する。EPI の `entropy_power_inequality` を `n=1`
で specialize する経路は本 file では取らない (signature 不一致のため;
EPI 経由路は `brunn-minkowski-from-epi-discharge-plan.md` 別 plan に defer)。

**Mathlib-shape 駆動**:
- `entropyPower_nDim` を `Real.exp ((2/n) h μ)` 直書きにし、`Real.exp_pos`
  / `Real.exp_log` の結論形に直結 (EPI と同パターン)。
- L-BM1 predicate は `entropyPower_nDim n h (P.map (X+Y)) ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y)`
  の形で、主定理本体 `:= h_bm` で 1 行着地できる形を取る。
- 系 `brunn_minkowski_convex_body` は `Real.exp ((1/n) log (vol A + vol B)) = (vol A + vol B)^{1/n}`
  を `Real.exp_log` で扱う (`Real.rpow` を直接使うと係数まわりが重くなるため、
  `exp_log` form のみで close)。

**撤退ラインの discharge 想定** (本 file scope 外):
- L-BM1: `brunn-minkowski-from-epi-discharge-plan.md` で EPI を `n`-dim に
  拡張し、coordinate-wise summation で導出 (Cover-Thomas Theorem 17.7.4)。
- L-BM2: `uniform-entropy-log-vol-plan.md` で uniform 分布の `differentialEntropy_nDim`
  が `log (vol)` に等しい事実を discharge。
- L-BM3: convex body theory (`Mathlib.Analysis.Convex.Body`) 経由で
  `Convex A ∧ Convex B → MeasurableSet (A + B)` を導出 (`Convex.measurableSet`
  系 + `Set.add` の可測性)。

## File breakdown

### `Common2026/Shannon/BrunnMinkowski.lean` (予測 ~280-340 行)

- imports: `Common2026.Shannon.DifferentialEntropy`,
  `Common2026.Shannon.EntropyPowerInequality`,
  `Mathlib.Analysis.SpecialFunctions.Exp`,
  `Mathlib.Analysis.SpecialFunctions.Log.Basic`,
  `Mathlib.Probability.Independence.Basic`,
  `Mathlib.Algebra.Group.Pointwise.Set.Basic`,
  `Mathlib.MeasureTheory.Measure.Haar.Basic`
- namespace: `InformationTheory.Shannon.BrunnMinkowski`

| Section | 名前                                                  | 行数予測 |
|---------|------------------------------------------------------|----------|
| §A      | `entropyPower_nDim`, `entropyPower_nDim_pos`,        | ~50      |
|         | `entropyPower_nDim_nonneg`, `entropyPower_nDim_eq_exp` |          |
| §B      | `IsBrunnMinkowskiEntropyHypothesis`,                 | ~70      |
|         | `IsUniformOnEntropyLogVolHypothesis`,                |          |
|         | `IsMinkowskiSumMeasurableHypothesis`                 |          |
| §C      | `brunn_minkowski_entropy_inequality`                 | ~30      |
| §D      | `brunn_minkowski_entropy_inequality_exp_form`,        | ~80      |
|         | `brunn_minkowski_convex_body`                        |          |
| §E      | `entropyPower_nDim_one_eq_entropyPower`,             | ~40      |
|         | `entropyPower_nDim_translation_invariant` (撤退)      |          |

合計予測: ~270 行 ± 50 行。EPI 347 行を下回って着地予想。

## 受入基準 (Definition of Done)

- `lake env lean Common2026/Shannon/BrunnMinkowski.lean` silent (零 error, 零 warning, 零 sorry)
- 主定理 `brunn_minkowski_entropy_inequality` が L-BM1 hypothesis pass-through で着地
- 系 `brunn_minkowski_convex_body` が L-BM1+L-BM2+L-BM3 combination で着地
- `Common2026.lean` に import 追加 (本 plan は親指示で **不変** 制約のため
  追加 import は本 plan scope 外、後続 publish PR に塞ぐ)
- `docs/textbook-roadmap.md` 不変 (本 plan は親指示で **不変** 制約)
