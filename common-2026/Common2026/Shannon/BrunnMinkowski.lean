import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.EntropyPowerInequality
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# T2-E: Brunn-Minkowski inequality (entropy form, Cover-Thomas Theorem 17.9.2)

独立な連続 `Fin n → ℝ`-値確率変数 `X, Y` に対する **Brunn-Minkowski
(entropy form)** :

    `exp ((2/n) · h(X + Y)) ≥ exp ((2/n) · h(X)) + exp ((2/n) · h(Y))`,

および凸体特殊化 `|A + B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}` を hypothesis
pass-through 形で publish。Cover-Thomas Ch.17.9 の頂点で EPI (T2-D,
`EntropyPowerInequality.lean`) と表裏。

## Roadmap (per `docs/shannon/brunn-minkowski-moonshot-plan.md`)

* §A — `entropyPower_nDim` 定義 + 基本 positivity
* §B — L-BM1 + L-BM2 + L-BM3 predicate 定義
* §C — 主定理 `brunn_minkowski_entropy_inequality` (L-BM1 適用)
* §D — Cover-Thomas 露出形 + 凸体 specialization
* §E — 補助 corollary 群

## 撤退ライン (本 file で発動)

Brunn-Minkowski entropy 形そのもの (EPI の n-dim 拡張 +
coordinate-wise summation) は Mathlib **完全不在**
(`loogle "BrunnMinkowski"` で unknown identifier、`loogle "Brunn"` で
unknown identifier)。本 file では Cover-Thomas Theorem 17.9.2 の
textbook 完全形を signature に保持しつつ、主定理本体は L-BM1 単独で
着地する **L-BM1 + L-BM2 + L-BM3 三本立て hypothesis pass-through pattern**
を採用する (T2-D EPI / T2-B / T2-C と同流儀)。

* **L-BM1 (Brunn-Minkowski entropy hypothesis, 核心 retreat)**:
  `IsBrunnMinkowskiEntropyHypothesis n h X Y P : Prop` を Brunn-Minkowski
  結論そのものとし、主定理本体は `:= h_bm` で着地。Discharge plan
  `brunn-minkowski-from-epi-discharge-plan.md` (起草済、本実装未着手) で
  EPI の n-dim 拡張 + Cover-Thomas Theorem 17.7.4 経路で導出する想定。
* **L-BM2 (uniform = log volume hypothesis)**:
  `IsUniformOnEntropyLogVolHypothesis n h μ vol : Prop` で uniform
  分布の `n`-dim differential entropy が `log vol` に等しい事実を
  hypothesis 化。系 (convex body) で利用、本主定理では未使用。
* **L-BM3 (Minkowski sum measurability hypothesis)**:
  `IsMinkowskiSumMeasurableHypothesis A B : Prop` で convex bodies
  `A, B ⊂ Fin n → ℝ` の Minkowski sum `A + B` の可測性を hypothesis 化。

## Mathlib-shape-driven Definitions

* `entropyPower_nDim n h μ := Real.exp ((2 / n) * h μ)` は `Real.exp_pos`
  / `Real.exp_log` の結論形に直結 (EPI と同パターン)。
* L-BM1 形 `IsBrunnMinkowskiEntropyHypothesis` は Brunn-Minkowski 結論
  を `Prop` 化し、主定理本体を `:= h_bm` の 1 行で着地させる (EPI L-EPI3
  と同流儀)。
* Common2026 には `Measure (Fin n → ℝ)` 上の differential entropy
  (`differentialEntropy_nDim`) が未定義のため、本 file の `entropyPower_nDim`
  は entropy scalar `h : Measure (Fin n → ℝ) → ℝ` を **abstract parameter**
  として受け取る。これにより将来の `differentialEntropy_nDim` 定義に
  signature を塞がない pass-through 形を保つ。

## 主シグネチャ

* `entropyPower_nDim` — §A 定義
* `entropyPower_nDim_pos`, `entropyPower_nDim_nonneg`,
  `entropyPower_nDim_eq_exp` — Tier 0 補助
* `IsBrunnMinkowskiEntropyHypothesis` /
  `IsUniformOnEntropyLogVolHypothesis` /
  `IsMinkowskiSumMeasurableHypothesis` — §B L-BM1/2/3 predicates
* `brunn_minkowski_entropy_inequality` — §C 主定理 (L-BM1 適用形)
* `brunn_minkowski_entropy_inequality_exp_form` — Cover-Thomas 露出形
* `brunn_minkowski_convex_body` — §D 系 (L-BM1+L-BM2+L-BM3 combination)
-/

namespace InformationTheory.Shannon.BrunnMinkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise

/-! ## §A — `entropyPower_nDim` 定義 + 基本性質 -/

/-- **`n`-dimensional entropy power** of a measure `μ` on `Fin n → ℝ`,
parameterised by an abstract differential entropy scalar
`h : Measure (Fin n → ℝ) → ℝ`.

`entropyPower_nDim n h μ := exp ((2/n) · h μ)`.

Cover-Thomas Ch.17.9 における `n`-dim entropy power の定義
(`N(X) := (2πe)^{-1} · exp ((2/n) h(X))` の係数を除いた本体)。EPI
(`EntropyPowerInequality.entropyPower`) は `n = 1` 限定の `exp (2 h(μ))`
に等価。Mathlib-shape-driven: `h` を abstract scalar として受け取ることで
Common2026 未定義の `differentialEntropy_nDim` 待ちで本 plan を塞がない。 -/
noncomputable def entropyPower_nDim
    (n : ℕ) (h : Measure (Fin n → ℝ) → ℝ) (μ : Measure (Fin n → ℝ)) : ℝ :=
  Real.exp ((2 / n) * h μ)

/-- The `n`-dim entropy power is strictly positive. -/
theorem entropyPower_nDim_pos (n : ℕ) (h : Measure (Fin n → ℝ) → ℝ)
    (μ : Measure (Fin n → ℝ)) :
    0 < entropyPower_nDim n h μ :=
  Real.exp_pos _

/-- The `n`-dim entropy power is non-negative. -/
theorem entropyPower_nDim_nonneg (n : ℕ) (h : Measure (Fin n → ℝ) → ℝ)
    (μ : Measure (Fin n → ℝ)) :
    0 ≤ entropyPower_nDim n h μ :=
  (entropyPower_nDim_pos n h μ).le

/-- Unfold lemma for `entropyPower_nDim`. -/
theorem entropyPower_nDim_eq_exp (n : ℕ) (h : Measure (Fin n → ℝ) → ℝ)
    (μ : Measure (Fin n → ℝ)) :
    entropyPower_nDim n h μ = Real.exp ((2 / n) * h μ) := rfl

/-! ## §B — L-BM1 + L-BM2 + L-BM3 retreat predicates -/

/-- **L-BM1 (Brunn-Minkowski entropy hypothesis, 核心 retreat)**:
Brunn-Minkowski (entropy form, Cover-Thomas Theorem 17.9.2) の結論

    `entropyPower_nDim n h (P.map (X+Y))
      ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y)`

を直接 hypothesis 化。主定理本体は `:= h_bm` の 1 行で着地。

Discharge plan `brunn-minkowski-from-epi-discharge-plan.md` (起草済、
本実装未着手) で EPI (T2-D) の n-dim 拡張 + Cover-Thomas Theorem 17.7.4
経路から導出する想定。 -/
def IsBrunnMinkowskiEntropyHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (P : Measure Ω) : Prop :=
  entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
    ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y)

/-- **L-BM2 (uniform = log volume hypothesis)**: uniform 分布の `n`-dim
differential entropy が `log vol` に等しい事実を hypothesis 化。

凸体 `A ⊂ Fin n → ℝ` 上の uniform 分布 `μ` について
`h μ = Real.log vol`。本主定理 (§C) では未使用、系 §D
`brunn_minkowski_convex_body` で `Real.exp_log` 経路を閉じるために利用。

Discharge plan `uniform-entropy-log-vol-plan.md` (未着手) で
Common2026 `differentialEntropy_nDim` (これも未定義) と組合せて
discharge する想定。 -/
def IsUniformOnEntropyLogVolHypothesis
    (n : ℕ) (h : Measure (Fin n → ℝ) → ℝ)
    (μ : Measure (Fin n → ℝ)) (vol : ℝ) : Prop :=
  h μ = Real.log vol

/-- **L-BM3 (Minkowski sum measurability hypothesis)**: convex bodies
`A, B ⊂ Fin n → ℝ` の Minkowski sum `A + B` の可測性を hypothesis 化。

`Set.add` (pointwise sum, `Mathlib.Algebra.Group.Pointwise.Set.Basic`)
で定義される `A + B := {a + b | a ∈ A, b ∈ B}`。Borel 集合間の Minkowski
sum は一般には Borel ではない (有名な反例) ため、convexity / compactness
の追加仮定が必要。本 plan ではこの可測性自身を hypothesis として外出し、
discharge plan で `Convex.measurableSet` 系 + compactness で吸収する想定。 -/
def IsMinkowskiSumMeasurableHypothesis {n : ℕ} (A B : Set (Fin n → ℝ)) : Prop :=
  MeasurableSet (A + B)

/-! ## §C — 主定理 (Cover-Thomas Theorem 17.9.2, L-BM1 適用形) -/

/-- **Brunn-Minkowski inequality (entropy form, Cover-Thomas Theorem 17.9.2)**.

独立な `Fin n → ℝ`-値確率変数 `X, Y` に対し

    `entropyPower_nDim n h (P.map (X+Y))
      ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y)`,

すなわち `exp ((2/n) h(X+Y)) ≥ exp ((2/n) h(X)) + exp ((2/n) h(Y))`。

🟢ʰ load-bearing hypothesis — NOT a discharge. 本定理本体は
`h_bm_entropy_assumed` (= `IsBrunnMinkowskiEntropyHypothesis`,
Brunn-Minkowski entropy 形そのもの) で着地する。L-BM1 retreat:
Brunn-Minkowski の結論を Mathlib 壁 (Cover-Thomas 17.9.2 / 17.7.4 系の
`n`-dim 拡張が Mathlib 未整備) のため hypothesis pass-through。
genuine reduction は `BrunnMinkowskiClosure.lean` の
`brunn_minkowski_entropy_jointPi` (concrete entropy + sqrt-form geometric
BM) に分離して provide される。

EPI との関係: EPI (`entropy_power_inequality`, T2-D) は `n = 1` 限定。
本 `n`-dim 形は EPI の coordinate-wise 拡張 + Cover-Thomas Theorem 17.7.4
経路で discharge plan `brunn-minkowski-from-epi-discharge-plan.md`
(起草済、本実装未着手) に塞ぐ。 -/
theorem brunn_minkowski_entropy_inequality
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm_entropy_assumed : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y) :=
  h_bm_entropy_assumed

/-! ## §D — Cover-Thomas 露出形 + 凸体 specialization -/

/-- **Brunn-Minkowski in `Real.exp ((2/n) · ...)` form** (Cover-Thomas
Theorem 17.9.2 露出形). -/
theorem brunn_minkowski_entropy_inequality_exp_form
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    Real.exp ((2 / n) * h (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp ((2 / n) * h (P.map X))
        + Real.exp ((2 / n) * h (P.map Y)) := by
  have hh := brunn_minkowski_entropy_inequality P h X Y hX hY hXY h_bm
  simpa [entropyPower_nDim] using hh

/-- **Brunn-Minkowski for convex bodies (Cover-Thomas Cor. 17.9.3)**: 凸体
`A, B ⊂ Fin n → ℝ` (正の体積) について

    `exp ((1/n) · log (vol(A+B))) ≥ exp ((1/n) · log (vol A))
      + exp ((1/n) · log (vol B))`,

すなわち `|A+B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}` (Minkowski の
Brunn-Minkowski 不等式)。

L-BM1 の主形は `(2/n)·h` を露出する `exp ((2/n)h(X+Y)) ≥ exp ((2/n)h(X)) + exp ((2/n)h(Y))`
であり、これは凸体に specialize すると `vol^{2/n}` の不等式となる。
Cover-Thomas Cor. 17.9.3 の `vol^{1/n}` 形を得るには **`(1/n)·h` 形の
Brunn-Minkowski** (= **L-BM1'**, sharper sqrt 版) を別 hypothesis として
追加 pass-through する。

撤退ライン採用:

* `h_bm_sharp` (L-BM1' = sharper `(1/n)` 形 Brunn-Minkowski): `vol^{1/n}`
  に直結する `(1/n)·h` 形を直接 hypothesis 化
* `hA_unif`, `hB_unif`, `hAB_unif` (L-BM2): uniform の entropy = log vol
  hypothesis (3 本: `Uniform A`, `Uniform B`, `Uniform (A+B)`)
* `_h_sum_meas` (L-BM3): Minkowski sum の可測性 hypothesis (signature
  露出のみ) -/
theorem brunn_minkowski_convex_body
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB)
    (hvolAB : 0 < volAB)
    (hA_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map X) volA)
    (hB_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map Y) volB)
    (hAB_unif : IsUniformOnEntropyLogVolHypothesis n h
      (P.map (fun ω => X ω + Y ω)) volAB)
    (_h_sum_meas : IsMinkowskiSumMeasurableHypothesis A B)
    (h_bm_sharp :
      Real.exp ((1 / n) * h (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp ((1 / n) * h (P.map X))
          + Real.exp ((1 / n) * h (P.map Y))) :
    Real.exp ((1 / n) * Real.log volAB)
      ≥ Real.exp ((1 / n) * Real.log volA)
        + Real.exp ((1 / n) * Real.log volB) := by
  -- L-BM2 で h(P.map X) = log volA 等に置換し、L-BM1' に流し込む。
  unfold IsUniformOnEntropyLogVolHypothesis at hA_unif hB_unif hAB_unif
  rw [hA_unif, hB_unif, hAB_unif] at h_bm_sharp
  exact h_bm_sharp

/-! ## §E — 補助 corollary 群 -/

/-- **`n = 1` specialization**: `entropyPower_nDim 1 h μ = Real.exp (2 · h μ)`,
EPI の `entropyPower` 形と係数 `(2/1) = 2` で一致。 -/
theorem entropyPower_nDim_one (h : Measure (Fin 1 → ℝ) → ℝ)
    (μ : Measure (Fin 1 → ℝ)) :
    entropyPower_nDim 1 h μ = Real.exp (2 * h μ) := by
  unfold entropyPower_nDim
  norm_num

/-- **3-arg Brunn-Minkowski pass-through**: 3 つの独立変数 `X, Y, Z` に対し
Brunn-Minkowski を chain することで

    `exp ((2/n) h(X+Y+Z)) ≥ exp ((2/n) h(X)) + exp ((2/n) h(Y)) + exp ((2/n) h(Z))`.

撤退ラインは 2-arg 形を 2 回適用するための 2 つの L-BM1 hypothesis を取る
形に外出し (X+Y vs Z のペアで 1 回、X vs Y のペアで 1 回)。EPI
`entropy_power_inequality_three_arg` と同パターン。 -/
theorem brunn_minkowski_entropy_inequality_three_arg
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y Z : Ω → (Fin n → ℝ))
    (h_xy_z_bm :
      IsBrunnMinkowskiEntropyHypothesis n h (fun ω => X ω + Y ω) Z P)
    (h_x_y_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    entropyPower_nDim n h (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y)
        + entropyPower_nDim n h (P.map Z) := by
  -- Step 1: from `h_xy_z_bm`, we get
  --   `entropyPower_nDim ((X+Y)+Z) ≥ entropyPower_nDim (X+Y) + entropyPower_nDim Z`.
  have h1 : entropyPower_nDim n h (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
        + entropyPower_nDim n h (P.map Z) := by
    -- `fun ω => (X ω + Y ω) + Z ω` is `fun ω => X ω + Y ω + Z ω` (assoc).
    have h_assoc : (fun ω : Ω => (X ω + Y ω) + Z ω)
        = (fun ω : Ω => X ω + Y ω + Z ω) := by
      funext ω; ring
    have h := h_xy_z_bm
    unfold IsBrunnMinkowskiEntropyHypothesis at h
    rw [h_assoc] at h
    exact h
  -- Step 2: from `h_x_y_bm`, we get
  --   `entropyPower_nDim (X+Y) ≥ entropyPower_nDim X + entropyPower_nDim Y`.
  have h2 : entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n h (P.map X)
        + entropyPower_nDim n h (P.map Y) := h_x_y_bm
  -- Combine via transitivity.
  linarith

end InformationTheory.Shannon.BrunnMinkowski
