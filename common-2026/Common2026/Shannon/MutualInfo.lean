import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Mutual information via KL divergence (Phase 4-α skeleton)

Shannon ムーンショット ([`docs/shannon-moonshot-plan.md`](../../../docs/shannon-moonshot-plan.md))
の Phase 4-α: Mathlib の `klDiv` を主軸に、相互情報量 `mutualInfo`、その基本性質
(`mutualInfo_nonneg`, `mutualInfo_comm`, `mutualInfo_eq_zero_iff_indep`) を整備する。

Phase 4-M0 の在庫調査結果 ([`docs/shannon-mathlib-inventory.md`](../../../docs/shannon-mathlib-inventory.md))
に基づく skeleton。実証は sorry-driven で順次充填する。

主要素材:
* `klDiv (μ ν : Measure α) : ℝ≥0∞` — `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57`
* `klDiv_compProd_left` — `KullbackLeibler/ChainRule.lean:182` (`@[simp]`)
* `klDiv_compProd_eq_add` — `KullbackLeibler/ChainRule.lean:204`
* `klDiv_eq_zero_iff` — `KullbackLeibler/Basic.lean:377`
* `indepFun_iff_map_prod_eq_prod_map_map` — `Probability/Independence/Basic.lean:701`
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]

/-- Mutual information via KL divergence:
`I(X; Y) := KL(P_{X,Y} ‖ P_X ⊗ P_Y)`. -/
noncomputable def mutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))

/-- 相互情報量は非負。`klDiv` が `ℝ≥0∞` 値なので signature 上自明。 -/
theorem mutualInfo_nonneg (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) :
    0 ≤ mutualInfo μ Xs Yo := bot_le

/-- KL の積測度補題: `klDiv (μ.prod ν₁) (μ.prod ν₂) = (μ Set.univ) * klDiv ν₁ ν₂`。
DPI plumbing の起点になる予定。

**証明戦略**: `compProd_const : μ ⊗ₘ Kernel.const _ ν = μ.prod ν` で `Measure.prod` を
`Kernel.compProd` 形に翻訳した後、KL の MeasurableEquiv 不変性 (= `Prod.swap` 経由の対称化)
で `(ν₁ ⊗ₘ Kernel.const _ μ)` 形に持ち込み、`klDiv_compProd_left` を適用。

**ボトルネック**: KL の MeasurableEquiv 不変性 (`klDiv_map_measurableEquiv`) は Mathlib に不在。
`rnDeriv_map` (`MeasureTheory/Function/ConditionalExpectation/RadonNikodym.lean:83`) を経由して
自作する必要がある (推定 50+ 行)。本補題はその完成後に着手。 -/
theorem klDiv_prod_const_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ]
    (ν₁ ν₂ : Measure β) [SFinite ν₁] [SFinite ν₂] :
    klDiv (μ.prod ν₁) (μ.prod ν₂) = (μ Set.univ) * klDiv ν₁ ν₂ := by
  sorry

/-- 相互情報量の対称性: `I(X; Y) = I(Y; X)`。

**証明戦略**: `Measure.prod_swap : (ν₁.prod ν₂).map Prod.swap = ν₂.prod ν₁` と
`Measure.map_map` で `(μ.map (Xs, Yo)).map Prod.swap = μ.map (Yo, Xs)` を示し、
KL の MeasurableEquiv 不変性 (`Prod.swap` 経由) で結ぶ。

**ボトルネック**: `klDiv_prod_const_left` と同じく `klDiv_map_measurableEquiv` が必要。
別ルート (chain rule + symmetric formulation) もあるが、いずれも自作補題に依存。 -/
theorem mutualInfo_comm
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = mutualInfo μ Yo Xs := by
  sorry

/-- 相互情報量がゼロ ↔ 独立。
`indepFun_iff_map_prod_eq_prod_map_map` (`Independence/Basic.lean:701`) と
`klDiv_eq_zero_iff` (`KullbackLeibler/Basic.lean:377`) の合成で示す。 -/
theorem mutualInfo_eq_zero_iff_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ := by
  have hpair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have : IsProbabilityMeasure (μ.map (fun ω => (Xs ω, Yo ω))) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  have : IsProbabilityMeasure (μ.map Xs) := Measure.isProbabilityMeasure_map hXs.aemeasurable
  have : IsProbabilityMeasure (μ.map Yo) := Measure.isProbabilityMeasure_map hYo.aemeasurable
  rw [mutualInfo, klDiv_eq_zero_iff,
      ← indepFun_iff_map_prod_eq_prod_map_map hXs.aemeasurable hYo.aemeasurable]

end InformationTheory.Shannon
