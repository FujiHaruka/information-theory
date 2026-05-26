import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.Measure.Prod
import Common2026.Meta.EntryPoint
import Common2026.Shannon.MutualInfo

/-!
# Data processing inequality for mutual information (Phase 4-α DPI)

Shannon ムーンショット ([`docs/shannon/shannon-moonshot-plan.md`](../../../docs/shannon/shannon-moonshot-plan.md))
の Phase 4-α DPI: `I(X; f(Y)) ≤ I(X; Y)` (deterministic post-processing on Y).

戦略 (計画書 `:223`, 在庫調査 `docs/shannon/shannon-mathlib-inventory.md` B 節):
1. **核補題** `klDiv_map_le`: 一般 pushforward DPI `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`。
   Mathlib に直接補題は **不在**。`ConvexOn.apply_rnDeriv_ae_le_integral` (`MeasureTheory/
   Measure/Decomposition/IntegralRNDeriv.lean:137`) の Jensen 不等式と `Measure.rnDeriv_map`
   (一般 Measurable 形, `ConditionalExpectation/RadonNikodym.lean:83`) で構築する。
2. **mutualInfo の DPI 系**: 核補題を `Prod.map id f` に適用し、`map_prod_map` と
   `compProd_map_condDistrib` の plumbing で `mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo`
   を導く。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]

/-- 一般 pushforward DPI (核補題): `Measurable f` の pushforward で KL divergence は減る。
Mathlib に直接補題は **完全不在** (Phase 4-M0 在庫調査 B 節で確認済) のため自作。

戦略 (Jensen + Measure.rnDeriv_map):
- `Measure.rnDeriv_map` (`ConditionalExpectation/RadonNikodym.lean:83`) で
  `(μ.map f).rnDeriv (ν.map f) ∘ f =ᵐ[ν] ν⁻[μ.rnDeriv ν | comap f]`
- `klFun` の凸性 (`KullbackLeibler/KLFun.lean: convexOn_klFun`) + 条件付き Jensen で
  `klFun((dμ.map f / dν.map f) ∘ f) ≤ᵐ ν⁻[klFun(dμ/dν) | comap f]`
- 両辺を `ν` 積分し、`(ν.map f)` 上の積分に変換すれば
  `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`

予算: 50〜100 行。条件付き期待値の積分・絶対連続性の `f`-pushforward への伝播・klFun
の連続性 / 強可測性が plumbing の主体。-/
@[entry_point]
theorem klDiv_map_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν := by
  -- 非絶対連続側: klDiv μ ν = ∞ なので自明
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hμν]; exact le_top
  -- klDiv μ ν = ∞ (= llr 非可積分) も自明
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable h_int]; exact le_top
  -- 主ケース: μ ≪ ν かつ klDiv μ ν < ∞
  have h_ac_map : μ.map f ≪ ν.map f := hμν.map hf
  have _ : IsFiniteMeasure (μ.map f) := Measure.isFiniteMeasure_map μ f
  have _ : IsFiniteMeasure (ν.map f) := Measure.isFiniteMeasure_map ν f
  -- klFun ∘ rnDeriv の integrability と nonneg
  have h_int_klFun : Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν :=
    (integrable_klFun_rnDeriv_iff hμν).mpr h_int
  have h_klFun_nn : 0 ≤ᵐ[ν] fun x ↦ klFun (μ.rnDeriv ν x).toReal :=
    ae_of_all _ fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  -- comap-σ (直接式で書く: `let` だと型クラス解決が汚染される)
  have hm : MeasurableSpace.comap f ‹MeasurableSpace β› ≤ ‹MeasurableSpace α› :=
    hf.comap_le
  -- 両 KL を lintegral klFun 形に
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac_map, klDiv_eq_lintegral_klFun_of_ac hμν]
  -- ν.map f 上の積分を ν 上の積分に翻訳
  rw [show (∫⁻ y, ENNReal.ofReal
              (klFun ((μ.map f).rnDeriv (ν.map f) y).toReal) ∂(ν.map f))
        = ∫⁻ x, ENNReal.ofReal
              (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) ∂ν from
      lintegral_map (by fun_prop) hf]
  -- toReal_rnDeriv_map: ((μ.map f).rnDeriv (ν.map f) (f ·)).toReal =ᵐ[ν] ν[(μ.rnDeriv ν ·).toReal | comap f]
  have h_rnDeriv_map :
      (fun x ↦ ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) =ᵐ[ν]
        ν[(fun x ↦ (μ.rnDeriv ν x).toReal) | MeasurableSpace.comap f ‹MeasurableSpace β›] :=
    toReal_rnDeriv_map hμν hf
  -- cond Jensen for klFun on Ici 0
  have h_jensen :
      (fun x ↦ klFun
          (ν[(fun x ↦ (μ.rnDeriv ν x).toReal)
             | MeasurableSpace.comap f ‹MeasurableSpace β›] x))
        ≤ᵐ[ν] (ν[(fun x ↦ klFun (μ.rnDeriv ν x).toReal)
                  | MeasurableSpace.comap f ‹MeasurableSpace β›]) :=
    ConvexOn.map_condExp_le hm convexOn_klFun
      (continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn _)
      (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
      isClosed_Ici
      Measure.integrable_toReal_rnDeriv
      h_int_klFun
  -- LHS の klFun ∘ rnDeriv map ≤ᵐ condExp ∘ klFun ∘ rnDeriv (ENNReal.ofReal で持ち上げ)
  have h_le_ae : (fun x ↦ ENNReal.ofReal (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal))
      ≤ᵐ[ν] fun x ↦
        ENNReal.ofReal (ν[(fun x ↦ klFun (μ.rnDeriv ν x).toReal)
                            | MeasurableSpace.comap f ‹MeasurableSpace β›] x) := by
    filter_upwards [h_rnDeriv_map, h_jensen] with x hx hjen
    rw [hx]; exact ENNReal.ofReal_le_ofReal hjen
  -- 積分: lintegral_mono_ae → ofReal-condExp-lintegral 等式 → ofReal-original-lintegral
  have h_step1 :
      ∫⁻ x, ENNReal.ofReal
              (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) ∂ν
        ≤ ∫⁻ x, ENNReal.ofReal
              (ν[(fun x ↦ klFun (μ.rnDeriv ν x).toReal)
                  | MeasurableSpace.comap f ‹MeasurableSpace β›] x) ∂ν :=
    lintegral_mono_ae h_le_ae
  have h_step2 :
      ∫⁻ x, ENNReal.ofReal
              (ν[(fun x ↦ klFun (μ.rnDeriv ν x).toReal)
                  | MeasurableSpace.comap f ‹MeasurableSpace β›] x) ∂ν
        = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν := by
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_condExp
          (condExp_nonneg h_klFun_nn),
        integral_condExp hm,
        ofReal_integral_eq_lintegral_ofReal h_int_klFun h_klFun_nn]
  exact h_step1.trans h_step2.le

/-- Data processing inequality: deterministic post-processing decreases mutual information.
`Z = f(Y)` で `I(X; f(Y)) ≤ I(X; Y)`.

戦略: `klDiv_map_le` を `g := Prod.map id f : X × Y → X × Z` に適用し、
- `μ.map (Xs, f∘Yo) = (μ.map (Xs, Yo)).map (Prod.map id f)` (Map composition)
- `(μ.map Xs).prod (μ.map (f∘Yo)) = ((μ.map Xs).prod (μ.map Yo)).map (Prod.map id f)`
  (`Measure.map_prod_map`)

の 2 つの書き換えで `mutualInfo μ Xs (f∘Yo) = klDiv ((μ.map (Xs,Yo)).map g) (((μ.map Xs).prod (μ.map Yo)).map g)`
にし、`klDiv_map_le` を直接適用。 -/
@[entry_point]
theorem mutualInfo_le_of_postprocess
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    {f : Y → Z} (hf : Measurable f) :
    mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo := by
  unfold mutualInfo
  have hpair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have hg : Measurable (Prod.map id f : X × Y → X × Z) := measurable_id.prodMap hf
  have _ : IsFiniteMeasure (μ.map Xs) := Measure.isFiniteMeasure_map μ Xs
  have _ : IsFiniteMeasure (μ.map Yo) := Measure.isFiniteMeasure_map μ Yo
  have _ : IsFiniteMeasure (μ.map (fun ω => (Xs ω, Yo ω))) :=
    Measure.isFiniteMeasure_map μ _
  -- joint distribution は Prod.map id f の pushforward
  have h_joint : μ.map (fun ω => (Xs ω, f (Yo ω)))
      = (μ.map (fun ω => (Xs ω, Yo ω))).map (Prod.map id f) := by
    rw [Measure.map_map hg hpair]
    rfl
  -- product distribution も Prod.map id f の pushforward
  have h_prod : (μ.map Xs).prod (μ.map (f ∘ Yo))
      = ((μ.map Xs).prod (μ.map Yo)).map (Prod.map id f) := by
    rw [show μ.map (f ∘ Yo) = (μ.map Yo).map f from (Measure.map_map hf hYo).symm,
        ← Measure.map_prod_map (μ.map Xs) (μ.map Yo) measurable_id hf,
        Measure.map_id]
  show klDiv (μ.map (fun ω => (Xs ω, f (Yo ω))))
      ((μ.map Xs).prod (μ.map (f ∘ Yo)))
    ≤ klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))
  rw [h_joint, h_prod]
  exact klDiv_map_le hg _ _

end InformationTheory.Shannon
