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
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo

/-!
# Data processing inequality for mutual information

The data processing inequality `I(X; f(Y)) ≤ I(X; Y)` for deterministic post-processing.

## Main statements

* `klDiv_map_le` — `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν` for any measurable `f`.
* `mutualInfo_le_of_postprocess` — `I(X; f(Y)) ≤ I(X; Y)`.

## Implementation notes

`klDiv_map_le` is built via conditional Jensen (`ConvexOn.map_condExp_le`) applied to
`klFun` and the Radon-Nikodym derivative identity `Measure.rnDeriv_map`.
The mutual-information bound follows by applying `klDiv_map_le` to `Prod.map id f`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]

/-- General pushforward DPI: `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν` for measurable `f`. -/
@[entry_point]
theorem klDiv_map_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν := by
  -- non-absolutely-continuous case: klDiv μ ν = ∞
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hμν]; exact le_top
  -- non-integrable case: klDiv μ ν = ∞
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable h_int]; exact le_top
  -- main case: μ ≪ ν and klDiv μ ν < ∞
  have h_ac_map : μ.map f ≪ ν.map f := hμν.map hf
  have _ : IsFiniteMeasure (μ.map f) := Measure.isFiniteMeasure_map μ f
  have _ : IsFiniteMeasure (ν.map f) := Measure.isFiniteMeasure_map ν f
  -- integrability and nonnegativity of klFun ∘ rnDeriv
  have h_int_klFun : Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν :=
    (integrable_klFun_rnDeriv_iff hμν).mpr h_int
  have h_klFun_nn : 0 ≤ᵐ[ν] fun x ↦ klFun (μ.rnDeriv ν x).toReal :=
    ae_of_all _ fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  -- comap sub-σ-algebra (written directly: `let` contaminates typeclass resolution)
  have hm : MeasurableSpace.comap f ‹MeasurableSpace β› ≤ ‹MeasurableSpace α› :=
    hf.comap_le
  -- rewrite both KL divergences as lintegral of klFun
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac_map, klDiv_eq_lintegral_klFun_of_ac hμν]
  -- translate the integral over ν.map f to an integral over ν
  rw [show (∫⁻ y, ENNReal.ofReal
              (klFun ((μ.map f).rnDeriv (ν.map f) y).toReal) ∂(ν.map f))
        = ∫⁻ x, ENNReal.ofReal
              (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) ∂ν from
      lintegral_map (by fun_prop) hf]
  -- toReal_rnDeriv_map: ((μ.map f).rnDeriv (ν.map f) (f ·)).toReal =ᵐ[ν] condExp of (μ.rnDeriv ν ·).toReal
  have h_rnDeriv_map :
      (fun x ↦ ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) =ᵐ[ν]
        ν[(fun x ↦ (μ.rnDeriv ν x).toReal) | MeasurableSpace.comap f ‹MeasurableSpace β›] :=
    toReal_rnDeriv_map hμν hf
  -- conditional Jensen for convex klFun on [0, ∞)
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
  -- lift the pointwise bound to ENNReal.ofReal
  have h_le_ae : (fun x ↦ ENNReal.ofReal (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal))
      ≤ᵐ[ν] fun x ↦
        ENNReal.ofReal (ν[(fun x ↦ klFun (μ.rnDeriv ν x).toReal)
                            | MeasurableSpace.comap f ‹MeasurableSpace β›] x) := by
    filter_upwards [h_rnDeriv_map, h_jensen] with x hx hjen
    rw [hx]; exact ENNReal.ofReal_le_ofReal hjen
  -- integrate: lintegral_mono_ae → condExp-integral identity → original integral
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

/-- Data processing inequality: `I(X; f(Y)) ≤ I(X; Y)` for measurable `f`. -/
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
  -- joint distribution is the pushforward of Prod.map id f
  have h_joint : μ.map (fun ω => (Xs ω, f (Yo ω)))
      = (μ.map (fun ω => (Xs ω, Yo ω))).map (Prod.map id f) := by
    rw [Measure.map_map hg hpair]
    rfl
  -- product distribution is also the pushforward of Prod.map id f
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
