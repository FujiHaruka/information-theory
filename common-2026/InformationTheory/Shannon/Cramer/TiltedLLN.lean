import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Cramer.TiltedIID
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Cramér lower-bound extension: tilted-side law of large numbers

This file extends `InformationTheory/Shannon/Cramer/TiltedIID.lean` with the
tilted-side law of large numbers for the coordinate-eval family on the infinite
product measure.

## Main statements

* `isProbabilityMeasure_infinitePi_tilted_of_bounded` — the tilted infinite
  product `Measure.infinitePi (fun _ : ℕ => μ₀.tilted (lam * Y ·))` is a
  probability measure.
* `pairwise_indepFun_tilted_ambient`, `integrable_eval_under_infinitePi_tilted`,
  `integral_eval_under_infinitePi_tilted` — the inputs to the strong law.
* `tilted_lln_ae` — the almost-sure law of large numbers on the tilted ambient.
* `tilted_lln_in_probability`, `tilted_lln_in_probability_real` — its in-measure
  (in-probability) upgrades.

## Implementation notes

`isProbabilityMeasure_infinitePi_tilted_of_bounded` is stated as an outward-facing
lemma because Lean's typeclass synthesis does not consistently β-reduce the
per-coordinate `μ₀.tilted` factor through the `fun _ : ℕ => …` wrapper when
looking up `IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => μ₀.tilted ...))`.
-/

namespace InformationTheory.Shannon.Cramer.TiltedLLN

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Probability-measure instance and strong-law inputs -/

/-- The infinite-product measure
`Measure.infinitePi (fun _ : ℕ => μ₀.tilted (lam * Y ·))` is a probability
measure. Stated explicitly because the unifier does not β-reduce the
per-coordinate factor through the `fun _ : ℕ => ...` wrapper consistently when
synthesizing the standard `Measure.infinitePi` instance. -/
@[entry_point]
lemma isProbabilityMeasure_infinitePi_tilted_of_bounded
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := by
  haveI hp : IsProbabilityMeasure (μ₀.tilted (fun ω => lam * Y ω)) :=
    isProbabilityMeasure_tilted_of_bounded hY_meas h_bdd lam
  haveI : ∀ i : ℕ, IsProbabilityMeasure
      ((fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) i) := fun _ => hp
  infer_instance

lemma pairwise_indepFun_tilted_ambient
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    Pairwise
      ((fun X Z => IndepFun X Z
          (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))))
        on (fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))) := by
  intro i j hij
  exact (iIndepFun_tilted_ambient hY_meas h_bdd lam).indepFun hij

lemma integrable_eval_under_infinitePi_tilted
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    Integrable (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := by
  haveI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    isProbabilityMeasure_infinitePi_tilted_of_bounded hY_meas h_bdd lam
  obtain ⟨M, hM⟩ := h_bdd
  have h_meas_comp : Measurable (fun ω : ℕ → Ω₀ => Y (ω 0)) :=
    hY_meas.comp (measurable_pi_apply 0)
  refine Integrable.mono'
    (g := fun _ : ℕ → Ω₀ => M)
    (integrable_const M)
    h_meas_comp.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs]
    exact hM (ω 0))

/-- The integral of `Y ∘ eval 0` under the tilted infinite product equals the
integral of `Y` under the tilted base. -/
lemma integral_eval_under_infinitePi_tilted
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    ∫ ω, Y (ω 0) ∂Measure.infinitePi
        (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))
      = ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) := by
  haveI hp : IsProbabilityMeasure (μ₀.tilted (fun ω => lam * Y ω)) :=
    isProbabilityMeasure_tilted_of_bounded hY_meas h_bdd lam
  haveI : ∀ i : ℕ, IsProbabilityMeasure
      ((fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) i) := fun _ => hp
  -- Rewrite LHS as `∫ y, Y y ∂(map (eval 0) (infinitePi ...))` via `integral_map`.
  have h_eval_meas : AEMeasurable (fun ω : ℕ → Ω₀ => ω 0)
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    (measurable_pi_apply 0).aemeasurable
  have h_push :
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).map
          (fun ω : ℕ → Ω₀ => ω 0)
        = μ₀.tilted (fun ω => lam * Y ω) :=
    Measure.infinitePi_map_eval _ 0
  have h_aesm : AEStronglyMeasurable Y
      ((Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).map
        (fun ω : ℕ → Ω₀ => ω 0)) := by
    rw [h_push]
    exact hY_meas.aestronglyMeasurable
  have h_map := integral_map (μ := Measure.infinitePi
      (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) h_eval_meas h_aesm
  rw [← h_map, h_push]

/-! ## Almost-sure LLN on the tilted ambient -/

/-- Under the tilted infinite product measure, the empirical mean of the
coordinate-eval family converges almost surely to the base-tilted expectation of
`Y`. -/
@[entry_point]
theorem tilted_lln_ae
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y (ω i)) / n) atTop
        (𝓝 (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)))) := by
  haveI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    isProbabilityMeasure_infinitePi_tilted_of_bounded hY_meas h_bdd lam
  -- Apply `strong_law_ae_real` to the family `X i ω := Y (ω i)`.
  have h_int : Integrable (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    integrable_eval_under_infinitePi_tilted hY_meas h_bdd lam
  have h_pairwise : Pairwise
      ((fun X Z => IndepFun X Z
          (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))))
        on (fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))) :=
    pairwise_indepFun_tilted_ambient hY_meas h_bdd lam
  have h_ident : ∀ i, IdentDistrib
      (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    fun i => identDistrib_tilted_ambient hY_meas h_bdd lam i
  have h_lln := strong_law_ae_real
    (X := fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))
    (μ := Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
    h_int h_pairwise h_ident
  -- Rewrite the limit `μ[X 0] = ∫ ω, Y (ω 0) ∂μ_tilted^∞ = ∫ ω, Y ω ∂μ.tilted ...`.
  have h_int_eq : ∫ ω, Y (ω 0)
      ∂Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))
      = ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) :=
    integral_eval_under_infinitePi_tilted hY_meas h_bdd lam
  rw [h_int_eq] at h_lln
  exact h_lln

/-! ## In-probability LLN on the tilted ambient -/

/-- The almost-sure convergence from `tilted_lln_ae` upgrades to convergence in
measure (= in probability on a probability space). -/
@[entry_point]
theorem tilted_lln_in_probability
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    TendstoInMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
      (fun n ω => (∑ i ∈ Finset.range n, Y (ω i)) / n)
      atTop
      (fun _ : ℕ → Ω₀ => ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) := by
  haveI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    isProbabilityMeasure_infinitePi_tilted_of_bounded hY_meas h_bdd lam
  have h_ae : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y (ω i)) / n) atTop
        (𝓝 (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)))) :=
    tilted_lln_ae hY_meas h_bdd lam
  -- Apply `tendstoInMeasure_of_tendsto_ae`. Each partial-sum / n is strongly
  -- measurable (finite sum of `Measurable` coordinate evals divided by a
  -- constant `n`).
  have h_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω : ℕ → Ω₀ => (∑ i ∈ Finset.range n, Y (ω i)) / n)
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := by
    intro n
    have h_sum : Measurable
        (fun ω : ℕ → Ω₀ => ∑ i ∈ Finset.range n, Y (ω i)) :=
      Finset.measurable_sum _ (fun i _ => hY_meas.comp (measurable_pi_apply i))
    exact (h_sum.div_const _).aestronglyMeasurable
  exact tendstoInMeasure_of_tendsto_ae h_meas h_ae

/-- The `.real`-form of `tilted_lln_in_probability`: for every `ε > 0`, the
measure of the bad set `{ω | ε ≤ |S̄_n - 𝔼[Y]|}` tends to zero. -/
@[entry_point]
theorem tilted_lln_in_probability_real
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω | ε ≤ |(∑ i ∈ Finset.range n, Y (ω i)) / n
            - ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))|}) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    isProbabilityMeasure_infinitePi_tilted_of_bounded hY_meas h_bdd lam
  have h_inprob : TendstoInMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
      (fun n ω => (∑ i ∈ Finset.range n, Y (ω i)) / n)
      atTop
      (fun _ : ℕ → Ω₀ => ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) :=
    tilted_lln_in_probability hY_meas h_bdd lam
  have h_real := (tendstoInMeasure_iff_measureReal_norm.mp h_inprob) ε hε
  -- For real-valued functions, `‖f - g‖ = |f - g|`, so the two sets agree.
  exact h_real

end InformationTheory.Shannon.Cramer.TiltedLLN
