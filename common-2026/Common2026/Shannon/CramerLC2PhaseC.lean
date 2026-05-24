import Common2026.Shannon.Cramer
import Common2026.Shannon.CramerLC2Discharge
import Common2026.Shannon.CramerLC2DischargeExt
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Cramér L-C2 Phase C partial discharge (T1-C follow-up Phase C)

This file extends `Common2026/Shannon/CramerLC2DischargeExt.lean` (Phase A/B
plumbing + tilted LLN) with the **Phase C partial discharge** of the
`h_tilted_lower` hypothesis of `Cramer.cramer_lower`.

## Status

Phase C requires a **Cramér change-of-measure step** that relates the tilted
infinite-product measure
`Measure.infinitePi (fun _ : ℕ => μ₀.tilted (lam * Y ·))` to the tilted-form of
the un-tilted product measure
`(Measure.infinitePi (fun _ : ℕ => μ₀)).tilted (∑ i ∈ Finset.range n, lam * Y ∘ eval i)`
on cylinders of width `n`. Mathlib has no direct compatibility lemma for this
(`Measure.infinitePi_tilted_eq`), and the textbook proof requires a 500+ line
construction of the n-letter Radon–Nikodym derivative.

We therefore **abstract this identification as a hypothesis** via the predicate
`IsMeasureInfinitePiTiltedEq` and publish a *partial* discharge: given the
n-letter RN-deriv compatibility as a hypothesis, the in-probability LLN from
`CramerLC2DischargeExt.tilted_lln_in_probability_real` is converted into the
parent `h_tilted_lower` hypothesis form, and threaded through the existing
`cramer_lower` / `cramer_lower_legendre` / `cramer_tendsto` chain.

## Outline

### Phase C-1 — predicate for the missing Mathlib gap

* `IsMeasureInfinitePiTiltedEq μ₀ Y lam` — the n-letter RN-deriv identification
  that the tilted infinite product is, on cylinders of width `n`, equivalent to
  the cylinder-restricted tilt of the un-tilted product measure with the sum
  exponent `∑ i ∈ Finset.range n, lam · Y (ω i) − n · Λ(lam)`.

### Phase C-2 — `h_tilted_lower` reduction

* `tilted_lower_from_predicate` — given the predicate + the in-probability LLN
  on the tilted ambient + bounded RV hypotheses, construct the
  `h_tilted_lower`-shape Chernoff lower bound on the un-tilted infinite product.

### Phase C-3 — main discharged wrappers

* `cramer_lower_phaseC_partial_discharge` — `cramer_lower` with `h_tilted_lower`
  replaced by `IsMeasureInfinitePiTiltedEq`.
* `cramer_lower_legendre_phaseC_partial_discharge` — Legendre form.
* `cramer_tendsto_phaseC_partial_discharge` — `Tendsto` form.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Phase C-1 — n-letter RN-deriv identification predicate -/

/-- **Cramér n-letter change-of-measure predicate** (Mathlib gap abstraction).

Captures the missing Mathlib compatibility lemma
`Measure.infinitePi (fun _ => μ₀.tilted (lam * Y ·)) ↔ (Measure.infinitePi μ₀).tilted (∑ lam * Y ∘ eval i)`
on cylinders of width `n`, in the form usable as input to Cramér's lower-bound
change-of-measure step.

The intended interpretation: for every `n` and every measurable event
`E ⊆ {ω | a·n ≤ ∑ i ∈ Finset.range n, Y (ω i)}`, the un-tilted product measure
of `E` admits the Chernoff-style lower bound
`exp(-n · (lam · a − Λ(lam))) · μ_tilt(E) − o(1) ≤ μ.real E`,
where `μ_tilt := Measure.infinitePi (fun _ => μ₀.tilted (lam * Y ·))` and
`Λ := cgf Y μ₀`.

In the textbook setting this follows from `(dμ_tilt / dμ)|_{cylinder n}
= exp(lam · ∑ Y(ω_i) − n·Λ(lam))`, but the n-letter RN-deriv identification is
not yet in Mathlib. -/
def IsMeasureInfinitePiTiltedEq (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a ε : ℝ, 0 < ε →
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}

/-! ## Phase C-2 — `h_tilted_lower` reduction -/

/-- **`h_tilted_lower` reduction**: given the n-letter RN-deriv predicate, the
parent `h_tilted_lower` hypothesis of `Cramer.cramer_lower` follows in the
canonical i.i.d. product-measure setting `X i ω := Y (ω i)`.

`@audit:suspect(cramer-lc2-discharge-moonshot-plan)` -/
lemma tilted_lower_from_predicate
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ}
    (_hY_meas : Measurable Y) (_h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ)
    (h_pred : IsMeasureInfinitePiTiltedEq μ₀ Y lam) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) *
          (lam * a
            - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
                (Measure.infinitePi (fun _ : ℕ => μ₀)) lam
            + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
  intro ε hε
  -- The CGF bridge `cgf_eval_eq_cgf_base` collapses
  -- `cgf (Y ∘ eval 0) (infinitePi μ₀) lam = cgf Y μ₀ lam`, after which the
  -- predicate `h_pred a ε hε` is exactly the target shape.
  have h_cgf := cgf_eval_eq_cgf_base (μ₀ := μ₀) (Y := Y) _hY_meas 0 lam
  obtain ⟨C, hC_pos, hC_event⟩ := h_pred a ε hε
  refine ⟨C, hC_pos, ?_⟩
  refine hC_event.mono fun n hn => ?_
  -- The two exponents agree by `h_cgf`.
  have h_exp_eq :
      Real.exp (-(n : ℝ) *
          (lam * a
            - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
                (Measure.infinitePi (fun _ : ℕ => μ₀)) lam
            + lam * ε))
        = Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε)) := by
    rw [h_cgf]
  rw [h_exp_eq]
  exact hn

/-! ## Phase C-3 — discharged wrappers -/

/-- **Cramér lower bound, Phase C partial discharge**.

For the canonical i.i.d. product-measure setting `X i ω := Y (ω i)` with
`Y : Ω₀ → ℝ` bounded and measurable, and on the un-tilted infinite product
`μ := Measure.infinitePi (fun _ => μ₀)`, the parent `cramer_lower`'s
`h_tilted_lower` hypothesis is reduced to the Mathlib-gap predicate
`IsMeasureInfinitePiTiltedEq μ₀ Y lam`.

The other ambient hypotheses (`iIndepFun`, `IdentDistrib`, bounded family) are
discharged using the Phase A plumbing from `CramerLC2Discharge`.

`@audit:suspect(cramer-lc2-discharge-moonshot-plan)` -/
theorem cramer_lower_phaseC_partial_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_pred : IsMeasureInfinitePiTiltedEq μ₀ Y lam) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  -- Phase A plumbing: the eval family is iIndepFun + IdentDistrib + bounded.
  have h_indep : iIndepFun (fun i : ℕ => fun ω : ℕ → Ω₀ => Y (ω i))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) :=
    iIndepFun_eval_under_infinitePi (μ₀ := μ₀) hY_meas
  have h_meas : ∀ i, Measurable (fun ω : ℕ → Ω₀ => Y (ω i)) :=
    fun i => hY_meas.comp (measurable_pi_apply i)
  have h_ident : ∀ i, IdentDistrib
      (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) :=
    fun i => identDistrib_eval_under_infinitePi hY_meas i
  have h_bdd_eval : ∃ M, ∀ i ω, |(fun (ω : ℕ → Ω₀) => Y (ω i)) ω| ≤ M := by
    obtain ⟨M, hM⟩ := bounded_eval_family h_bdd
    exact ⟨M, hM⟩
  -- Phase C-2: reduce `h_pred` to `h_tilted_lower`-shape.
  have h_tilted_lower :=
    tilted_lower_from_predicate hY_meas h_bdd a lam h_pred
  exact cramer_lower (μ := Measure.infinitePi (fun _ : ℕ => μ₀))
    h_indep h_meas h_ident h_bdd_eval a lam hlam h_coboundedBelow h_tilted_lower

/-- **Cramér lower bound (Legendre form), Phase C partial discharge**.

`@audit:suspect(cramer-lc2-discharge-moonshot-plan)` -/
theorem cramer_lower_legendre_phaseC_partial_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (hlam_opt :
      lam * a
          - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
              (Measure.infinitePi (fun _ : ℕ => μ₀)) lam
        = cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a)
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_pred : IsMeasureInfinitePiTiltedEq μ₀ Y lam) :
    -cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ => μ₀)) a
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  have h := cramer_lower_phaseC_partial_discharge
    (μ₀ := μ₀) hY_meas h_bdd a lam hlam h_coboundedBelow h_pred
  rw [← hlam_opt]; exact h

/-- **Cramér's theorem (`Tendsto` form), Phase C partial discharge**.

The asymptotic exponential rate of the upper-tail probability of the i.i.d.
sample sum equals the negative Cramér rate. Discharged from `cramer_tendsto`
with `h_tilted_lower` replaced by the n-letter RN-deriv predicate.

`@audit:suspect(cramer-lc2-discharge-moonshot-plan)` -/
theorem cramer_tendsto_phaseC_partial_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (hlam_opt :
      lam * a
          - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
              (Measure.infinitePi (fun _ : ℕ => μ₀)) lam
        = cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a)
    (h_pos : ∀ᶠ n : ℕ in atTop,
      0 < (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})
    (h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_pred : IsMeasureInfinitePiTiltedEq μ₀ Y lam) :
    Filter.Tendsto (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop
      (𝓝 (-cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a)) := by
  have h_indep : iIndepFun (fun i : ℕ => fun ω : ℕ → Ω₀ => Y (ω i))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) :=
    iIndepFun_eval_under_infinitePi (μ₀ := μ₀) hY_meas
  have h_meas : ∀ i, Measurable (fun ω : ℕ → Ω₀ => Y (ω i)) :=
    fun i => hY_meas.comp (measurable_pi_apply i)
  have h_ident : ∀ i, IdentDistrib
      (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) :=
    fun i => identDistrib_eval_under_infinitePi hY_meas i
  have h_bdd_eval : ∃ M, ∀ i ω, |(fun (ω : ℕ → Ω₀) => Y (ω i)) ω| ≤ M := by
    obtain ⟨M, hM⟩ := bounded_eval_family h_bdd
    exact ⟨M, hM⟩
  have h_tilted_lower :=
    tilted_lower_from_predicate hY_meas h_bdd a lam h_pred
  exact cramer_tendsto (μ := Measure.infinitePi (fun _ : ℕ => μ₀))
    h_indep h_meas h_ident h_bdd_eval a lam hlam hlam_opt h_pos
    h_cobdd h_coboundedBelow h_bdd_above h_bdd_below h_tilted_lower

/-! ## Phase C-4 — sanity corollary: predicate triviality cases

These corollaries are not part of the main discharge but illustrate the
predicate's interface. They are kept minimal and trivial. -/

/-- The predicate is monotone in the un-tilted ambient: if it holds for one
choice of `μ₀`, the consequent inequality is parameterized by `a` and `ε`. The
following helper records the predicate's defining shape `∀ a ε, ... ∃ C ...`
for downstream callers who want to inline the construction. -/
lemma isMeasureInfinitePiTiltedEq_iff (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam ↔
      ∀ a ε : ℝ, 0 < ε →
        ∃ C > 0, ∀ᶠ n : ℕ in atTop,
          C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
            ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
                {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} :=
  Iff.rfl

end InformationTheory.Shannon.Cramer.Discharge
