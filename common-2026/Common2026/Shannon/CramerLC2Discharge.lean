import Common2026.Draft.Shannon.Cramer
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Cramér L-C2 discharge (T1-C follow-up) — Phase A scaffolding (L-D3 retreat)

The parent file `Common2026/Shannon/Cramer.lean` publishes `cramer_lower`,
`cramer_lower_legendre`, and `cramer_tendsto` in **L-C2 hypothesis-form**: the
caller must supply `h_tilted_lower`, a tilted-side lower bound on the upper
tail probability of an i.i.d. sample sum.

This file makes progress towards discharging that hypothesis under the
canonical probabilistic model where the ambient space is `ℕ → Ω₀` with the
infinite product `μ := Measure.infinitePi (fun _ : ℕ => μ₀)` and the i.i.d.
family is `X i := Y ∘ eval i` for some bounded `Y : Ω₀ → ℝ`.

## Status (L-D3 retreat, see `cramer-lc2-discharge-moonshot-plan.md` §撤退ライン)

This module publishes **Phase A scaffolding** only:

* `cgf_eval_eq_cgf_base` — the CGF bridge `cgf (Y ∘ eval i) (infinitePi μ₀) =
  cgf Y μ₀` used to align the Cramér exponent across the two sides.
* `iIndepFun_tilted_ambient` — the tilted-ambient family
  `(fun i ω => Y (ω i))` is `iIndepFun` under
  `Measure.infinitePi (fun _ : ℕ => μ₀.tilted (lam * Y ·))`.
* `identDistrib_tilted_ambient` — each `Y ∘ eval i` is identically
  distributed to `Y ∘ eval 0`.
* `iIndepFun_eval_under_infinitePi` / `identDistrib_eval_under_infinitePi` /
  `bounded_eval_family` — the same plumbing under the un-tilted base
  product measure, used to invoke the parent `cramer_lower`.

Phase B (Mathlib `strong_law_ae_real` launch + in-probability LLN) and Phase C
(Cramér change-of-measure) are deferred to a follow-up plan (`cramer-lc2-
discharge-phase-bc-plan.md`) per the planning document's L-D3 retreat line.
The blocker encountered during Phase B implementation was repeated
typeclass-instance synthesis failures around `IsProbabilityMeasure
(Measure.infinitePi (fun _ : ℕ => μ₀.tilted ...))`: Lean's instance machinery
does not consistently beta-reduce the per-coordinate `μ₀.tilted` factor through
the `fun _ : ℕ => ...` wrapper, even when the equivalent `haveI` is in scope,
which propagates metavariable stuck-ness to every downstream lemma whose
return type mentions the product measure.

Note: the parent `cramer_lower` already publishes the full Cramér lower bound
in hypothesis form, so downstream consumers can supply their own
`h_tilted_lower` and use `Cramer.cramer_lower` directly without this module.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Phase A — tilted ambient + n-IID plumbing -/

/-- **CGF bridge**: `cgf (Y ∘ eval i) (infinitePi (fun _ => μ₀)) = cgf Y μ₀`.
This is the key identification used to align the Cramér exponent across the
infinitePi-side and the per-coordinate `μ₀`-side. -/
lemma cgf_eval_eq_cgf_base
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (i : ℕ) (t : ℝ) :
    cgf (fun ω : ℕ → Ω₀ => Y (ω i)) (Measure.infinitePi (fun _ : ℕ => μ₀)) t
      = cgf Y μ₀ t := by
  -- `cgf (Y ∘ eval i) (infinitePi μ₀) = log (mgf (Y ∘ eval i) (infinitePi μ₀))`
  -- `= log (mgf Y ((infinitePi μ₀).map (eval i)))` by `mgf_map`
  -- `= log (mgf Y μ₀)` by `infinitePi_map_eval`.
  have h_factor : (fun ω : ℕ → Ω₀ => Y (ω i)) = Y ∘ (fun ω : ℕ → Ω₀ => ω i) := rfl
  have h_aesm :
      AEStronglyMeasurable (fun ω => Real.exp (t * Y ω))
        ((Measure.infinitePi (fun _ : ℕ => μ₀)).map (fun ω : ℕ → Ω₀ => ω i)) := by
    rw [Measure.infinitePi_map_eval]
    exact ((measurable_const.mul hY_meas).exp).aestronglyMeasurable
  have h_mgf_map :
      mgf Y ((Measure.infinitePi (fun _ : ℕ => μ₀)).map (fun ω : ℕ → Ω₀ => ω i)) t
        = mgf (Y ∘ (fun ω : ℕ → Ω₀ => ω i)) (Measure.infinitePi (fun _ : ℕ => μ₀)) t :=
    mgf_map (measurable_pi_apply i).aemeasurable h_aesm
  unfold cgf
  rw [h_factor, ← h_mgf_map, Measure.infinitePi_map_eval]

/-- Under the tilted ambient, the coordinate-eval family is `iIndepFun`. -/
lemma iIndepFun_tilted_ambient
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := by
  haveI hp : IsProbabilityMeasure (μ₀.tilted (fun ω => lam * Y ω)) :=
    isProbabilityMeasure_tilted_of_bounded hY_meas h_bdd lam
  haveI : ∀ i : ℕ, IsProbabilityMeasure
      ((fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) i) := fun _ => hp
  exact iIndepFun_infinitePi (mX := fun _ => hY_meas)

/-- Under the tilted ambient, each coordinate-eval `Y ∘ eval i` is identically
distributed to `Y ∘ eval 0`. -/
lemma identDistrib_tilted_ambient
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    (i : ℕ) :
    IdentDistrib (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := by
  haveI hp : IsProbabilityMeasure (μ₀.tilted (fun ω => lam * Y ω)) :=
    isProbabilityMeasure_tilted_of_bounded hY_meas h_bdd lam
  haveI : ∀ i : ℕ, IsProbabilityMeasure
      ((fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) i) := fun _ => hp
  refine
    { aemeasurable_fst := ?_
      aemeasurable_snd := ?_
      map_eq := ?_ }
  · exact (hY_meas.comp (measurable_pi_apply i)).aemeasurable
  · exact (hY_meas.comp (measurable_pi_apply 0)).aemeasurable
  · have h_push : ∀ k : ℕ,
        (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).map
            (fun ω : ℕ → Ω₀ => Y (ω k))
          = (μ₀.tilted (fun ω => lam * Y ω)).map Y := by
      intro k
      have h_factor :
          (fun ω : ℕ → Ω₀ => Y (ω k)) = Y ∘ (fun ω : ℕ → Ω₀ => ω k) := rfl
      rw [h_factor, ← Measure.map_map hY_meas (measurable_pi_apply k)]
      congr 1
      exact Measure.infinitePi_map_eval _ k
    rw [h_push i, h_push 0]

/-! ## Phase A — coordinate-eval family under the un-tilted base product -/

/-- The coordinate-eval family `X i ω := Y (ω i)` is `iIndepFun` under
`infinitePi μ₀` (un-tilted base product measure). This is a Phase A bystander
needed to invoke the parent `cramer_lower`. -/
lemma iIndepFun_eval_under_infinitePi
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) :
    iIndepFun (fun i : ℕ => fun ω : ℕ → Ω₀ => Y (ω i))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) :=
  iIndepFun_infinitePi (mX := fun _ => hY_meas)

/-- The coordinate-eval family is identically distributed under
`infinitePi μ₀` (un-tilted). -/
lemma identDistrib_eval_under_infinitePi
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y)
    (i : ℕ) :
    IdentDistrib (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) := by
  refine
    { aemeasurable_fst := (hY_meas.comp (measurable_pi_apply i)).aemeasurable
      aemeasurable_snd := (hY_meas.comp (measurable_pi_apply 0)).aemeasurable
      map_eq := ?_ }
  have h_push : ∀ k : ℕ,
      (Measure.infinitePi (fun _ : ℕ => μ₀)).map (fun ω : ℕ → Ω₀ => Y (ω k))
        = μ₀.map Y := by
    intro k
    have h_factor :
        (fun ω : ℕ → Ω₀ => Y (ω k)) = Y ∘ (fun ω : ℕ → Ω₀ => ω k) := rfl
    rw [h_factor, ← Measure.map_map hY_meas (measurable_pi_apply k)]
    congr 1
    exact Measure.infinitePi_map_eval _ k
  rw [h_push i, h_push 0]

end InformationTheory.Shannon.Cramer.Discharge

/-- The coordinate-eval family `X i ω := Y (ω i)` is bounded by the same `M`
that bounds `Y`. -/
lemma InformationTheory.Shannon.Cramer.Discharge.bounded_eval_family
    {Ω₀ : Type*} {Y : Ω₀ → ℝ} (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) :
    ∃ M, ∀ i : ℕ, ∀ ω : ℕ → Ω₀, |Y (ω i)| ≤ M := by
  obtain ⟨M, hM⟩ := h_bdd
  exact ⟨M, fun i ω => hM (ω i)⟩

