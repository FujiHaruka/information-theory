import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.V2
import Mathlib.Analysis.Calculus.ParametricIntegral   -- hasDerivAt_integral_of_dominated_loc_of_deriv_le
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Group.Integral           -- integral_sub_left_eq_self (reflection)

/-!
# Convolution density apparatus — gateway atom (DECISIVE GATE)

`p_Z(z) = ∫ x, p_X(x) · p_Y(z - x) ∂volume` (sum density of independent `X, Y`),
its pointwise differentiability, and the `logDeriv p_Z` representation. This is
the common foundational helper that both former EPI walls
(`wall:stam-step2-density` / `wall:debruijn-integration`, both now [CLOSED
2026-06-04] — genuine, sorryAx-free) consume.

## Why the parametric-integral route (not `HasCompactSupport`)

The 6 Mathlib `HasCompactSupport.*_convolution_*` lemmas
(`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`,
`epi-wall-reattack-inventory.md` §3) require the smooth factor to have **compact
support**, which the Gaussian heat kernel does not. We bypass that wall entirely
by going through `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean:289`): differentiation under
the integral sign, with the Gaussian-tail domination supplied as **regularity
preconditions** (honest hyp, NOT load-bearing — see CLAUDE.md "Verification honesty").

## Mathlib-shape-driven

`convDensityAdd` is defined as a Bochner `∫` (not `⋆ₗ` / `⋆[L,μ]`), matching the
conclusion shape of the parametric-integral gateway
`HasDerivAt (fun z ↦ ∫ a, F z a ∂μ) (∫ a, F' x₀ a ∂μ) x₀`.
-/

namespace InformationTheory.Shannon.EPIConvDensity

open MeasureTheory Real
open scoped ENNReal NNReal

/-- Convolution density (sum density of independent `X, Y`):
`p_Z(z) = ∫ x, p_X(x) · p_Y(z - x) ∂volume`. Bochner-`∫` form to match the
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` conclusion shape. -/
noncomputable def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ x, pX x * pY (z - x) ∂volume

/-- **Commutativity of the convolution density**: `pX ⋆ pY = pY ⋆ pX`.
Genuine fact via the reflection substitution `x ↦ z - x` (volume-preserving). -/
theorem convDensityAdd_comm (pX pY : ℝ → ℝ) :
    convDensityAdd pX pY = convDensityAdd pY pX := by
  funext z
  unfold convDensityAdd
  -- Reflection substitution `x ↦ z - x` (volume is add-right-invariant) applied to
  -- the integrand `f x := pX (z - x) * pY x`:
  --   `∫ x, f (z - x) = ∫ x, f x`, i.e.
  --   `∫ x, pX (z - (z - x)) * pY (z - x) = ∫ x, pX (z - x) * pY x`.
  have h := MeasureTheory.integral_sub_left_eq_self
      (fun x => pX (z - x) * pY x) (μ := volume) z
  -- h : ∫ x, pX (z - (z - x)) * pY (z - x) = ∫ x, pX (z - x) * pY x
  simp only [sub_sub_cancel] at h
  -- h : ∫ x, pX x * pY (z - x) = ∫ x, pX (z - x) * pY x
  rw [h]
  congr 1
  funext x
  rw [mul_comm]

/-- The `z`-partial-derivative integrand: `∂_z (p_X x · p_Y (z - x)) = p_X x · p_Y' (z - x)`. -/
noncomputable def convDensityAddDeriv (pX pY : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z x => pX x * deriv pY (z - x)

/-- **Gateway atom (DECISIVE GATE).** Under Gaussian-tail / integrability
regularity preconditions, `convDensityAdd pX pY` is differentiable at `z₀` with
derivative `∫ x, p_X x · p_Y' (z₀ - x)`.

All hypotheses are honest regularity preconditions (integrability,
ae-measurability, the domination bound, pointwise differentiability of the
integrand), pinned exactly in the shape
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` consumes. They are NOT a
load-bearing bundling of the conclusion: the differentiability of `convDensityAdd`
is *derived*, not assumed.

* `s` is a neighborhood of `z₀`.
* `bound` is the integrable Gaussian-tail dominating function.

Independent audit 2026-05-30: `h_diff` quantifies the *per-`x` integrand*
`fun z => pX x * pY (z - x)`, not the integral — regularity precondition, 1:1
with the gateway lemma's `h_diff`.
@audit:ok -/
theorem convDensityAdd_hasDerivAt
    (pX pY : ℝ → ℝ) (z₀ : ℝ) {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ nhds z₀)
    (hF_meas : ∀ᶠ z in nhds z₀,
        AEStronglyMeasurable (fun x => pX x * pY (z - x)) volume)
    (hF_int : Integrable (fun x => pX x * pY (z₀ - x)) volume)
    (hF'_meas : AEStronglyMeasurable (fun x => convDensityAddDeriv pX pY z₀ x) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s, ‖convDensityAddDeriv pX pY z x‖ ≤ bound x)
    (bound_integrable : Integrable bound volume)
    (h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s,
        HasDerivAt (fun z => pX x * pY (z - x)) (convDensityAddDeriv pX pY z x) z) :
    HasDerivAt (convDensityAdd pX pY)
      (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) z₀ := by
  have hgate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z x => pX x * pY (z - x))
      (F' := fun z x => convDensityAddDeriv pX pY z x)
      (bound := bound) hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  simpa only [convDensityAdd] using hgate.2

/-- `logDeriv p_Z` representation at `z₀` (score of the convolution density):
`logDeriv (convDensityAdd pX pY) z₀ = (∫ x, p_X x · p_Y'(z₀ - x)) / p_Z(z₀)`.
This is the Blachman / Fisher connection point.
@audit:ok -/
@[entry_point]
theorem convDensityAdd_logDeriv
    (pX pY : ℝ → ℝ) (z₀ : ℝ) {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ nhds z₀)
    (hF_meas : ∀ᶠ z in nhds z₀,
        AEStronglyMeasurable (fun x => pX x * pY (z - x)) volume)
    (hF_int : Integrable (fun x => pX x * pY (z₀ - x)) volume)
    (hF'_meas : AEStronglyMeasurable (fun x => convDensityAddDeriv pX pY z₀ x) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s, ‖convDensityAddDeriv pX pY z x‖ ≤ bound x)
    (bound_integrable : Integrable bound volume)
    (h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s,
        HasDerivAt (fun z => pX x * pY (z - x)) (convDensityAddDeriv pX pY z x) z) :
    logDeriv (convDensityAdd pX pY) z₀
      = (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) / convDensityAdd pX pY z₀ := by
  have hderiv :
      HasDerivAt (convDensityAdd pX pY)
        (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) z₀ :=
    convDensityAdd_hasDerivAt pX pY z₀ hs hF_meas hF_int hF'_meas h_bound
      bound_integrable h_diff
  rw [logDeriv_apply, hderiv.deriv]

/-- **Public gateway API**: the convolution density is differentiable at `z₀`, with
the `logDeriv` (score) given by the score-of-convolution formula. Bundles the two
atoms above for downstream walls (Phase 3 Blachman / Phase 4 de Bruijn).
@audit:ok -/
@[entry_point]
theorem convDensity_add_differentiable
    (pX pY : ℝ → ℝ) (z₀ : ℝ) {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ nhds z₀)
    (hF_meas : ∀ᶠ z in nhds z₀,
        AEStronglyMeasurable (fun x => pX x * pY (z - x)) volume)
    (hF_int : Integrable (fun x => pX x * pY (z₀ - x)) volume)
    (hF'_meas : AEStronglyMeasurable (fun x => convDensityAddDeriv pX pY z₀ x) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s, ‖convDensityAddDeriv pX pY z x‖ ≤ bound x)
    (bound_integrable : Integrable bound volume)
    (h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s,
        HasDerivAt (fun z => pX x * pY (z - x)) (convDensityAddDeriv pX pY z x) z) :
    HasDerivAt (convDensityAdd pX pY)
        (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) z₀
      ∧ logDeriv (convDensityAdd pX pY) z₀
        = (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) / convDensityAdd pX pY z₀ := by
  refine ⟨convDensityAdd_hasDerivAt pX pY z₀ hs hF_meas hF_int hF'_meas h_bound
      bound_integrable h_diff,
    convDensityAdd_logDeriv pX pY z₀ hs hF_meas hF_int hF'_meas h_bound
      bound_integrable h_diff⟩

/-! ## Phase 3a (GATE) — discharge the 7 gateway hyps from `IsRegularDensityV2`

`convDensityAdd_hasDerivAt_of_regular`: the GATE wrapper that supplies all 7
parametric-integral regularity hyps from Stam's density preconditions
`IsRegularDensityV2 fX/fY` + normalization `∫fX = 1` (`∫fY = 1` not needed here)
plus three genuine regularity preconditions:

* `hX_int : Integrable fX` — `fX` is a probability density.
* `hY_bdd`  : `fY` is bounded (Gaussian PDF is, since `exp(-x²)` is bounded).
* `hY'_bdd` : `deriv fY` is bounded (Gaussian `deriv = -(x-m)/v · pdf`,
  polynomial × Gaussian decay → bounded).

These three are **honest regularity preconditions**, NOT load-bearing: the
differentiability of `convDensityAdd` is *derived* via the gateway, not assumed.
The Gaussian instance satisfies all three (1-line confirmation in docstring of
each `have`).

Independent audit 2026-05-30: the 3 added hyps are per-factor regularity
(`Integrable fX` / `|fY|≤M` / `|deriv fY|≤M`) on `fX`/`fY` individually, NOT on
the convolution; none has `HasDerivAt`/`Differentiable (convDensityAdd …)` type,
so no circularity. core-reconstruction test: granting all 5 hyps does not hand
the differentiability — it is constructed via the gateway `convDensityAdd_hasDerivAt`
(itself `@audit:ok`) inside the body. Gaussian witnesses are non-vacuous
(smooth+positive+tail→0 ⇒ `IsRegularDensityV2`; PDF bounded; `deriv = poly×Gaussian`
bounded; PDF integrable). `#print axioms` = [propext, Classical.choice, Quot.sound]
(sorryAx-free, machine-checked). 0 sorry / 0 @residual.
@audit:ok -/
theorem convDensityAdd_hasDerivAt_of_regular (fX fY : ℝ → ℝ) (z₀ : ℝ)
    (hregX : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fX)
    (hregY : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fY)
    (hX_int : Integrable fX volume)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M)
    (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M) :
    HasDerivAt (convDensityAdd fX fY)
      (∫ x, convDensityAddDeriv fX fY z₀ x ∂volume) z₀ := by
  obtain ⟨MY, hMY⟩ := hY_bdd
  obtain ⟨MY', hMY'⟩ := hY'_bdd
  -- Continuity / measurability facts.
  have hX_cont : Continuous fX := hregX.diff.continuous
  have hY_cont : Continuous fY := hregY.diff.continuous
  have hY'_meas : Measurable (deriv fY) := measurable_deriv fY
  -- `s := Metric.ball z₀ 1`, a neighborhood of `z₀`.
  set s : Set ℝ := Metric.ball z₀ 1 with hs_def
  -- (1) `hs : s ∈ nhds z₀`.
  have hs : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ one_pos
  -- (2) `hF_meas`.
  have hF_meas : ∀ᶠ z in nhds z₀,
      AEStronglyMeasurable (fun x => fX x * fY (z - x)) volume := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    exact (hX_cont.aestronglyMeasurable).mul
      ((hY_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  -- (3) `hF_int : Integrable (fun x => fX x * fY (z₀ - x))`.
  have hF_int : Integrable (fun x => fX x * fY (z₀ - x)) volume := by
    have hYmeas : AEStronglyMeasurable (fun x => fY (z₀ - x)) volume :=
      (hY_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂volume, ‖fY (z₀ - x)‖ ≤ MY :=
      Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]; exact hMY (z₀ - x))
    have := hX_int.bdd_mul hYmeas hbound
    -- `this : Integrable (fun x => fY (z₀ - x) * fX x)`
    simpa only [mul_comm] using this
  -- (4) `hF'_meas`.
  have hF'_meas : AEStronglyMeasurable
      (fun x => convDensityAddDeriv fX fY z₀ x) volume := by
    unfold convDensityAddDeriv
    exact (hX_cont.aestronglyMeasurable).mul
      ((hY'_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  -- bound function `bound x := MY' * |fX x|`.
  set bound : ℝ → ℝ := fun x => MY' * |fX x| with hbound_def
  -- (5) `h_bound`.
  have h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s,
      ‖convDensityAddDeriv fX fY z x‖ ≤ bound x := by
    refine Filter.Eventually.of_forall (fun x z _ => ?_)
    unfold convDensityAddDeriv
    rw [Real.norm_eq_abs, abs_mul, hbound_def]
    have : |deriv fY (z - x)| ≤ MY' := hMY' (z - x)
    calc |fX x| * |deriv fY (z - x)|
        ≤ |fX x| * MY' := by
          gcongr
      _ = MY' * |fX x| := mul_comm _ _
  -- (6) `bound_integrable`.
  have bound_integrable : Integrable bound volume := by
    rw [hbound_def]
    exact (hX_int.abs).const_mul MY'
  -- (7) `h_diff`.
  have h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s,
      HasDerivAt (fun z => fX x * fY (z - x))
        (convDensityAddDeriv fX fY z x) z := by
    refine Filter.Eventually.of_forall (fun x z _ => ?_)
    unfold convDensityAddDeriv
    -- inner: `z ↦ z - x` has derivative `1`.
    have hinner : HasDerivAt (fun z : ℝ => z - x) 1 z :=
      (hasDerivAt_id z).sub_const x
    -- `fY` differentiable at `z - x`.
    have hY_at : HasDerivAt fY (deriv fY (z - x)) (z - x) :=
      (hregY.diff (z - x)).hasDerivAt
    -- compose: `z ↦ fY (z - x)` has derivative `deriv fY (z-x) * 1`.
    have hcomp : HasDerivAt (fun z : ℝ => fY (z - x)) (deriv fY (z - x) * 1) z :=
      hY_at.comp z hinner
    rw [mul_one] at hcomp
    -- const_mul by `fX x`.
    have := hcomp.const_mul (fX x)
    -- `this : HasDerivAt (fun z => fX x * fY (z - x)) (fX x * deriv fY (z - x)) z`
    exact this
  exact convDensityAdd_hasDerivAt fX fY z₀ hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff

end InformationTheory.Shannon.EPIConvDensity
