import Common2026.Shannon.FisherInfoV2
import Mathlib.Analysis.Calculus.ParametricIntegral   -- hasDerivAt_integral_of_dominated_loc_of_deriv_le
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Group.Integral           -- integral_sub_left_eq_self (reflection)

/-!
# Convolution density apparatus — gateway atom (DECISIVE GATE)

`p_Z(z) = ∫ x, p_X(x) · p_Y(z - x) ∂volume` (sum density of independent `X, Y`),
its pointwise differentiability, and the `logDeriv p_Z` representation. This is
the common foundational helper that both EPI walls
(`wall:stam-step2-density` / `wall:debruijn-integration`) consume.

## Why the parametric-integral route (not `HasCompactSupport`)

The 6 Mathlib `HasCompactSupport.*_convolution_*` lemmas
(`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`,
`epi-wall-reattack-inventory.md` §3) require the smooth factor to have **compact
support**, which the Gaussian heat kernel does not. We bypass that wall entirely
by going through `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean:289`): differentiation under
the integral sign, with the Gaussian-tail domination supplied as **regularity
preconditions** (honest hyp, NOT load-bearing — see CLAUDE.md「検証の誠実性」).

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
with the gateway lemma's `h_diff`. All 7 hyps are regularity (no load-bearing).
`#print axioms` = [propext, Classical.choice, Quot.sound] (sorryAx-free).
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

Independent audit 2026-05-30: genuine, sorryAx-free
(`#print axioms` = [propext, Classical.choice, Quot.sound]).
@audit:ok -/
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

Independent audit 2026-05-30: genuine, sorryAx-free.
`#print axioms` = [propext, Classical.choice, Quot.sound].
@audit:ok -/
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

end InformationTheory.Shannon.EPIConvDensity
