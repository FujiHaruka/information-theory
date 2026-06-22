import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.MutualInfoBridge
import Mathlib.MeasureTheory.Group.Convolution

/-!
# AWGN bind/convolution bridge

The AWGN kernel composed with the Gaussian input law equals the additive
convolution of the input with the noise law,
`(awgnChannel N h_meas) ∘ₘ (gaussianReal 0 P.toNNReal)
= (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)` (`IsAwgnBindEqConv`). This is a
purely measure-theoretic fact that does not depend on the concrete form of the input.

## Main statements

* `bind_eq_conv_of_translation_kernel` — the generic translation-kernel ↔
  additive-convolution bridge: for any kernel whose fibres are translation maps of a
  fixed measure `ν`, `κ ∘ₘ p = p ∗ ν`.
* `isAwgnBindEqConv_discharged` — the AWGN specialization.

## Implementation notes

The two sides are matched through their `lintegral` characterizations
(`Measure.ext_of_lintegral`): the Giry-monad composition expands fibrewise via
`Measure.lintegral_bind`, the convolution via `Measure.lintegral_conv`, and the
fibres agree because each AWGN fibre is the translation map of the noise-only
Gaussian, `gaussianReal x N = (gaussianReal 0 N).map (x + ·)` (Mathlib
`gaussianReal_map_const_add`). The AWGN-specific result is the one-line
specialization of the generic translation-kernel lemma.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Fibre identity: translation map of a Gaussian -/

/-- Each AWGN fibre is the translation map of the noise-only Gaussian:
`gaussianReal x N = (gaussianReal 0 N).map (x + ·)`. -/
theorem gaussianReal_eq_map_const_add (N : ℝ≥0) (x : ℝ) :
    gaussianReal x N = (gaussianReal 0 N).map (x + ·) := by
  rw [gaussianReal_map_const_add (μ := 0) (v := N) x, zero_add]

/-! ## Generic translation-kernel ↔ convolution bridge -/

/-- For any kernel `κ : Kernel ℝ ℝ` whose every fibre is the translation map of a
fixed measure `ν` (`κ x = ν.map (x + ·)`), the Giry-monad composition with an
s-finite input `p` coincides with the additive convolution `p ∗ ν`. -/
@[entry_point]
theorem bind_eq_conv_of_translation_kernel
    (κ : Kernel ℝ ℝ) (p ν : Measure ℝ) [SFinite p] [SFinite ν]
    (hκ : ∀ x, κ x = ν.map (x + ·)) :
    κ ∘ₘ p = p ∗ ν := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  -- LHS: Giry-monad bind expands fibrewise.
  rw [Measure.lintegral_bind κ.aemeasurable hf.aemeasurable]
  -- RHS: convolution expands as a double lintegral over `p ∗ ν`.
  rw [Measure.lintegral_conv hf]
  -- Match fibrewise: `∫⁻ y, f y ∂(κ x) = ∫⁻ y, f (x + y) ∂ν`.
  refine lintegral_congr fun x ↦ ?_
  rw [hκ x, lintegral_map hf (measurable_const_add x)]

/-! ## AWGN specialization -/

/-- The AWGN kernel composed with the Gaussian input equals the additive convolution
with the noise law:
`(awgnChannel N h_meas) ∘ₘ (gaussianReal 0 P.toNNReal)
= (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)`. -/
@[entry_point]
theorem isAwgnBindEqConv_discharged
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) :
    IsAwgnBindEqConv P N h_meas := by
  unfold IsAwgnBindEqConv
  refine bind_eq_conv_of_translation_kernel
    (awgnChannel N h_meas) (gaussianReal 0 P.toNNReal) (gaussianReal 0 N) ?_
  intro x
  rw [awgnChannel_apply]
  exact gaussianReal_eq_map_const_add N x

/-- The AWGN capacity closed form, with the output-Gaussian fact discharged via the
bind/convolution bridge (so `IsAwgnBindEqConv` is supplied automatically) and the MI
decomposition `h_decomp`, boundedness `h_bdd`, and max-entropy bound `h_max_ent`
taken as hypotheses.

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form_of_maxent_bindconv_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ ↦
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N (isAwgnChannelMeasurable N))).toReal) ''
          awgnPowerConstraintSet P))
    (h_max_ent :
        ∀ p ∈ awgnPowerConstraintSet P,
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have h_bridge : IsAwgnBindEqConv P N (isAwgnChannelMeasurable N) :=
    isAwgnBindEqConv_discharged P N (isAwgnChannelMeasurable N)
  exact awgn_capacity_closed_form_of_maxent_bindconv P hP N hN
    h_bridge h_decomp h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
