import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.MIBridgeDischarge
import Mathlib.MeasureTheory.Group.Convolution

/-!
# W9-S1 T2-A: body discharge of `IsAwgnBindEqConv`

Wave7 で publish した `InformationTheory/Shannon/AWGNMIBridgeDischarge.lean` は
`IsAwgnOutputGaussian` を named hypothesis `IsAwgnBindEqConv` に縮減した:

```
IsAwgnBindEqConv P N h_meas
  := (awgnChannel N h_meas) ∘ₘ (gaussianReal 0 P.toNNReal)
       = (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)
```

本 file はこの translation-kernel ↔ additive-convolution bridge を **完全 discharge**
する。AWGN 独立な純粋測度論的事実であり、入力 `p := gaussianReal 0 P.toNNReal`
の具体形には依存しない。

## Approach

`κ ∘ₘ p = Measure.bind p κ` (Giry monad bind, `CompNotation`), `p ∗ ν = (p.prod ν).map (·+·)`
(`Measure.conv`)。両者を `lintegral` 経由で一致させる (`Measure.ext_of_lintegral`):

```
∫⁻ y, f y ∂(κ ∘ₘ p)  = ∫⁻ x, ∫⁻ y, f y ∂(κ x) ∂p        -- lintegral_bind
∫⁻ y, f y ∂(p ∗ ν)   = ∫⁻ x, ∫⁻ y, f (x+y) ∂ν ∂p         -- lintegral_conv
```

x ごとの fibre は `awgnChannel N x = gaussianReal x N`。Mathlib
`gaussianReal_map_const_add` で `gaussianReal x N = (gaussianReal 0 N).map (x + ·)`、
`lintegral_map` で fibre 一致:

```
∫⁻ y, f y ∂(gaussianReal x N)
  = ∫⁻ y, f y ∂((gaussianReal 0 N).map (x + ·))
  = ∫⁻ y, f (x + y) ∂(gaussianReal 0 N).
```

## 一般化レイヤ

主補題 `bind_eq_conv_of_translation_kernel` は AWGN に依存しない一般 translation
kernel `κ x = ν.map (x + ·)` (s-finite `p`, sfinite `ν`) について `κ ∘ₘ p = p ∗ ν`
を示す。AWGN への特殊化はこの一般補題 + `gaussianReal_map_const_add` で 1 行。

## Mathlib gap

`Kernel.comp_eq_conv_of_translation` 相当 (translation-kernel ↔ conv) は Mathlib
未掲載。本 file の `bind_eq_conv_of_translation_kernel` がその generic 形を publish。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — fibre identity: translation map of a Gaussian -/

/-- Each AWGN fibre is the translation map of the noise-only Gaussian:
`gaussianReal x N = (gaussianReal 0 N).map (x + ·)`.
Direct corollary of Mathlib `gaussianReal_map_const_add` (mean `0 + x = x`). -/
theorem gaussianReal_eq_map_const_add (N : ℝ≥0) (x : ℝ) :
    gaussianReal x N = (gaussianReal 0 N).map (x + ·) := by
  rw [gaussianReal_map_const_add (μ := 0) (v := N) x, zero_add]

/-! ## Phase B — generic translation-kernel ↔ convolution bridge -/

/-- **Translation-kernel ↔ additive-convolution bridge (generic).**

For any kernel `κ : Kernel ℝ ℝ` whose every fibre is the translation map of a fixed
finite measure `ν` (`κ x = ν.map (x + ·)`), the Giry-monad composition with an
s-finite input `p` coincides with the additive convolution `p ∗ ν`. -/
@[entry_point]
theorem bind_eq_conv_of_translation_kernel
    (κ : Kernel ℝ ℝ) (p ν : Measure ℝ) [SFinite p] [SFinite ν]
    (hκ : ∀ x, κ x = ν.map (x + ·)) :
    κ ∘ₘ p = p ∗ ν := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- LHS: Giry-monad bind expands fibrewise.
  rw [Measure.lintegral_bind κ.aemeasurable hf.aemeasurable]
  -- RHS: convolution expands as a double lintegral over `p ∗ ν`.
  rw [Measure.lintegral_conv hf]
  -- Match fibrewise: `∫⁻ y, f y ∂(κ x) = ∫⁻ y, f (x + y) ∂ν`.
  refine lintegral_congr fun x => ?_
  rw [hκ x, lintegral_map hf (measurable_const_add x)]

/-! ## Phase C — AWGN specialization: discharge `IsAwgnBindEqConv` -/

/-- **`IsAwgnBindEqConv` body discharge.**

The AWGN kernel composed with the Gaussian input equals the additive convolution
with the noise law:
`(awgnChannel N h_meas) ∘ₘ (gaussianReal 0 P.toNNReal)
  = (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)`.

Specialization of `bind_eq_conv_of_translation_kernel` with `ν := gaussianReal 0 N`
and the fibre identity `gaussianReal_eq_map_const_add`. -/
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

/-- **AWGN capacity closed form — output-Gaussian (bind/conv) genuinely closed,
MI-decomp/bddAbove/max-entropy taken as hypotheses.**

⚠️ NOT a full discharge: the MI decomposition (`h_decomp`), `h_bdd` and the
max-entropy bound (`h_max_ent`) remain OPEN — taken as hypotheses (max-entropy /
continuous MI chain rule machinery absent from Mathlib). Only the output-Gaussian
fact is genuinely closed via the now-proved bind/conv bridge, so `IsAwgnBindEqConv`
is dispatched automatically.

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form_of_maxent_bindconv_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
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
