import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.MIBridge

/-!
# AWGN output marginal is Gaussian

The AWGN channel output marginal under Gaussian input is itself Gaussian:

```
IsAwgnOutputGaussian P N h_meas
  := (outputDistribution (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas))
        = gaussianReal 0 (P.toNNReal + N)
```

that is, for `Y = X + Z` with `X ∼ 𝒩(0, P)` and independent `Z ∼ 𝒩(0, N)` one has
`Y ∼ 𝒩(0, P + N)`.

## Main definitions

* `IsAwgnBindEqConv` — the bridge identity stating that the AWGN kernel composition
  equals additive convolution of measures.

## Main statements

* `awgn_output_gaussian_of_bind_eq_conv` — the output marginal is `𝒩(0, P + N)`,
  given the bind/conv bridge.
* `awgn_capacity_closed_form_of_maxent_bindconv` — the capacity closed form with the
  output-Gaussian fact reduced to the bind/conv bridge, the remaining mutual-information
  facts taken as hypotheses.

## Implementation notes

The output marginal is computed in three structural steps: `outputDistribution` is
the second marginal of the joint law (definitional), `(p ⊗ₘ W).snd = W ∘ₘ p` is the
Markov-kernel composition identity (`Measure.snd_compProd`), and
`gaussianReal_conv_gaussianReal` collapses the convolution of two Gaussians into a
single Gaussian.

The middle step — that the AWGN kernel composition coincides with additive
convolution — is a generic translation-kernel identity that is independent of the
AWGN specifics. Discharging it inline through the characteristic-function route would
inflate the file by roughly 80–100 lines (`lintegral` expansion, Fubini, change of
variables), so it is exposed as the single named hypothesis `IsAwgnBindEqConv` and
discharged separately.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-- The bridge identity stating that, for the AWGN translation kernel `awgnChannel N`
and Gaussian input `p := gaussianReal 0 P.toNNReal`, the kernel composition coincides
with the additive convolution of measures:

```
awgnChannel N ∘ₘ (gaussianReal 0 P.toNNReal)
  = (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)
```

This is an AWGN-independent measure-theoretic fact: any translation kernel
`κ x = ν.map (x + ·)` satisfies `κ ∘ₘ p = p ∗ ν` for s-finite `p` and finite `ν`, by
Fubini and change of variables. It is exposed as a named hypothesis so the
output-Gaussian computation does not have to expand it inline. -/
def IsAwgnBindEqConv (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (awgnChannel N h_meas) ∘ₘ (gaussianReal 0 P.toNNReal)
    = (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)

/-- The AWGN channel output marginal under Gaussian input equals `𝒩(0, P + N)`, given
the bind/conv bridge `IsAwgnBindEqConv P N h_meas`.

The proof chains `outputDistribution = compProd.snd` (definitional),
`Measure.snd_compProd`, the bridge hypothesis, and `gaussianReal_conv_gaussianReal`. -/
@[entry_point]
theorem awgn_output_gaussian_of_bind_eq_conv
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_bridge : IsAwgnBindEqConv P N h_meas) :
    IsAwgnOutputGaussian P N h_meas := by
  unfold IsAwgnOutputGaussian
  unfold InformationTheory.Shannon.ChannelCoding.outputDistribution
  unfold InformationTheory.Shannon.ChannelCoding.jointDistribution
  -- Step 1: (p ⊗ₘ W).snd = W ∘ₘ p.
  rw [Measure.snd_compProd]
  -- Step 2: kernel composition = additive convolution (named hypothesis).
  rw [h_bridge]
  -- Step 3: Gaussian + Gaussian = Gaussian (Mathlib).
  -- `gaussianReal_conv_gaussianReal` gives mean `0+0 = 0`; normalize.
  have := gaussianReal_conv_gaussianReal
      (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ)) (v₁ := P.toNNReal) (v₂ := N)
  simpa using this

/-- The AWGN capacity closed form, with the output-Gaussian fact reduced to the
bind/conv bridge `IsAwgnBindEqConv`. The mutual-information decomposition
(`h_decomp`), the boundedness `h_bdd`, and the max-entropy bound (`h_max_ent`)
remain as hypotheses; only the output-Gaussian fact is supplied here.

`@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form_of_maxent_bindconv
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge : IsAwgnBindEqConv P N (isAwgnChannelMeasurable N))
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
  have h_out : IsAwgnOutputGaussian P N (isAwgnChannelMeasurable N) :=
    awgn_output_gaussian_of_bind_eq_conv P N (isAwgnChannelMeasurable N) h_bridge
  exact awgn_capacity_closed_form_F2_discharged P hP N hN
    h_out h_decomp h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
