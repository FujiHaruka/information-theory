import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.MIBridgeDischarge

/-!
# AWGN mutual-information decomposition

The AWGN mutual-information bridge (Cover–Thomas 9.2.1) states the channel MI
decomposition `I(X;Y) = h(Y) − h(Y∣X)`, with the conditional differential entropy
`h(Y∣X)` realized as the integral of the fibrewise differential entropies. The
AWGN-specific form is `IsAwgnMIDecomp`.

## Main definitions

* `IsContChannelMIDecompHyp p W` — the AWGN-independent, density-level
  mutual-information chain rule `I(X;Y) = h(Y) − h(Y∣X)` for an arbitrary Markov
  channel `W` and input law `p`.

## Main statements

* `awgnChannel_apply_absolutelyContinuous`,
  `awgn_output_absolutelyContinuous_of_outputGaussian` — every AWGN fibre and (given
  the output-Gaussian fact) the output marginal are absolutely continuous w.r.t.
  Lebesgue volume.
* `awgn_midecomp_of_cont_chain`, `cont_chain_of_awgn_midecomp` — at the AWGN
  instance the abstract chain rule and `IsAwgnMIDecomp` are definitionally
  interchangeable.

## Implementation notes

The chain identity `I(X;Y) = h(Y) − h(Y∣X)` is not AWGN-specific: it holds for any
Markov channel whose joint, output, and fibre laws are absolutely continuous w.r.t.
Lebesgue volume (so all differential entropies are density integrals). It is a
density-level identity obtained from the Radon–Nikodym / Bayes split
`rnDeriv (p ⊗ₘ W) (p.prod q) = W(y∣x) / q(y)` together with the differential-entropy
definition. The continuous form is captured by the single AWGN-independent predicate
`IsContChannelMIDecompHyp`, which is strictly more primitive and reusable than the
AWGN-specific `IsAwgnMIDecomp`; the AWGN-specific absolute-continuity side conditions
are discharged here directly from `gaussianReal_absolutelyContinuous`.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Absolute-continuity facts -/

/-- Each AWGN fibre is absolutely continuous w.r.t. Lebesgue volume:
`gaussianReal x N ≪ volume` for `N ≠ 0`. -/
@[entry_point]
theorem awgnChannel_apply_absolutelyContinuous
    (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) :
    (awgnChannel N h_meas) x ≪ volume := by
  rw [awgnChannel_apply]
  exact gaussianReal_absolutelyContinuous x hN

/-- Given the output-Gaussian fact `IsAwgnOutputGaussian`, the output marginal is
`gaussianReal 0 (P.toNNReal + N)`, hence absolutely continuous w.r.t. Lebesgue
volume. -/
@[entry_point]
theorem awgn_output_absolutelyContinuous_of_outputGaussian
    (P : ℝ) (N : ℝ≥0) (hPN : P.toNNReal + N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    (InformationTheory.Shannon.ChannelCoding.outputDistribution
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)) ≪ volume := by
  rw [h_out]
  exact gaussianReal_absolutelyContinuous 0 hPN

/-! ## Continuous-channel mutual-information chain rule predicate -/

/-- The continuous-channel mutual-information chain rule
`(mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W)
− ∫ x, differentialEntropy (W x) ∂p`, i.e. `I(X;Y) = h(Y) − h(Y∣X)`, for an input
law `p` on `ℝ` and a Markov channel `W`. This is the density-based analogue of the
discrete `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`; it requires the joint,
output, and fibre laws to be absolutely continuous w.r.t. Lebesgue volume plus the
relevant integrability, and makes no reference to the AWGN or Gaussian structure. -/
def IsContChannelMIDecompHyp
    (p : Measure ℝ) (W : InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ) : Prop :=
  (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel p W).toReal
    = InformationTheory.Shannon.differentialEntropy
        (InformationTheory.Shannon.ChannelCoding.outputDistribution p W)
      - (∫ x, InformationTheory.Shannon.differentialEntropy (W x) ∂p)

/-! ## Combinator: abstract chain rule → `IsAwgnMIDecomp` -/

/-- `IsAwgnMIDecomp` follows from the abstract continuous MI chain rule. At the AWGN
instance `p := gaussianReal 0 P.toNNReal`, `W := awgnChannel N h_meas`, the abstract
predicate `IsContChannelMIDecompHyp` is definitionally the AWGN predicate
`IsAwgnMIDecomp`, so the discharge is an `exact`. -/
@[entry_point]
theorem awgn_midecomp_of_cont_chain
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_chain : IsContChannelMIDecompHyp
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)) :
    IsAwgnMIDecomp P N h_meas := by
  unfold IsAwgnMIDecomp
  unfold IsContChannelMIDecompHyp at h_chain
  exact h_chain

/-- The reverse direction also holds definitionally — the AWGN predicate is just
the abstract chain rule at the AWGN instance. Confirms the two predicates carry
identical content (no information lost in the abstraction). -/
@[entry_point]
theorem cont_chain_of_awgn_midecomp
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_decomp : IsAwgnMIDecomp P N h_meas) :
    IsContChannelMIDecompHyp
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas) := by
  unfold IsContChannelMIDecompHyp
  unfold IsAwgnMIDecomp at h_decomp
  exact h_decomp

end InformationTheory.Shannon.AWGN
