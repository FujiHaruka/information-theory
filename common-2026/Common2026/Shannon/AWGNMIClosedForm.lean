import Common2026.Shannon.AWGNBindConvBody
import Common2026.Draft.Shannon.ContChannelMIDecomp

/-!
# AWGN Gaussian-input MI closed form — hypothesis-free successor

[awgn-mi-closed-form-relocation-plan.md](../../docs/shannon/awgn-mi-closed-form-relocation-plan.md).

This file hosts the hypothesis-free successor of the `h_bridge`-form
`mutualInfoOfChannel_gaussianInput_closed_form` (`AWGN.lean:125`). The old form
took the textbook identity `I = h(P+N) − h(N)` as an opaque load-bearing
hypothesis `h_bridge`; the genuine machinery that discharges it lives strictly
**downstream** of `AWGN.lean` (the MI-decomposition wall in `AwgnWalls.lean`, the
output-Gaussian bind/conv bridge in `AWGNBindConvBody.lean`, and the assembled
`awgn_mi_gaussian_closed_form_of_out` in `ContChannelMIDecomp.lean`), so the
closed form must be **relocated** to the lowest file that can see both genuine
producers.

`AWGNBindConvBody` and `ContChannelMIDecomp` are non-importing siblings (both sit
directly under `AWGNMIBridgeDischarge`), so this NEW file imports both and is the
sole place where the hypothesis-free wrapper can be assembled.

The wrapper's own body is **0 sorry**. The former transitive dependency on the
shared MI-decomposition wall `contChannelMIDecomp_holds` has been retired
(closed 2026-05-28: `ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
is now assembled genuinely from local helpers), so this Gaussian-input MI closed form
is now genuine transitively. This file carries no `@residual` tag of its own.
-/

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-- AWGN channel mutual information, Gaussian input, closed form
`I = (1/2)·log(1 + P/N)`, fully hypothesis-free (takes no `h_bridge`).
The former transitive dependency on the shared MI-decomposition wall
`contChannelMIDecomp_holds` has been retired (closed 2026-05-28: the generic body
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` is now genuine), so this is now a
genuine closed form. Hypothesis-free successor of the `h_bridge`-form
`mutualInfoOfChannel_gaussianInput_closed_form` (`AWGN.lean`). -/
@[entry_point]
theorem mutualInfoOfChannel_gaussianInput_closed_form'
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  -- `h_out` is genuine via the bind/conv bridge (both producers genuine, 0 sorry).
  have h_conv := isAwgnBindEqConv_discharged P N h_meas
  have h_out : IsAwgnOutputGaussian P N h_meas :=
    awgn_output_gaussian_of_bind_eq_conv P N h_meas h_conv
  -- Delegate to the assembled producer (MI-decomp genuine + cond-entropy + log-algebra).
  exact awgn_mi_gaussian_closed_form_of_out P hP N hN h_meas h_out

end InformationTheory.Shannon.AWGN
