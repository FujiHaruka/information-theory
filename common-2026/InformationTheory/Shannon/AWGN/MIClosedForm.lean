import InformationTheory.Shannon.AWGN.BindConvolution
import InformationTheory.Shannon.AWGN.ContChannelMIDecomp

/-!
# AWGN Gaussian-input MI closed form — hypothesis-free successor

This file hosts the hypothesis-free Gaussian-input MI closed form. The old
`h_bridge`-form wrapper `AWGN.mutualInfoOfChannel_gaussianInput_closed_form`
(took the textbook identity `I = h(P+N) − h(N)` as an opaque load-bearing
hypothesis `h_bridge`) has been retired; its log-algebra was inlined into
`AWGNMIBridge.awgn_mi_gaussian_closed_form_of_primitives`, where the bridge is
genuinely discharged. The genuine machinery that discharges the bridge lives strictly
downstream of `AWGN.lean` (the MI-decomposition wall in `AwgnWalls.lean`, the
output-Gaussian bind/conv bridge in `AWGNBindConvolution.lean`, and the assembled
`awgn_mi_gaussian_closed_form_of_out` in `ContChannelMIDecomp.lean`), so the
closed form must be relocated to the lowest file that can see both genuine
producers.

`AWGNBindConvolution` and `ContChannelMIDecomp` are non-importing siblings (both sit
directly under `AWGNMutualInfoBridge`), so this NEW file imports both and is the
sole place where the hypothesis-free wrapper can be assembled.

The MI-decomposition is assembled genuinely from local helpers via
`ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`, so this
Gaussian-input MI closed form is genuine transitively. This file carries no
`@residual` tag of its own.
-/

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-- AWGN channel mutual information, Gaussian input, closed form
`I = (1/2)·log(1 + P/N)`, fully hypothesis-free (takes no `h_bridge`).
The MI-decomposition generic body
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` is genuine, so this is a
genuine closed form. The log-algebra of the former `h_bridge`-form wrapper is
inlined into `AWGNMIBridge.awgn_mi_gaussian_closed_form_of_primitives`. -/
@[entry_point]
theorem mutualInfoOfChannel_gaussianInput_closed_form'
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  -- `h_out` is genuine via the bind/conv bridge (both producers genuine).
  have h_conv := isAwgnBindEqConv_discharged P N h_meas
  have h_out : IsAwgnOutputGaussian P N h_meas :=
    awgn_output_gaussian_of_bind_eq_conv P N h_meas h_conv
  -- Delegate to the assembled producer (MI-decomp genuine + cond-entropy + log-algebra).
  exact awgn_mi_gaussian_closed_form_of_out P hP N hN h_meas h_out

end InformationTheory.Shannon.AWGN
