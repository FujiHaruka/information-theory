import InformationTheory.Shannon.AWGN.BindConvolution
import InformationTheory.Shannon.AWGN.ContChannelMIDecomp

/-!
# AWGN Gaussian-input MI closed form

The hypothesis-free Gaussian-input mutual-information closed form
`I = (1/2)·log(1 + P/N)` (no opaque `h_bridge` hypothesis for the textbook identity
`I = h(P+N) − h(N)`), assembled from the MI decomposition
(`mutualInfoOfChannel_toReal_eq_diffEntropy_sub`, `ContChannelMIDecomp.lean`) and the
output-Gaussian bind/conv bridge (`AWGNBindConvolution.lean`).

`ContChannelMIDecomp.lean`'s own closed-form producer `awgn_mi_gaussian_closed_form_of_out`
still leaves `IsAwgnOutputGaussian` standing as a hypothesis; this file discharges it inline
from the AWGN-specialized, hypothesis-free bind/conv fact `isAwgnBindEqConv_discharged`
(`BindConvolution.lean`), so it is the join point where the fully hypothesis-free wrapper is
assembled.
-/

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-- AWGN channel mutual information, Gaussian input, closed form
`I = (1/2)·log(1 + P/N)`, fully hypothesis-free (takes no `h_bridge`).
The log-algebra is `awgn_mi_gaussian_closed_form_of_primitives` (`MIBridge.lean`). -/
@[entry_point]
theorem mutualInfoOfChannel_gaussianInput_closed_form'
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  -- `h_out` via the bind/conv bridge.
  have h_conv := isAwgnBindEqConv_discharged P N h_meas
  have h_out : IsAwgnOutputGaussian P N h_meas :=
    awgn_output_gaussian_of_bind_eq_conv P N h_meas h_conv
  -- Delegate to the assembled producer (MI decomposition + cond-entropy + log-algebra).
  exact awgn_mi_gaussian_closed_form_of_out P hP N hN h_meas h_out

end InformationTheory.Shannon.AWGN
