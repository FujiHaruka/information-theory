import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The random Gaussian codebook

The random codebook law for AWGN achievability (Cover–Thomas 9.2): `M` codewords,
each with `n` i.i.d. `𝒩(0, σsq)` components, carried by `Fin M → Fin n → ℝ` and
built as a two-stage `Measure.pi` so that it is definitionally equal to
`AwgnCode.encoder`.

## Main definitions

* `gaussianCodebook M n σsq` — the random codebook law.

## Main statements

* `gaussianCodebook_codeword_law` — projecting onto a single codeword index gives
  the inner i.i.d. Gaussian product measure.
* `gaussianCodebook_indepFun_codewords` — distinct codewords are independent.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Random Gaussian codebook -/

/-- The random Gaussian codebook: `M` codewords, each `n` i.i.d. components
`X(m, i) ∼ 𝒩(0, σsq)`, built as a two-stage `Measure.pi`. The concrete carrier
type `Fin M → Fin n → ℝ` matches `AwgnCode.encoder` definitionally, so no
measurable-equivalence transport is needed. -/
noncomputable def gaussianCodebook (M n : ℕ) (σsq : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))

/-- `gaussianCodebook M n σsq` is a probability measure (2-stage `Measure.pi` of
the probability measure `gaussianReal 0 σsq`). All instances autoderive via
`pi.instIsProbabilityMeasure` + `instIsProbabilityMeasureGaussianReal`. -/
instance gaussianCodebook_isProbabilityMeasure (M n : ℕ) (σsq : ℝ≥0) :
    IsProbabilityMeasure (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook; infer_instance

/-- Projecting `gaussianCodebook` onto codeword index `m` gives back the inner
i.i.d. Gaussian product measure on `Fin n → ℝ`. -/
@[entry_point]
theorem gaussianCodebook_codeword_law (M n : ℕ) (σsq : ℝ≥0) (m : Fin M) :
    (gaussianCodebook M n σsq).map (fun c : Fin M → Fin n → ℝ => c m)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 σsq) := by
  unfold gaussianCodebook
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq)) m).map_eq

/-- Under the codebook law, distinct codewords `c m`, `c m'` are independent
random variables. -/
@[entry_point]
theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σsq : ℝ≥0)
    {m m' : Fin M} (hmm' : m ≠ m') :
    IndepFun (fun c : Fin M → Fin n → ℝ => c m)
             (fun c : Fin M → Fin n → ℝ => c m')
             (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook
  have h_iIndep :
      iIndepFun (fun (i : Fin M) (ω : Fin M → Fin n → ℝ) => ω i)
        (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))) := by
    have :=
      iIndepFun_pi (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))
        (X := fun (_ : Fin M) (x : Fin n → ℝ) => x)
        (fun _ => aemeasurable_id)
    exact this
  exact h_iIndep.indepFun hmm'

end InformationTheory.Shannon.AWGN
