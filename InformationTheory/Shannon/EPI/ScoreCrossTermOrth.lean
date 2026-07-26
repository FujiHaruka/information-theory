import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.OfDensity
import Mathlib.Probability.Independence.Integration   -- IndepFun.integral_fun_mul_eq_mul_integral
import Mathlib.Probability.Independence.Basic          -- IndepFun.comp

/-!
# Score cross-term orthogonality (toward Blachman / Stam)

`E[s_X(X) · s_Y(Y)] = 0` for independent `X, Y` with mean-zero scores. Independence
factors the expectation (`IndepFun.integral_fun_mul_eq_mul_integral`), and the
mean-zero score factor kills the product; the mean-zero input itself comes from
`FisherInfo.integral_logDeriv_density_eq_zero`.

This is the cross-term a Blachman-style score expansion consumes; the
score-of-convolution identity `s_Z = E[s_X | σ(X+Y)]` itself is not proved here.
-/

namespace InformationTheory.Shannon.EPIScoreCrossTermOrth

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Score cross-term orthogonality (full-expectation version).
For independent `X, Y` whose score functions `sX, sY` have zero mean (here only
`sX` needs mean zero), the cross-term `∫ sX(X ω) · sY(Y ω) dP = 0`. Built from
`IndepFun.comp` + `IndepFun.integral_fun_mul_eq_mul_integral` + the mean-zero
hypothesis `hmeanX`. This is not the Blachman score-of-convolution identity.

`hsXmeas` / `hsYmeas` are `Measurable sX` / `Measurable sY` regularity
preconditions (needed for `IndepFun.comp`), not load-bearing. `hmeanX`
constrains the *input* score's mean (`E[sX∘X] = 0`), which is distinct from the
conclusion `E[sX·sY] = 0`.
@audit:ok -/
@[entry_point]
theorem score_cross_term_eq_zero
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {sX sY : ℝ → ℝ}
    (hXY : IndepFun X Y P)
    (hsXmeas : Measurable sX) (hsYmeas : Measurable sY)
    (hsX : AEStronglyMeasurable (fun ω ↦ sX (X ω)) P)
    (hsY : AEStronglyMeasurable (fun ω ↦ sY (Y ω)) P)
    (hmeanX : ∫ ω, sX (X ω) ∂P = 0) :
    ∫ ω, sX (X ω) * sY (Y ω) ∂P = 0 := by
  have hindep : IndepFun (fun ω ↦ sX (X ω)) (fun ω ↦ sY (Y ω)) P :=
    hXY.comp hsXmeas hsYmeas
  have hsplit :
      ∫ ω, sX (X ω) * sY (Y ω) ∂P
        = (∫ ω, sX (X ω) ∂P) * (∫ ω, sY (Y ω) ∂P) :=
    hindep.integral_fun_mul_eq_mul_integral hsX hsY
  rw [hsplit, hmeanX, zero_mul]

end InformationTheory.Shannon.EPIScoreCrossTermOrth
