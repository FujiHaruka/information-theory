import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.OfDensity
import Mathlib.Probability.Independence.Integration   -- IndepFun.integral_fun_mul_eq_mul_integral
import Mathlib.Probability.Independence.Basic          -- IndepFun.comp

/-!
# Score cross-term orthogonality (toward Blachman / Stam)

`E[s_X(X) · s_Y(Y)] = 0` for independent `X, Y` with mean-zero scores. This is the
one Stam/Blachman sub-piece that re-verification (2026-05-30,
`epi-wall-reattack-inventory.md` §2) found to be Mathlib-buildable:
`IndepFun.integral_fun_mul_eq_mul_integral` (`Integration.lean:253`) + repo
score-mean-zero (`FisherInfo.integral_logDeriv_density_eq_zero`). Earlier
inventories (`epi-stam-condexp-score-discharge-mathlib-inventory.md:149`)
mis-flagged this as `Found 0` — the bare-identifier loogle query
`condExp_indep` simply failed; `MeasureTheory.condExp_indep_eq` is real and
`IndepFun.integral_fun_mul_eq_mul_integral` is real.

**NOT the Blachman identity itself** (`wall:stam-blachman`) — that remains a
self-build wall (score-of-convolution `s_Z = E[s_X | σ(X+Y)]`, PR-grade). This
file only supplies the cross-term lemma the Blachman expansion consumes.
-/

namespace InformationTheory.Shannon.EPIScoreCrossTermOrth

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Score cross-term orthogonality (full-expectation version).**
For independent `X, Y` whose score functions `sX, sY` have zero mean (here only
`sX` needs mean zero), the cross-term `∫ sX(X ω) · sY(Y ω) dP = 0`. Built from
`IndepFun.comp` + `IndepFun.integral_fun_mul_eq_mul_integral` + the mean-zero
hypothesis `hmeanX`; NOT a discharge of the Blachman identity (which stays
`@residual(wall:stam-blachman)` in its own file).

`hsXmeas` / `hsYmeas` are `Measurable sX` / `Measurable sY` regularity
preconditions (honest hyp, needed for `IndepFun.comp`), not load-bearing.

Independent audit 2026-05-30: `hmeanX` is a precondition on the *input* score's
mean (`E[sX∘X]=0`), distinct from the conclusion `E[sX·sY]=0` — not circular.
`IndepFun.comp` + `IndepFun.integral_fun_mul_eq_mul_integral` used correctly.
`#print axioms` = [propext, Classical.choice, Quot.sound] (sorryAx-free).
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
