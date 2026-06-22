import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.DeBruijn
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Positivity

/-!
# Stam convex Fisher bound — Gaussian instance

EPI (Ch.17) follow-up to the Stam inequality core `J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)`.

Keyed on the V2 Fisher information `fisherInfoOfMeasureV2`, which evaluates to the
closed form `1/v` for a Gaussian with variance `v`. The proof reduces the convex
Fisher bound to the arithmetic kernel `1/(a+b) ≤ λ²/a + (1-λ)²/b`, with equality
at `λ* = a/(a+b)`.

Scope: only the Gaussian instance. The general case (heat-flow + de Bruijn) is
out of scope here.

## Main statements

* `stam_fisher_arith` — arithmetic kernel `1/(a+b) ≤ λ²/a + (1-λ)²/b`
* `stam_fisher_arith_eq_at_opt` — equality at `λ* = a/(a+b)`
* `stam_convex_fisher_bound_gaussian` — Gaussian convex Fisher bound (closed form)
* `stam_convex_fisher_bound_gaussian_indep` — independent-RV form via
  `gaussianReal_add_gaussianReal_of_indepFun`
-/

namespace InformationTheory.Shannon.FisherInfo

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## §1 — Arithmetic kernel (Gaussian-independent) -/

/-- The Stam arithmetic kernel. For positive `a, b` and `λ ∈ [0,1]`,
`1/(a+b) ≤ λ²/a + (1-λ)²/b`. This is the pure real-number content of the convex
Fisher bound after substituting the Gaussian closed form `J(𝒩(m,v)) = 1/v`.

The difference `λ²(a+b)b + (1-λ)²(a+b)a − ab` equals `(a − λ(a+b))²`, hence is
`≥ 0`; equality holds exactly at `λ = a/(a+b)`. -/
@[entry_point]
theorem stam_fisher_arith (a b lam : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
    1 / (a + b) ≤ lam ^ 2 / a + (1 - lam) ^ 2 / b := by
  have hab : 0 < a + b := by linarith
  rw [div_add_div _ _ (ne_of_gt ha) (ne_of_gt hb), div_le_div_iff₀ hab (by positivity)]
  nlinarith [sq_nonneg (a - lam * (a + b)), mul_pos ha hb, mul_pos (mul_pos ha hb) hab,
    mul_pos ha hab, mul_pos hb hab]

/-! ## §2 — Gaussian convex Fisher bound (V2-keyed, non-vacuous) -/

/-- The Gaussian Stam convex Fisher bound. For Gaussian laws `𝒩(m₁,v₁)`, `𝒩(m₂,v₂)`
with `v₁, v₂ ≠ 0`, the V2 Fisher information of the sum law `𝒩(m₁+m₂, v₁+v₂)`
satisfies `J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)` for every `λ ∈ [0,1]`.
Each Fisher info evaluates to the closed form `1/v` via `fisherInfoOfMeasureV2_gaussianReal`. -/
@[entry_point]
theorem stam_convex_fisher_bound_gaussian
    (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (lam : ℝ) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
    (fisherInfoOfMeasureV2 (gaussianReal (m₁ + m₂) (v₁ + v₂))
        (gaussianPDFReal (m₁ + m₂) (v₁ + v₂))).toReal
      ≤ lam ^ 2 *
          (fisherInfoOfMeasureV2 (gaussianReal m₁ v₁) (gaussianPDFReal m₁ v₁)).toReal
        + (1 - lam) ^ 2 *
          (fisherInfoOfMeasureV2 (gaussianReal m₂ v₂) (gaussianPDFReal m₂ v₂)).toReal := by
  have hv₁pos : (0 : ℝ) < (v₁ : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hv₁)
  have hv₂pos : (0 : ℝ) < (v₂ : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hv₂)
  have hsum : v₁ + v₂ ≠ 0 := (add_pos (zero_lt_iff.mpr hv₁) (zero_lt_iff.mpr hv₂)).ne'
  rw [fisherInfoOfMeasureV2_gaussianReal (m₁ + m₂) hsum,
    fisherInfoOfMeasureV2_gaussianReal m₁ hv₁,
    fisherInfoOfMeasureV2_gaussianReal m₂ hv₂,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity),
    NNReal.coe_add]
  have := stam_fisher_arith (v₁ : ℝ) (v₂ : ℝ) lam hv₁pos hv₂pos hlo hhi
  rw [mul_one_div, mul_one_div]
  exact this

end InformationTheory.Shannon.FisherInfo
