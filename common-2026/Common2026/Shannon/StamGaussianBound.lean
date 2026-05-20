import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Positivity
import Common2026.Shannon.FisherInfoV2DeBruijn

/-!
# Stam convex Fisher bound — non-vacuous Gaussian instance (L-S12-C′)

Common2026 EPI (Ch.17) follow-up to the Stam inequality core
`J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)`.

The pre-existing Gaussian discharge `isStamCondExpCSHyp_of_gaussian_fisherInfo_zero`
(`Common2026/Shannon/EPIStamStep12Body.lean:327`) is **vacuous**: it exploits the
V1 representative-dependence bug under which `fisherInfo` degenerates to `0` on a
Gaussian law, so the precondition `0 < J_X` is contradicted and the ∀λ bound holds
for no informative reason. It asserts *nothing* about Stam actually holding for
Gaussians.

This file replaces that vacuous discharge with the **correct, non-vacuous Gaussian
instance**, keyed on the V2 Fisher information `fisherInfoOfMeasureV2`
(`Common2026/Shannon/FisherInfoV2DeBruijn.lean:124`) which evaluates to the true
closed form `1/v` rather than the V1 `0` ghost. The proof reduces the convex Fisher
bound to a pure real-arithmetic kernel
`1/(a+b) ≤ λ²/a + (1-λ)²/b` whose equality is saturated at `λ* = a/(a+b)`
(matching the textbook Stam optimum).

**Scope.** This publishes only the *Gaussian* instance of the convex Fisher bound.
The discharge for general `X, Y` is a separate, PR-scale effort (heat-flow + de
Bruijn machinery) and is deliberately out of scope here.

## 主シグネチャ

* `stam_fisher_arith` — pure real arithmetic kernel `1/(a+b) ≤ λ²/a + (1-λ)²/b`
* `stam_fisher_arith_eq_at_opt` — saturation: equality at `λ* = a/(a+b)`
* `stam_convex_fisher_bound_gaussian` — V2-keyed Gaussian convex Fisher bound (closed form)
* `stam_convex_fisher_bound_gaussian_indep` — independent-RV form via
  `gaussianReal_add_gaussianReal_of_indepFun`
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## §1 — Arithmetic kernel (Gaussian-independent) -/

/-- **Stam arithmetic kernel.** For positive `a, b` and `λ ∈ [0,1]`,
`1/(a+b) ≤ λ²/a + (1-λ)²/b`. This is the pure real-number content of the convex
Fisher bound after substituting the Gaussian closed form `J(𝒩(m,v)) = 1/v`.

The difference `λ²(a+b)b + (1-λ)²(a+b)a − ab` equals `(a − λ(a+b))²`, hence is
`≥ 0`; equality holds exactly at `λ = a/(a+b)`. -/
theorem stam_fisher_arith (a b lam : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
    1 / (a + b) ≤ lam ^ 2 / a + (1 - lam) ^ 2 / b := by
  have hab : 0 < a + b := by linarith
  rw [div_add_div _ _ (ne_of_gt ha) (ne_of_gt hb), div_le_div_iff₀ hab (by positivity)]
  nlinarith [sq_nonneg (a - lam * (a + b)), mul_pos ha hb, mul_pos (mul_pos ha hb) hab,
    mul_pos ha hab, mul_pos hb hab]

/-- **Saturation of the Stam kernel.** At the optimum `λ* = a/(a+b)` the bound
`stam_fisher_arith` holds with equality. -/
theorem stam_fisher_arith_eq_at_opt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (a + b)
      = (a / (a + b)) ^ 2 / a + (1 - a / (a + b)) ^ 2 / b := by
  have hab : 0 < a + b := by linarith
  field_simp
  ring

/-! ## §2 — Gaussian convex Fisher bound (V2-keyed, non-vacuous) -/

/-- **Gaussian Stam convex Fisher bound.** For Gaussian laws `𝒩(m₁,v₁)`, `𝒩(m₂,v₂)`
with `v₁, v₂ ≠ 0`, the V2 Fisher information of the sum law `𝒩(m₁+m₂, v₁+v₂)`
satisfies the Stam convex bound
`J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)`
for every `λ ∈ [0,1]`. Each Fisher info evaluates to the true closed form `1/v`
(via `fisherInfoOfMeasureV2_gaussianReal`), so this is the **non-vacuous** Gaussian
instance — contrast `isStamCondExpCSHyp_of_gaussian_fisherInfo_zero` which is
vacuous under the V1 `0` artefact. -/
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

/-! ## §3 — Independent-RV form -/

/-- **Gaussian Stam convex Fisher bound, independent-RV form.** If `X, Y` are
independent with Gaussian laws `𝒩(m₁,v₁)`, `𝒩(m₂,v₂)` (`v₁, v₂ ≠ 0`), then the
law of `X + Y` is `𝒩(m₁+m₂, v₁+v₂)`
(`gaussianReal_add_gaussianReal_of_indepFun`) and the convex Fisher bound holds. -/
theorem stam_convex_fisher_bound_gaussian_indep
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
    {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂)
    (lam : ℝ) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
    (fisherInfoOfMeasureV2 (P.map (X + Y))
        (gaussianPDFReal (m₁ + m₂) (v₁ + v₂))).toReal
      ≤ lam ^ 2 *
          (fisherInfoOfMeasureV2 (gaussianReal m₁ v₁) (gaussianPDFReal m₁ v₁)).toReal
        + (1 - lam) ^ 2 *
          (fisherInfoOfMeasureV2 (gaussianReal m₂ v₂) (gaussianPDFReal m₂ v₂)).toReal := by
  rw [gaussianReal_add_gaussianReal_of_indepFun hXY hX hY]
  exact stam_convex_fisher_bound_gaussian m₁ m₂ hv₁ hv₂ lam hlo hhi

end Common2026.Shannon.FisherInfoV2
