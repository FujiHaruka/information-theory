import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import InformationTheory.Meta.EntryPoint

/-!
# A binary erasure channel more capable than a binary symmetric channel

Fix a crossover probability `p` with `0 < p < 1/2`. Feeding the input law `Bern(x)` to the
binary symmetric channel with that crossover probability produces the mutual information
`h₂(x ∗ p) - h₂(p)`, where `x ∗ p = x (1 - p) + (1 - x) p` is the binary convolution and `h₂`
is the binary entropy in bits; feeding the same input law to the binary erasure channel with
erasure probability `h₂(p)` produces `(1 - h₂(p)) h₂(x)`. The second quantity dominates the
first at every `x`, which is the pointwise form of the statement that the erasure channel is
more capable than the symmetric one.

Mathlib's `Real.binEntropy` is measured in nats, so `h₂ = Real.binEntropy / Real.log 2`.
Clearing both denominators turns the comparison into the inequality recorded here, whose two
sides are the two mutual informations scaled by `(Real.log 2) ^ 2`.

The proof is a curvature argument on the difference of the two sides, viewed as a function of
`x` on `[0, 1]`. That difference vanishes at `0`, at `1/2` and at `1`, and is symmetric about
`1/2`, so only `[0, 1/2]` matters. Its second derivative has the sign of a downward parabola in
`x` shifted by a constant, so on `(0, 1/2)` the second derivative changes sign at most once, and
only from negative to positive. The difference is therefore concave on an initial segment and
convex on the remaining one. On the convex segment its derivative is at most the derivative at
`1/2`, which vanishes, so the difference is nonincreasing there and stays above its value at
`1/2`; on the concave segment it stays above the smaller of its two endpoint values, both of
which are already known to be nonnegative. The degenerate case where the sign change does not
occur is the same argument with an empty convex segment.

## Main statements

* `log_two_mul_binEntropy_binConv_sub_binEntropy_le` — the comparison itself, in nats.
* `binEntropy_binConv_sub_binEntropy_le` — the form carrying an erasure probability `e` at
  most `h₂(p)`, obtained from the previous one by monotonicity in `e`.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open Real Set

variable {p x : ℝ}

/-- Binary convolution `x ∗ p = x (1 - p) + (1 - x) p`, the probability that the binary
symmetric channel with crossover probability `p` outputs `1` on the input law `Bern(x)`. -/
private def binConv (p : ℝ) : ℝ → ℝ := fun x ↦ x * (1 - p) + (1 - x) * p

/-- The excess of the erasure channel's mutual information over the symmetric channel's, both
measured in nats and scaled by `Real.log 2`. -/
private noncomputable def gapFun (p : ℝ) : ℝ → ℝ := fun x ↦
  (Real.log 2 - Real.binEntropy p) * Real.binEntropy x
    - Real.log 2 * (Real.binEntropy (binConv p x) - Real.binEntropy p)

/-- The derivative of `gapFun p` on `(0, 1)`. -/
private noncomputable def gapFunDeriv (p : ℝ) : ℝ → ℝ := fun x ↦
  (Real.log 2 - Real.binEntropy p) * (Real.log (1 - x) - Real.log x)
    - Real.log 2 * (1 - 2 * p) * (Real.log (1 - binConv p x) - Real.log (binConv p x))

/-- The second derivative of `gapFun p` on `(0, 1)`. -/
private noncomputable def gapFunDeriv2 (p : ℝ) : ℝ → ℝ := fun x ↦
  -(Real.log 2 - Real.binEntropy p) / (x * (1 - x))
    + Real.log 2 * (1 - 2 * p) ^ 2 / (binConv p x * (1 - binConv p x))

/-- The value of `x (1 - x)` at which the second derivative of `gapFun p` changes sign. -/
private noncomputable def curvatureThreshold (p : ℝ) : ℝ :=
  (Real.log 2 - Real.binEntropy p) * (p * (1 - p)) / (Real.binEntropy p * (1 - 2 * p) ^ 2)

/-- The point of `[0, 1/2]` at which `gapFun p` turns from concave to convex; it equals `1/2`
when the turn does not occur. -/
private noncomputable def inflection (p : ℝ) : ℝ :=
  (1 - Real.sqrt (max 0 (1 - 4 * curvatureThreshold p))) / 2

/-! ### Elementary values and symmetry -/

private lemma binConv_one_sub (p x : ℝ) : binConv p (1 - x) = 1 - binConv p x := by
  simp only [binConv]; ring

private lemma binConv_mem_Ioo (hp₀ : 0 < p) (hp₁ : p < 1) (hx₀ : 0 < x) (hx₁ : x < 1) :
    binConv p x ∈ Ioo (0 : ℝ) 1 := by
  simp only [binConv, mem_Ioo]
  constructor <;> nlinarith

private lemma gapFun_zero (p : ℝ) : gapFun p 0 = 0 := by
  simp [gapFun, binConv]

private lemma gapFun_two_inv (p : ℝ) : gapFun p 2⁻¹ = 0 := by
  have h : binConv p 2⁻¹ = 2⁻¹ := by simp only [binConv]; ring
  simp only [gapFun, h, Real.binEntropy_two_inv]
  ring

private lemma gapFun_one_sub (p x : ℝ) : gapFun p (1 - x) = gapFun p x := by
  simp [gapFun, binConv_one_sub, Real.binEntropy_one_sub]

private lemma gapFunDeriv_two_inv (p : ℝ) : gapFunDeriv p 2⁻¹ = 0 := by
  have h : binConv p 2⁻¹ = 2⁻¹ := by simp only [binConv]; ring
  have h' : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  simp only [gapFunDeriv, h, h', sub_self, mul_zero]

/-! ### Derivatives -/

private lemma continuous_gapFun (p : ℝ) : Continuous (gapFun p) := by
  unfold gapFun binConv
  fun_prop

private lemma hasDerivAt_binConv (p x : ℝ) : HasDerivAt (binConv p) (1 - 2 * p) x := by
  have h₁ : HasDerivAt (fun y : ℝ ↦ y * (1 - p)) (1 - p) x := by
    simpa using (hasDerivAt_id x).mul_const (1 - p)
  have h₂ : HasDerivAt (fun y : ℝ ↦ (1 - y) * p) (-p) x := by
    have h₃ : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    simpa using h₃.mul_const p
  have h₄ := h₁.add h₂
  have h₅ : (1 : ℝ) - p + -p = 1 - 2 * p := by ring
  rw [h₅] at h₄
  exact h₄

private lemma hasDerivAt_gapFun (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) (hx₀' : 0 < x) (hx₁' : x < 1) :
    HasDerivAt (gapFun p) (gapFunDeriv p x) x := by
  obtain ⟨hu₀', hu₁'⟩ := binConv_mem_Ioo hp₀ (by linarith) hx₀' hx₁'
  have hx₀ : x ≠ 0 := ne_of_gt hx₀'
  have hx₁ : x ≠ 1 := ne_of_lt hx₁'
  have hu₀ : binConv p x ≠ 0 := ne_of_gt hu₀'
  have hu₁ : binConv p x ≠ 1 := ne_of_lt hu₁'
  have h₁ : HasDerivAt Real.binEntropy (Real.log (1 - x) - Real.log x) x :=
    Real.hasDerivAt_binEntropy hx₀ hx₁
  have h₂ : HasDerivAt (fun y ↦ Real.binEntropy (binConv p y))
      ((Real.log (1 - binConv p x) - Real.log (binConv p x)) * (1 - 2 * p)) x :=
    (Real.hasDerivAt_binEntropy hu₀ hu₁).comp x (hasDerivAt_binConv p x)
  have h₃ := (h₁.const_mul (Real.log 2 - Real.binEntropy p)).sub
    ((h₂.sub_const (Real.binEntropy p)).const_mul (Real.log 2))
  refine h₃.congr_deriv ?_
  simp only [gapFunDeriv]
  ring

private lemma hasDerivAt_gapFunDeriv (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) (hxa : 0 < x) (hxb : x < 1) :
    HasDerivAt (gapFunDeriv p) (gapFunDeriv2 p x) x := by
  obtain ⟨hua, hub⟩ := binConv_mem_Ioo hp₀ (by linarith) hxa hxb
  have hx₀ : x ≠ 0 := ne_of_gt hxa
  have hu₀ : binConv p x ≠ 0 := ne_of_gt hua
  have hx₁' : (1 : ℝ) - x ≠ 0 := by intro h; exact absurd (by linarith : x = 1) (ne_of_lt hxb)
  have hu₁' : (1 : ℝ) - binConv p x ≠ 0 := by
    intro h; exact absurd (by linarith : binConv p x = 1) (ne_of_lt hub)
  have e₁ : HasDerivAt (fun y : ℝ ↦ Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id' x).const_sub 1).log hx₁'
  have e₂ : HasDerivAt (fun y : ℝ ↦ Real.log y) (1 / x) x := (hasDerivAt_id' x).log hx₀
  have e₃ : HasDerivAt (fun y : ℝ ↦ Real.log (1 - binConv p y))
      (-(1 - 2 * p) / (1 - binConv p x)) x :=
    ((hasDerivAt_binConv p x).const_sub 1).log hu₁'
  have e₄ : HasDerivAt (fun y : ℝ ↦ Real.log (binConv p y))
      ((1 - 2 * p) / binConv p x) x :=
    (hasDerivAt_binConv p x).log hu₀
  have h := ((e₁.sub e₂).const_mul (Real.log 2 - Real.binEntropy p)).sub
    ((e₃.sub e₄).const_mul (Real.log 2 * (1 - 2 * p)))
  refine h.congr_deriv ?_
  simp only [gapFunDeriv2]
  field_simp
  ring

/-! ### The sign of the second derivative -/

private lemma binConv_mul_one_sub (p x : ℝ) :
    binConv p x * (1 - binConv p x) = p * (1 - p) + (1 - 2 * p) ^ 2 * (x * (1 - x)) := by
  simp only [binConv]; ring

private lemma binEntropy_lt_log_two_of_lt_two_inv (hp₁ : p < 2⁻¹) :
    Real.binEntropy p < Real.log 2 :=
  Real.binEntropy_lt_log_two.mpr (ne_of_lt hp₁)

private lemma binEntropy_pos_of_lt_two_inv (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) :
    0 < Real.binEntropy p :=
  Real.binEntropy_pos hp₀ (by linarith)

private lemma curvatureThreshold_pos (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) :
    0 < curvatureThreshold p := by
  have h₁ : 0 < Real.log 2 - Real.binEntropy p := by
    have := binEntropy_lt_log_two_of_lt_two_inv hp₁; linarith
  have h₂ : 0 < p * (1 - p) := by nlinarith
  have h₃ : 0 < Real.binEntropy p := binEntropy_pos_of_lt_two_inv hp₀ hp₁
  have h₄ : 0 < (1 - 2 * p) ^ 2 := pow_pos (by linarith) 2
  exact div_pos (mul_pos h₁ h₂) (mul_pos h₃ h₄)

private lemma gapFunDeriv2_mul (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) (hx₀ : 0 < x) (hx₁ : x < 1) :
    gapFunDeriv2 p x * (x * (1 - x) * (binConv p x * (1 - binConv p x)))
      = Real.binEntropy p * (1 - 2 * p) ^ 2 * (x * (1 - x) - curvatureThreshold p) := by
  obtain ⟨hua, hub⟩ := binConv_mem_Ioo hp₀ (by linarith) hx₀ hx₁
  have hA₀ : x ≠ 0 := ne_of_gt hx₀
  have hA₁ : (1 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
  have hB₀ : binConv p x ≠ 0 := ne_of_gt hua
  have hB₁ : (1 : ℝ) - binConv p x ≠ 0 := ne_of_gt (by linarith)
  have hE : Real.binEntropy p ≠ 0 := ne_of_gt (binEntropy_pos_of_lt_two_inv hp₀ hp₁)
  have hQ : (1 - 2 * p) ^ 2 ≠ 0 := ne_of_gt (pow_pos (by linarith) 2)
  have key : gapFunDeriv2 p x * (x * (1 - x) * (binConv p x * (1 - binConv p x)))
      = -(Real.log 2 - Real.binEntropy p) * (binConv p x * (1 - binConv p x))
        + Real.log 2 * (1 - 2 * p) ^ 2 * (x * (1 - x)) := by
    simp only [gapFunDeriv2]
    field_simp
  have hcancel : Real.binEntropy p * (1 - 2 * p) ^ 2 * curvatureThreshold p
      = (Real.log 2 - Real.binEntropy p) * (p * (1 - p)) := by
    simp only [curvatureThreshold]
    set D := Real.binEntropy p * (1 - 2 * p) ^ 2 with hDdef
    have hD : D ≠ 0 := mul_ne_zero hE hQ
    field_simp
  have hsplit : Real.binEntropy p * (1 - 2 * p) ^ 2 * (x * (1 - x) - curvatureThreshold p)
      = Real.binEntropy p * (1 - 2 * p) ^ 2 * (x * (1 - x))
        - Real.binEntropy p * (1 - 2 * p) ^ 2 * curvatureThreshold p := by ring
  rw [key, binConv_mul_one_sub, hsplit, hcancel]
  ring

private lemma gapFunDeriv2_nonpos (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) (hx₀ : 0 < x) (hx₁ : x < 1)
    (hle : x * (1 - x) ≤ curvatureThreshold p) : gapFunDeriv2 p x ≤ 0 := by
  obtain ⟨hua, hub⟩ := binConv_mem_Ioo hp₀ (by linarith) hx₀ hx₁
  have hD : 0 < x * (1 - x) * (binConv p x * (1 - binConv p x)) := by
    apply mul_pos (mul_pos hx₀ (by linarith)) (mul_pos hua (by linarith))
  refine le_of_mul_le_mul_right ?_ hD
  rw [zero_mul, gapFunDeriv2_mul hp₀ hp₁ hx₀ hx₁]
  have h₃ : 0 < Real.binEntropy p := binEntropy_pos_of_lt_two_inv hp₀ hp₁
  have h₄ : 0 < (1 - 2 * p) ^ 2 := pow_pos (by linarith) 2
  have hC : (0 : ℝ) ≤ Real.binEntropy p * (1 - 2 * p) ^ 2 := (mul_pos h₃ h₄).le
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hle)]

private lemma gapFunDeriv2_nonneg (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) (hx₀ : 0 < x) (hx₁ : x < 1)
    (hge : curvatureThreshold p ≤ x * (1 - x)) : 0 ≤ gapFunDeriv2 p x := by
  obtain ⟨hua, hub⟩ := binConv_mem_Ioo hp₀ (by linarith) hx₀ hx₁
  have hD : 0 < x * (1 - x) * (binConv p x * (1 - binConv p x)) := by
    apply mul_pos (mul_pos hx₀ (by linarith)) (mul_pos hua (by linarith))
  refine le_of_mul_le_mul_right ?_ hD
  rw [zero_mul, gapFunDeriv2_mul hp₀ hp₁ hx₀ hx₁]
  have h₃ : 0 < Real.binEntropy p := binEntropy_pos_of_lt_two_inv hp₀ hp₁
  have h₄ : 0 < (1 - 2 * p) ^ 2 := pow_pos (by linarith) 2
  have hC : (0 : ℝ) ≤ Real.binEntropy p * (1 - 2 * p) ^ 2 := (mul_pos h₃ h₄).le
  exact mul_nonneg hC (sub_nonneg.mpr hge)

/-! ### The inflection point -/

private lemma inflection_pos (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) : 0 < inflection p := by
  have hK := curvatureThreshold_pos hp₀ hp₁
  have h₁ : max 0 (1 - 4 * curvatureThreshold p) < 1 := by
    rcases max_cases 0 (1 - 4 * curvatureThreshold p) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> linarith
  have h₂ : Real.sqrt (max 0 (1 - 4 * curvatureThreshold p)) < 1 := by
    simpa using Real.sqrt_lt_sqrt (le_max_left _ _) h₁
  simp only [inflection]
  linarith

private lemma inflection_le_two_inv (p : ℝ) : inflection p ≤ 2⁻¹ := by
  have h := Real.sqrt_nonneg (max 0 (1 - 4 * curvatureThreshold p))
  simp only [inflection]
  linarith

private lemma inflection_mul_le (p : ℝ) :
    inflection p * (1 - inflection p) ≤ curvatureThreshold p := by
  have hsq : Real.sqrt (max 0 (1 - 4 * curvatureThreshold p)) ^ 2
      = max 0 (1 - 4 * curvatureThreshold p) := Real.sq_sqrt (le_max_left _ _)
  have hge : 1 - 4 * curvatureThreshold p ≤ max 0 (1 - 4 * curvatureThreshold p) :=
    le_max_right _ _
  simp only [inflection]
  nlinarith [hsq, hge]

private lemma curvatureThreshold_le_inflection_mul (h : inflection p < 2⁻¹) :
    curvatureThreshold p ≤ inflection p * (1 - inflection p) := by
  simp only [inflection] at h ⊢
  have hsq : Real.sqrt (max 0 (1 - 4 * curvatureThreshold p)) ^ 2
      = max 0 (1 - 4 * curvatureThreshold p) := Real.sq_sqrt (le_max_left _ _)
  have hs₀ : 0 < Real.sqrt (max 0 (1 - 4 * curvatureThreshold p)) := by linarith
  have hpos : 0 < max 0 (1 - 4 * curvatureThreshold p) := by nlinarith
  have heq : max 0 (1 - 4 * curvatureThreshold p) = 1 - 4 * curvatureThreshold p := by
    rcases max_cases 0 (1 - 4 * curvatureThreshold p) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact he
  rw [heq] at hsq ⊢
  nlinarith [hsq]

/-! ### The two arcs -/

private lemma mem_Ioo_of_mem_Icc_inflection (hp₀ : 0 < p) (hp₁ : p < 2⁻¹)
    (hy : x ∈ Icc (inflection p) (2⁻¹ : ℝ)) : 0 < x ∧ x < 1 :=
  ⟨lt_of_lt_of_le (inflection_pos hp₀ hp₁) hy.1, lt_of_le_of_lt hy.2 (by norm_num)⟩

private lemma gapFunDeriv_nonpos_of_mem (hp₀ : 0 < p) (hp₁ : p < 2⁻¹)
    (hx : x ∈ Icc (inflection p) (2⁻¹ : ℝ)) : gapFunDeriv p x ≤ 0 := by
  have hx0 : 0 < inflection p := inflection_pos hp₀ hp₁
  have hx0' : inflection p ≤ 2⁻¹ := inflection_le_two_inv p
  have hcont : ContinuousOn (gapFunDeriv p) (Icc (inflection p) 2⁻¹) := by
    intro y hy
    obtain ⟨h₁, h₂⟩ := mem_Ioo_of_mem_Icc_inflection hp₀ hp₁ hy
    exact (hasDerivAt_gapFunDeriv hp₀ hp₁ h₁ h₂).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (gapFunDeriv p) (interior (Icc (inflection p) 2⁻¹)) := by
    rw [interior_Icc]
    intro y hy
    obtain ⟨h₁, h₂⟩ := mem_Ioo_of_mem_Icc_inflection hp₀ hp₁ (Ioo_subset_Icc_self hy)
    exact (hasDerivAt_gapFunDeriv hp₀ hp₁ h₁ h₂).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Icc (inflection p) (2⁻¹ : ℝ)), 0 ≤ deriv (gapFunDeriv p) y := by
    rw [interior_Icc]
    intro y hy
    obtain ⟨h₁, h₂⟩ := mem_Ioo_of_mem_Icc_inflection hp₀ hp₁ (Ioo_subset_Icc_self hy)
    rw [(hasDerivAt_gapFunDeriv hp₀ hp₁ h₁ h₂).deriv]
    refine gapFunDeriv2_nonneg hp₀ hp₁ h₁ h₂ ?_
    have hKle := curvatureThreshold_le_inflection_mul (lt_trans hy.1 hy.2)
    nlinarith [hy.1, hy.2, hx0]
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (inflection p) (2⁻¹ : ℝ)) hcont hdiff hderiv
  have hres := hmono hx (right_mem_Icc.mpr hx0') hx.2
  rwa [gapFunDeriv_two_inv] at hres

private lemma gapFun_nonneg_of_mem_Icc_inflection_two_inv (hp₀ : 0 < p) (hp₁ : p < 2⁻¹)
    (hx : x ∈ Icc (inflection p) (2⁻¹ : ℝ)) : 0 ≤ gapFun p x := by
  have hx0' : inflection p ≤ 2⁻¹ := inflection_le_two_inv p
  have hdiff : DifferentiableOn ℝ (gapFun p) (interior (Icc (inflection p) 2⁻¹)) := by
    rw [interior_Icc]
    intro y hy
    obtain ⟨h₁, h₂⟩ := mem_Ioo_of_mem_Icc_inflection hp₀ hp₁ (Ioo_subset_Icc_self hy)
    exact (hasDerivAt_gapFun hp₀ hp₁ h₁ h₂).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Icc (inflection p) (2⁻¹ : ℝ)), deriv (gapFun p) y ≤ 0 := by
    rw [interior_Icc]
    intro y hy
    obtain ⟨h₁, h₂⟩ := mem_Ioo_of_mem_Icc_inflection hp₀ hp₁ (Ioo_subset_Icc_self hy)
    rw [(hasDerivAt_gapFun hp₀ hp₁ h₁ h₂).deriv]
    exact gapFunDeriv_nonpos_of_mem hp₀ hp₁ (Ioo_subset_Icc_self hy)
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc (inflection p) (2⁻¹ : ℝ))
    (continuous_gapFun p).continuousOn hdiff hderiv
  have hres := hanti hx (right_mem_Icc.mpr hx0') hx.2
  rwa [gapFun_two_inv] at hres

private lemma concaveOn_gapFun_Icc_zero_inflection (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) :
    ConcaveOn ℝ (Icc 0 (inflection p)) (gapFun p) := by
  have hx0 : 0 < inflection p := inflection_pos hp₀ hp₁
  have hx0' : inflection p ≤ 2⁻¹ := inflection_le_two_inv p
  have hsub : ∀ y ∈ Ioo (0 : ℝ) (inflection p), 0 < y ∧ y < 1 := fun y hy ↦
    ⟨hy.1, lt_of_lt_of_le (lt_of_lt_of_le hy.2 hx0') (by norm_num)⟩
  refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := gapFunDeriv p) (f'' := gapFunDeriv2 p)
    (convex_Icc 0 (inflection p)) (continuous_gapFun p).continuousOn ?_ ?_ ?_
  · rw [interior_Icc]
    intro y hy
    obtain ⟨h₁, h₂⟩ := hsub y hy
    exact (hasDerivAt_gapFun hp₀ hp₁ h₁ h₂).hasDerivWithinAt
  · rw [interior_Icc]
    intro y hy
    obtain ⟨h₁, h₂⟩ := hsub y hy
    exact (hasDerivAt_gapFunDeriv hp₀ hp₁ h₁ h₂).hasDerivWithinAt
  · rw [interior_Icc]
    intro y hy
    obtain ⟨h₁, h₂⟩ := hsub y hy
    refine gapFunDeriv2_nonpos hp₀ hp₁ h₁ h₂ ?_
    have hKle := inflection_mul_le p
    nlinarith [hy.1, hy.2, hx0, hx0']

private lemma gapFun_nonneg_of_mem_Icc_zero_inflection (hp₀ : 0 < p) (hp₁ : p < 2⁻¹)
    (hx : x ∈ Icc 0 (inflection p)) : 0 ≤ gapFun p x := by
  have hx0 : 0 < inflection p := inflection_pos hp₀ hp₁
  have hend : 0 ≤ gapFun p (inflection p) :=
    gapFun_nonneg_of_mem_Icc_inflection_two_inv hp₀ hp₁
      ⟨le_refl _, inflection_le_two_inv p⟩
  have hres := (concaveOn_gapFun_Icc_zero_inflection hp₀ hp₁).min_le_of_mem_Icc
    (left_mem_Icc.mpr hx0.le) (right_mem_Icc.mpr hx0.le) hx
  rw [gapFun_zero] at hres
  exact le_trans (le_min (le_refl 0) hend) hres

private lemma gapFun_nonneg (hp₀ : 0 < p) (hp₁ : p < 2⁻¹) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 ≤ gapFun p x := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 2⁻¹ → 0 ≤ gapFun p y := by
    intro y hy₀ hy₁
    rcases le_or_gt y (inflection p) with h | h
    · exact gapFun_nonneg_of_mem_Icc_zero_inflection hp₀ hp₁ ⟨hy₀, h⟩
    · exact gapFun_nonneg_of_mem_Icc_inflection_two_inv hp₀ hp₁ ⟨h.le, hy₁⟩
  rcases le_or_gt x 2⁻¹ with h | h
  · exact key x hx₀ h
  · rw [← gapFun_one_sub p x]
    exact key (1 - x) (by linarith) (by linarith)

/-! ### The comparison -/

/-- The binary erasure channel with erasure probability `h₂(p)` is more capable than the binary
symmetric channel with crossover probability `p`: at the input law `Bern(x)` the erasure
channel's mutual information `(1 - h₂(p)) h₂(x)` is at least the symmetric channel's
`h₂(x ∗ p) - h₂(p)`, where `x ∗ p = x (1 - p) + (1 - x) p`. Both sides are stated in nats and
scaled by `Real.log 2`, so that `h₂ = Real.binEntropy / Real.log 2` clears.

@audit:ok -/
@[entry_point]
theorem log_two_mul_binEntropy_binConv_sub_binEntropy_le (hp₀ : 0 < p) (hp₁ : p < 1 / 2)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.log 2 * (Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p)
      ≤ (Real.log 2 - Real.binEntropy p) * Real.binEntropy x := by
  have h := gapFun_nonneg hp₀ (by linarith) hx₀ hx₁
  simp only [gapFun, binConv] at h
  linarith

/-- The binary erasure channel with erasure probability `e` is more capable than the binary
symmetric channel with crossover probability `p` as soon as `e ≤ h₂(p)`, where `h₂` is the
binary entropy in bits. Only the upper bound on `e` is used, so no lower bound on it is
assumed.

@audit:ok -/
@[entry_point]
theorem binEntropy_binConv_sub_binEntropy_le {e : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1 / 2)
    (he : e * Real.log 2 ≤ Real.binEntropy p) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p
      ≤ (1 - e) * Real.binEntropy x := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmain := log_two_mul_binEntropy_binConv_sub_binEntropy_le hp₀ hp₁ hx₀ hx₁
  have hent : 0 ≤ Real.binEntropy x := Real.binEntropy_nonneg hx₀ hx₁
  have hstep : (Real.log 2 - Real.binEntropy p) * Real.binEntropy x
      ≤ Real.log 2 * ((1 - e) * Real.binEntropy x) := by
    have : Real.log 2 - Real.binEntropy p ≤ Real.log 2 * (1 - e) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hent]
  have := le_trans hmain hstep
  exact le_of_mul_le_mul_left (by linarith) hlog

end InformationTheory.Shannon.BroadcastChannel
