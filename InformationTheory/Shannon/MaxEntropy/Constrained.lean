import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.CsiszarProjection
import InformationTheory.Shannon.Chernoff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Constrained maximum entropy (Cover–Thomas Theorem 12.1.1)

For a pmf `P : α → ℝ` on a finite alphabet, the distribution maximizing Shannon entropy
`H(P) = ∑ x, negMulLog (P x)` subject to moment constraints `∑ x, P x · f i x = c i`
is the Boltzmann–Gibbs exponential family

  `gibbsPmf f λ x := exp (∑ i, λ i · f i x) / Z(λ)`

where `Z(λ) = ∑ y, exp (∑ i, λ i · f i y)` is the partition function.
The Lagrange parameter `λ` is passed in as a hypothesis rather than solved for.

## Main definitions

* `gibbsZ` — partition function `Z(λ) := ∑ y, exp ⟨λ, f y⟩`.
* `gibbsPmf` — Boltzmann–Gibbs pmf `x ↦ exp ⟨λ, f x⟩ / Z(λ)`.

## Main statements

* `gibbsPmf_mem_stdSimplex` — `gibbsPmf f λ ∈ stdSimplex ℝ α`.
* `entropy_le_gibbs_of_constraints` — under moment constraints, `H(P) ≤ H(gibbsPmf f λ)`.
* `entropy_eq_gibbs_iff_of_constraints` — equality holds iff `P = gibbsPmf f λ`.

## Implementation notes

KKT / Lagrange duality is not available in Mathlib
(`Mathlib/Analysis/Calculus/LagrangeMultipliers.lean` notes the absence). The proof
avoids this via the Gibbs + Csiszár `klDivPmf` algebraic-identity route:

```
0 ≤ klDivPmf P (gibbsPmf f λ) = −H(P) − ⟨λ, c⟩ + log Z(λ)
0 = klDivPmf (gibbsPmf f λ) (gibbsPmf f λ) = −H(gibbsPmf f λ) − ⟨λ, c⟩ + log Z(λ)
```

This avoids any need for ψ(λ) convexity or Lagrange-multiplier existence theory.
We use `CsiszarProjection.klDivPmf` rather than `Mathlib.MeasureTheory.Measure.Tilted`
because the Csiszár API (`klDivPmf_nonneg`, `klDivPmf_self_eq_zero`) is closed in the pmf
world, and `Real.exp / log` arithmetic suffices without `rnDeriv` or `=ᵐ` arguments.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006. Theorem 12.1.1.
-/

namespace InformationTheory.Shannon.MaxEntropyConstrained

set_option linter.unusedSectionVars false

open Real InformationTheory
open InformationTheory.Shannon.CsiszarProjection (klDivPmf klDivPmf_nonneg)
open InformationTheory.Shannon.Chernoff (klDivPmf_self_eq_zero)
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {k : ℕ}

/-! ## Gibbs pmf: definition and basic properties -/

/-- Partition function `Z(λ) := ∑ y, exp (∑ i, λ i · f i y)`. Independent `def` so
that `Real.log Z(λ)` can be reused throughout the core identity. -/
noncomputable def gibbsZ (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : ℝ :=
  ∑ y, Real.exp (∑ i, lam i * f i y)

/-- Boltzmann–Gibbs exponential family pmf, parametrized by Lagrange parameter
`lam : Fin k → ℝ` and feature maps `f : Fin k → α → ℝ`:

  gibbsPmf f λ x := exp (∑ i, λ i · f i x) / Z(λ).

The denominator `Z(λ)` (`gibbsZ f lam`) is the partition function. -/
noncomputable def gibbsPmf (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : α → ℝ :=
  fun x ↦ Real.exp (∑ i, lam i * f i x) / gibbsZ f lam

omit [DecidableEq α] in
/-- The partition function `Z(λ)` is strictly positive (each summand is `exp _ > 0`
and there is at least one term by `[Nonempty α]`). -/
lemma gibbsZ_pos [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    0 < gibbsZ f lam := by
  unfold gibbsZ
  apply Finset.sum_pos
  · intro y _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

omit [DecidableEq α] in
/-- Each component of `gibbsPmf f λ` is strictly positive. -/
lemma gibbsPmf_pos [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
    0 < gibbsPmf f lam x := by
  unfold gibbsPmf
  exact div_pos (Real.exp_pos _) (gibbsZ_pos f lam)

omit [DecidableEq α] in
/-- `gibbsPmf f λ` is non-negative pointwise (corollary of positivity). -/
lemma gibbsPmf_nonneg [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
    0 ≤ gibbsPmf f lam x :=
  (gibbsPmf_pos f lam x).le

omit [DecidableEq α] in
/-- The mass of `gibbsPmf f λ` sums to `1`. -/
lemma gibbsPmf_sum_eq_one [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    ∑ x, gibbsPmf f lam x = 1 := by
  unfold gibbsPmf
  rw [← Finset.sum_div]
  exact div_self (gibbsZ_pos f lam).ne'

omit [DecidableEq α] in
/-- `gibbsPmf f λ ∈ stdSimplex ℝ α`. -/
lemma gibbsPmf_mem_stdSimplex [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    gibbsPmf f lam ∈ stdSimplex ℝ α :=
  ⟨fun x ↦ gibbsPmf_nonneg f lam x, gibbsPmf_sum_eq_one f lam⟩

omit [DecidableEq α] in
/-- Closed form for `log (gibbsPmf f λ x)`: the numerator's exponent minus `log Z(λ)`. -/
lemma log_gibbsPmf [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
    Real.log (gibbsPmf f lam x)
      = (∑ i, lam i * f i x) - Real.log (gibbsZ f lam) := by
  unfold gibbsPmf
  rw [Real.log_div (Real.exp_ne_zero _) (gibbsZ_pos f lam).ne']
  rw [Real.log_exp]

/-! ## Core identity and main upper bound -/

omit [DecidableEq α] in
/-- For any `Q ∈ stdSimplex` on `α`, the KL divergence from `Q` to `gibbsPmf f λ`
decomposes into negative entropy, the constraint inner product `⟨λ, 𝔼_Q[f]⟩`, and
`log Z(λ)`:

  klDivPmf Q (gibbsPmf f λ)
    = -H(Q) - ⟨λ, 𝔼_Q[f]⟩ + log Z(λ). -/
lemma klDivPmf_gibbsPmf_eq [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ)
    (Q : α → ℝ) (hQ : Q ∈ stdSimplex ℝ α) :
    klDivPmf Q (gibbsPmf f lam)
      = -(∑ x, Real.negMulLog (Q x))
        - (∑ i, lam i * (∑ x, Q x * f i x))
        + Real.log (gibbsZ f lam) := by
  obtain ⟨hQ_nn, hQ_sum⟩ := hQ
  -- Per-term: gibbs x * klFun (Q x / gibbs x) = Q x * log Q x - Q x * log gibbs x
  --                                            + gibbs x - Q x.
  have h_per : ∀ x : α,
      gibbsPmf f lam x * InformationTheory.klFun (Q x / gibbsPmf f lam x)
        = Real.negMulLog (Q x) * (-1)
          - Q x * Real.log (gibbsPmf f lam x)
          + gibbsPmf f lam x - Q x := by
    intro x
    have hg_pos : 0 < gibbsPmf f lam x := gibbsPmf_pos f lam x
    have hg_ne : gibbsPmf f lam x ≠ 0 := hg_pos.ne'
    have hnml : Real.negMulLog (Q x) = -(Q x * Real.log (Q x)) := by
      rw [Real.negMulLog]; ring
    by_cases hQx : Q x = 0
    · -- Q x = 0: Q x / gibbs x = 0, klFun 0 = 1, gibbs x * 1 = gibbs x.
      have h_div : Q x / gibbsPmf f lam x = 0 := by rw [hQx]; exact zero_div _
      rw [h_div, InformationTheory.klFun_zero, mul_one, hnml, hQx]
      simp
    · -- Q x > 0: standard expansion.
      have hQx_pos : 0 < Q x := lt_of_le_of_ne (hQ_nn x) (Ne.symm hQx)
      have h_ratio_pos : 0 < Q x / gibbsPmf f lam x := div_pos hQx_pos hg_pos
      have h_ratio_ne : Q x / gibbsPmf f lam x ≠ 0 := h_ratio_pos.ne'
      rw [InformationTheory.klFun_apply, Real.log_div hQx hg_ne]
      have key : gibbsPmf f lam x * (Q x / gibbsPmf f lam x
              * (Real.log (Q x) - Real.log (gibbsPmf f lam x)) + 1 - Q x / gibbsPmf f lam x)
            = Q x * Real.log (Q x) - Q x * Real.log (gibbsPmf f lam x)
              + gibbsPmf f lam x - Q x := by
        field_simp
      rw [key]
      rw [hnml]
      ring
  -- Sum the per-term identity.
  have h_sum : klDivPmf Q (gibbsPmf f lam)
      = ∑ x, (Real.negMulLog (Q x) * (-1)
              - Q x * Real.log (gibbsPmf f lam x)
              + gibbsPmf f lam x - Q x) := by
    unfold klDivPmf
    exact Finset.sum_congr rfl (fun x _ ↦ h_per x)
  rw [h_sum]
  -- Split the four summands.
  have h_split : ∀ x : α,
      Real.negMulLog (Q x) * (-1)
        - Q x * Real.log (gibbsPmf f lam x)
        + gibbsPmf f lam x - Q x
        = (-(Real.negMulLog (Q x)))
          + (-(Q x * Real.log (gibbsPmf f lam x)))
          + (gibbsPmf f lam x - Q x) := by
    intro x; ring
  rw [Finset.sum_congr rfl (fun x _ ↦ h_split x)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- ∑ (-(negMulLog (Q x))) = - ∑ negMulLog (Q x)
  rw [show (∑ x, -(Real.negMulLog (Q x))) = -(∑ x, Real.negMulLog (Q x)) from by
        rw [← Finset.sum_neg_distrib]]
  -- ∑ -(Q x * log (gibbs x)) = -(∑ Q x * log gibbs x)
  rw [show (∑ x, -(Q x * Real.log (gibbsPmf f lam x)))
          = -(∑ x, Q x * Real.log (gibbsPmf f lam x)) from by
        rw [← Finset.sum_neg_distrib]]
  -- ∑ Q x * log gibbs x = ∑ Q x * (⟨λ,f⟩(x) - log Z) using log_gibbsPmf.
  have h_inner : ∀ x : α,
      Q x * Real.log (gibbsPmf f lam x)
        = Q x * (∑ i, lam i * f i x) - Q x * Real.log (gibbsZ f lam) := by
    intro x
    rw [log_gibbsPmf f lam x]; ring
  rw [show (∑ x, Q x * Real.log (gibbsPmf f lam x))
        = ∑ x, (Q x * (∑ i, lam i * f i x) - Q x * Real.log (gibbsZ f lam))
      from Finset.sum_congr rfl (fun x _ ↦ h_inner x)]
  rw [Finset.sum_sub_distrib]
  -- ∑ Q x * ⟨λ,f⟩(x) = ⟨λ, 𝔼_Q[f]⟩  (swap sum order)
  have h_lin : (∑ x, Q x * (∑ i, lam i * f i x))
                = ∑ i, lam i * (∑ x, Q x * f i x) := by
    -- Expand Q x * (∑ i, ...) to ∑ i, lam i * (Q x * f i x), swap sums, factor lam i.
    have step1 : (∑ x, Q x * (∑ i, lam i * f i x))
                  = ∑ x, ∑ i, lam i * (Q x * f i x) := by
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      ring
    rw [step1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [← Finset.mul_sum]
  rw [h_lin]
  -- ∑ Q x * log Z = (∑ Q x) * log Z = 1 * log Z = log Z
  rw [show (∑ x, Q x * Real.log (gibbsZ f lam))
        = (∑ x, Q x) * Real.log (gibbsZ f lam) from by
        rw [Finset.sum_mul]]
  rw [hQ_sum, one_mul]
  -- ∑ (gibbs x - Q x) = ∑ gibbs x - ∑ Q x = 1 - 1 = 0
  rw [Finset.sum_sub_distrib, gibbsPmf_sum_eq_one f lam, hQ_sum, sub_self]
  ring

omit [DecidableEq α] in
/-- **Maximum entropy theorem** (upper bound, pmf form): under moment constraints
`∑ x, P x · f i x = c i` for all `i`, and assuming the same constraints hold for the
Boltzmann–Gibbs ansatz `gibbsPmf f λ` for some fixed Lagrange parameter
`lam : Fin k → ℝ`, the entropy of `P` is bounded by the entropy of the gibbs
distribution:

  H(P) ≤ H(gibbsPmf f λ).

The Lagrange parameter `lam` is passed in as a hypothesis (with the matching
constraint witness `h_gibbs_constraints`), so the result does not need ψ(λ) convexity
or any Lagrange-multiplier existence theory. -/
@[entry_point]
theorem entropy_le_gibbs_of_constraints [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (gibbsPmf f lam x) := by
  classical
  -- Gibbs inequality: klDivPmf P G ≥ 0.
  have h_KL_P : 0 ≤ klDivPmf P (gibbsPmf f lam) :=
    klDivPmf_nonneg P (gibbsPmf f lam) hP.1 (fun a ↦ gibbsPmf_nonneg f lam a)
  -- Self-KL: klDivPmf G G = 0.
  have h_KL_G : klDivPmf (gibbsPmf f lam) (gibbsPmf f lam) = 0 :=
    klDivPmf_self_eq_zero (gibbsPmf f lam) (gibbsPmf_pos f lam)
  -- Core identity at Q := P.
  have h_eq_P := klDivPmf_gibbsPmf_eq f lam P hP
  -- Core identity at Q := gibbsPmf f lam.
  have h_eq_G := klDivPmf_gibbsPmf_eq f lam (gibbsPmf f lam)
                    (gibbsPmf_mem_stdSimplex f lam)
  -- Inner product of lam with the constraints is the same for P and G (= ⟨λ, c⟩).
  have h_inner_P : (∑ i, lam i * (∑ x, P x * f i x))
                    = ∑ i, lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [hP_constraints i]
  have h_inner_G : (∑ i, lam i * (∑ x, gibbsPmf f lam x * f i x))
                    = ∑ i, lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [h_gibbs_constraints i]
  rw [h_inner_P] at h_eq_P
  rw [h_inner_G] at h_eq_G
  -- Combine: H(G) - H(P) = klDivPmf P G - 0 ≥ 0.
  linarith

/-! ## Uniqueness -/

omit [DecidableEq α] in
/-- For a full-support reference pmf `Q`, `klDivPmf P Q = 0 ↔ P = Q`. -/
lemma klDivPmf_eq_zero_iff_pmf
    {P Q : α → ℝ} (hP : P ∈ stdSimplex ℝ α) (_hQ : Q ∈ stdSimplex ℝ α)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf P Q = 0 ↔ P = Q := by
  constructor
  · -- (→) klDivPmf P Q = 0 → P = Q.
    intro h
    -- Each summand of the sum is non-negative, so all must be zero.
    have h_per_zero : ∀ a, Q a * InformationTheory.klFun (P a / Q a) = 0 := by
      have h_per_nn : ∀ a ∈ Finset.univ,
          0 ≤ Q a * InformationTheory.klFun (P a / Q a) := fun a _ ↦
        mul_nonneg (hQ_pos a).le
          (InformationTheory.klFun_nonneg (div_nonneg (hP.1 a) (hQ_pos a).le))
      have h_sum_zero : ∑ a, Q a * InformationTheory.klFun (P a / Q a) = 0 := h
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg h_per_nn).mp h_sum_zero a (Finset.mem_univ a)
    funext a
    -- Q a > 0 and the per-term factor is zero, so klFun (P a / Q a) = 0.
    have h_kl_zero : InformationTheory.klFun (P a / Q a) = 0 := by
      have := h_per_zero a
      rcases mul_eq_zero.mp this with hQ0 | hkl
      · exact absurd hQ0 (hQ_pos a).ne'
      · exact hkl
    have h_ratio_nn : 0 ≤ P a / Q a := div_nonneg (hP.1 a) (hQ_pos a).le
    -- klFun y = 0 iff y = 1; so P a / Q a = 1, hence P a = Q a.
    have h_ratio_one : P a / Q a = 1 :=
      (InformationTheory.klFun_eq_zero_iff h_ratio_nn).mp h_kl_zero
    have hQne : Q a ≠ 0 := (hQ_pos a).ne'
    field_simp at h_ratio_one
    exact h_ratio_one
  · -- (←) P = Q → klDivPmf P Q = 0 (use klDivPmf_self_eq_zero).
    intro h
    rw [h]
    exact klDivPmf_self_eq_zero Q hQ_pos

omit [DecidableEq α] in
/-- **Maximum entropy theorem** (uniqueness, pmf form): `H(P) = H(gibbsPmf f λ)` if and
only if `P = gibbsPmf f λ` pointwise. -/
@[entry_point]
theorem entropy_eq_gibbs_iff_of_constraints [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (gibbsPmf f lam x)
      ↔ P = gibbsPmf f lam := by
  -- Core identity at Q := P and Q := gibbsPmf f lam.
  have h_eq_P := klDivPmf_gibbsPmf_eq f lam P hP
  have h_eq_G := klDivPmf_gibbsPmf_eq f lam (gibbsPmf f lam)
                    (gibbsPmf_mem_stdSimplex f lam)
  have h_inner_P : (∑ i, lam i * (∑ x, P x * f i x))
                    = ∑ i, lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [hP_constraints i]
  have h_inner_G : (∑ i, lam i * (∑ x, gibbsPmf f lam x * f i x))
                    = ∑ i, lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [h_gibbs_constraints i]
  rw [h_inner_P] at h_eq_P
  rw [h_inner_G] at h_eq_G
  have h_KL_G : klDivPmf (gibbsPmf f lam) (gibbsPmf f lam) = 0 :=
    klDivPmf_self_eq_zero (gibbsPmf f lam) (gibbsPmf_pos f lam)
  -- From h_eq_P and h_eq_G:
  --   klDivPmf P G = -H(P) - ⟨λ,c⟩ + log Z
  --   0            = -H(G) - ⟨λ,c⟩ + log Z   (since klDivPmf G G = 0)
  -- Subtracting: klDivPmf P G = H(G) - H(P).
  have h_KL_eq : klDivPmf P (gibbsPmf f lam)
                  = (∑ x, Real.negMulLog (gibbsPmf f lam x))
                    - (∑ x, Real.negMulLog (P x)) := by
    linarith
  rw [show (∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (gibbsPmf f lam x))
        ↔ klDivPmf P (gibbsPmf f lam) = 0 from by
        constructor
        · intro h; linarith
        · intro h; linarith]
  exact klDivPmf_eq_zero_iff_pmf hP (gibbsPmf_mem_stdSimplex f lam)
          (gibbsPmf_pos f lam)

/-! ## Special cases -/

/-! ### Zero feature map reduces to uniform pmf -/

omit [DecidableEq α] in
/-- `gibbsZ` of the zero feature map is just `Fintype.card α` (each `exp 0 = 1` summed
`N` times). -/
lemma gibbsZ_zero [Nonempty α] (lam : Fin k → ℝ) :
    gibbsZ (0 : Fin k → α → ℝ) lam = (Fintype.card α : ℝ) := by
  unfold gibbsZ
  have h_term : ∀ y : α, Real.exp (∑ i, lam i * (0 : Fin k → α → ℝ) i y) = 1 := by
    intro y
    have h_sum_zero : (∑ i, lam i * (0 : Fin k → α → ℝ) i y) = 0 := by
      simp
    rw [h_sum_zero, Real.exp_zero]
  rw [Finset.sum_congr rfl (fun y _ ↦ h_term y)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

omit [DecidableEq α] in
/-- With the zero feature map, `gibbsPmf` is the uniform pmf `x ↦ 1 / Fintype.card α`. -/
lemma gibbsPmf_zero_eq_uniform [Nonempty α] (lam : Fin k → ℝ) :
    gibbsPmf (0 : Fin k → α → ℝ) lam = fun _ ↦ (1 : ℝ) / Fintype.card α := by
  funext x
  unfold gibbsPmf
  rw [gibbsZ_zero lam]
  have h_num : Real.exp (∑ i, lam i * (0 : Fin k → α → ℝ) i x) = 1 := by
    have : (∑ i, lam i * (0 : Fin k → α → ℝ) i x) = 0 := by simp
    rw [this, Real.exp_zero]
  rw [h_num]

omit [DecidableEq α] in
/-- Entropy of the uniform pmf `x ↦ 1 / N` is `log N`. -/
lemma entropy_uniform_pmf [Nonempty α] :
    ∑ _x : α, Real.negMulLog ((1 : ℝ) / Fintype.card α) = Real.log (Fintype.card α) := by
  set N : ℕ := Fintype.card α with hN_def
  have hN_pos : 0 < N := Fintype.card_pos
  have hN_pos_R : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hN_ne_R : (N : ℝ) ≠ 0 := hN_pos_R.ne'
  -- ∑ x, c = (Fintype.card α : ℕ) • c = (N : ℝ) * c.
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- N * negMulLog (1/N) = N * (-(1/N) * log (1/N))
  --                     = -log (1/N) = log N.
  rw [Real.negMulLog]
  rw [show ((1 : ℝ) / N) = (N : ℝ)⁻¹ from by rw [one_div]]
  rw [Real.log_inv]
  rw [← hN_def]
  field_simp

omit [DecidableEq α] in
/-- With the zero feature map, the Gibbs entropy equals `log (Fintype.card α)`. -/
@[entry_point]
theorem entropy_gibbsPmf_zero_eq_log_card [Nonempty α] (lam : Fin k → ℝ) :
    ∑ x : α, Real.negMulLog (gibbsPmf (0 : Fin k → α → ℝ) lam x)
      = Real.log (Fintype.card α) := by
  rw [show (fun x ↦ Real.negMulLog (gibbsPmf (0 : Fin k → α → ℝ) lam x))
        = (fun _ : α ↦ Real.negMulLog ((1 : ℝ) / Fintype.card α)) from by
        funext x
        rw [gibbsPmf_zero_eq_uniform lam]]
  exact entropy_uniform_pmf

/-! ### Bernoulli case -/

/-- The two-point feature map: indicator of `true`. -/
noncomputable def boolFeature : Fin 1 → Bool → ℝ :=
  fun _ b ↦ if b then 1 else 0

/-- For any `λ : Fin 1 → ℝ`,
`gibbsPmf boolFeature λ true + gibbsPmf boolFeature λ false = 1`. -/
lemma gibbsPmf_bool_sum_eq_one (lam : Fin 1 → ℝ) :
    gibbsPmf boolFeature lam true + gibbsPmf boolFeature lam false = 1 := by
  have h := gibbsPmf_sum_eq_one (α := Bool) boolFeature lam
  rw [Fintype.sum_bool] at h
  exact h

/-- For any `λ` and any `μ ∈ (0,1)`, if the mean constraint
`gibbsPmf boolFeature λ · 1 + gibbsPmf boolFeature λ · 0 = μ` holds, then
`gibbsPmf boolFeature λ true = μ`. -/
lemma gibbsPmf_bool_true_eq_of_mean
    (lam : Fin 1 → ℝ) (μ : ℝ)
    (h_mean : ∑ b : Bool, gibbsPmf boolFeature lam b * boolFeature 0 b = μ) :
    gibbsPmf boolFeature lam true = μ := by
  rw [Fintype.sum_bool] at h_mean
  -- boolFeature 0 true = 1, boolFeature 0 false = 0
  simp only [boolFeature, ↓reduceIte, mul_one, Bool.false_eq_true, mul_zero, add_zero] at h_mean
  exact h_mean

/-- Under the same mean constraint, `gibbsPmf boolFeature λ false = 1 - μ`. -/
lemma gibbsPmf_bool_false_eq_of_mean
    (lam : Fin 1 → ℝ) (μ : ℝ)
    (h_mean : ∑ b : Bool, gibbsPmf boolFeature lam b * boolFeature 0 b = μ) :
    gibbsPmf boolFeature lam false = 1 - μ := by
  have h_sum := gibbsPmf_bool_sum_eq_one lam
  have h_true := gibbsPmf_bool_true_eq_of_mean lam μ h_mean
  linarith

/-- Under mean constraint `μ`, the Gibbs
entropy on `Bool` is exactly the binary entropy `Real.binEntropy μ` (= textbook
`-μ log μ - (1-μ) log (1-μ)`, Ex. 12.1). -/
@[entry_point]
theorem entropy_gibbsPmf_bool_eq_binEntropy
    (lam : Fin 1 → ℝ) (μ : ℝ)
    (h_mean : ∑ b : Bool, gibbsPmf boolFeature lam b * boolFeature 0 b = μ) :
    ∑ b : Bool, Real.negMulLog (gibbsPmf boolFeature lam b) = Real.binEntropy μ := by
  rw [Fintype.sum_bool]
  rw [gibbsPmf_bool_true_eq_of_mean lam μ h_mean,
      gibbsPmf_bool_false_eq_of_mean lam μ h_mean]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-! ### Discretized exponential (geometric ratio form) -/

/-- The discrete "linear" feature map on `Fin (N+1)`: `f 0 x := (x.val : ℝ)`. -/
noncomputable def linearFeature {N : ℕ} : Fin 1 → Fin (N + 1) → ℝ :=
  fun _ x ↦ (x : ℝ)

/-- Geometric ratio form — setting `q := exp (λ 0)`,
the Gibbs distribution with the linear feature is the geometric ratio
`x ↦ q^x.val / ∑ y, q^y.val` on `Fin (N+1)`. Lagrange parameter `λ` is left as an
ansatz; choosing `λ 0 = log q` then yields the geometric distribution with ratio `q`. -/
@[entry_point]
theorem gibbsPmf_linearFeature_eq_geometric {N : ℕ} (lam : Fin 1 → ℝ) :
    gibbsPmf (linearFeature (N := N)) lam
      = fun x : Fin (N + 1) ↦
          (Real.exp (lam 0)) ^ (x : ℕ)
            / ∑ y : Fin (N + 1), (Real.exp (lam 0)) ^ (y : ℕ) := by
  funext x
  unfold gibbsPmf gibbsZ linearFeature
  -- Numerator: exp (∑ i, lam i * (x : ℝ)) where the sum is only over `i = 0`.
  --          = exp (lam 0 * (x : ℝ)) = exp (lam 0) ^ (x : ℕ).
  have h_num : Real.exp (∑ i, lam i * (x : ℝ)) = (Real.exp (lam 0)) ^ (x : ℕ) := by
    have h_sum : (∑ i : Fin 1, lam i * (x : ℝ)) = lam 0 * (x : ℝ) := by
      rw [Fin.sum_univ_one]
    rw [h_sum, show ((x : Fin (N + 1)) : ℝ) = ((x : ℕ) : ℝ) from rfl,
        show lam 0 * ((x : ℕ) : ℝ) = ((x : ℕ) : ℝ) * lam 0 from mul_comm _ _,
        ← Real.exp_nat_mul]
  -- Denominator: ∑ y, exp (lam 0 * (y : ℝ)) = ∑ y, (exp (lam 0)) ^ (y : ℕ).
  have h_den : (∑ y : Fin (N + 1), Real.exp (∑ i, lam i * (y : ℝ)))
                = ∑ y : Fin (N + 1), (Real.exp (lam 0)) ^ (y : ℕ) := by
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    have h_sum : (∑ i : Fin 1, lam i * (y : ℝ)) = lam 0 * (y : ℝ) := by
      rw [Fin.sum_univ_one]
    rw [h_sum, show ((y : Fin (N + 1)) : ℝ) = ((y : ℕ) : ℝ) from rfl,
        show lam 0 * ((y : ℕ) : ℝ) = ((y : ℕ) : ℝ) * lam 0 from mul_comm _ _,
        ← Real.exp_nat_mul]
  rw [h_num, h_den]

end InformationTheory.Shannon.MaxEntropyConstrained
