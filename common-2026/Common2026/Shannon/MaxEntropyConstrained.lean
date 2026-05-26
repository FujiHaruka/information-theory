import Common2026.Meta.EntryPoint
import Common2026.Shannon.CsiszarProjection
import Common2026.Shannon.Chernoff
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Constrained Maximum Entropy (Cover–Thomas Theorem 12.1.1) — T3-A

有限アルファベット `α` 上の pmf `P : α → ℝ` (∈ `stdSimplex ℝ α`) について、
モーメント制約 `∑ x, P x · f i x = c i` (`i = 1..k`) のもとで Shannon entropy
`H(P) = ∑ x, negMulLog (P x)` を最大化する分布は **Boltzmann–Gibbs exponential family**

  gibbsPmf f λ x := exp (∑ i, λ i · f i x) / ∑ y, exp (∑ i, λ i · f i y)

で表される (Lagrange parameter `λ` を **ansatz として外から受け取る** pass-through 設計)。

## 主定理

* `gibbsPmf`                       — Boltzmann–Gibbs pmf 定義
* `gibbsPmf_mem_stdSimplex`        — `gibbsPmf f λ` は pmf (∈ `stdSimplex`)
* `entropy_le_gibbs_of_constraints`
                                   — **Tier 1 上界**: 制約下で `H(P) ≤ H(gibbsPmf f λ)`
* `entropy_eq_gibbs_iff_of_constraints`
                                   — **Tier 2 uniqueness**: 等号 ⟺ `P = gibbsPmf f λ`

## Approach

KKT / Lagrange duality は Mathlib に未整備 (`LagrangeMultipliers.lean:22-24` で TODO
明記、KKT 不在)。本ファイルではこれを **Gibbs + Csiszár `klDivPmf` 直接ルート** で回避:

```
0 ≤ klDivPmf P (gibbsPmf f λ)                    -- CsiszarProjection.klDivPmf_nonneg
  = -H(P) - ⟨λ, 𝔼_P[f]⟩ + log Z(λ)               -- 核 identity
  = -H(P) - ⟨λ, c⟩    + log Z(λ)                 -- hP_constraints

0 = klDivPmf (gibbsPmf f λ) (gibbsPmf f λ)       -- Chernoff.klDivPmf_self_eq_zero
  = -H(gibbsPmf f λ) - ⟨λ, c⟩ + log Z(λ)         -- h_gibbs_constraints

∴ H(P) ≤ H(gibbsPmf f λ)
```

ansatz `λ` を主定理 signature の hypothesis として外から取ることで、ψ(λ) 凸性 /
Lagrange parameter 存在性 (Mathlib 不在道具立て) を**完全に回避**する。Lagrange
parameter の存在性は別 plan (`max-entropy-constrained-existence-*`) で扱う想定。

`Mathlib/MeasureTheory/Measure/Tilted.lean` ではなく `CsiszarProjection.klDivPmf` の
pmf 形を採用したのは:
1. Csiszár 既存 API (`klDivPmf_nonneg`, `klDivPmf_strictConvexOn_left`,
   `klDivPmf_self_eq_zero`) が pmf 形に閉じている
2. `Real.exp / log` の算術だけで gibbs と `log Z` が閉じる (`Tilted` の
   `rnDeriv` / `=ᵐ` 議論を完全回避)
-/

namespace InformationTheory.Shannon.MaxEntropyConstrained

set_option linter.unusedSectionVars false

open Real InformationTheory
open InformationTheory.Shannon.CsiszarProjection (klDivPmf klDivPmf_nonneg)
open InformationTheory.Shannon.Chernoff (klDivPmf_self_eq_zero)
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {k : ℕ}

/-! ## Phase A — `gibbsPmf` 定義 + 基本性質 (Tier 0) -/

/-- Partition function `Z(λ) := ∑ y, exp (∑ i, λ i · f i y)`. Independent `def` so
that `Real.log Z(λ)` can be reused throughout Phase B's core identity. -/
noncomputable def gibbsZ (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : ℝ :=
  ∑ y, Real.exp (∑ i, lam i * f i y)

/-- **Boltzmann–Gibbs exponential family pmf**, parametrized by Lagrange parameter
`lam : Fin k → ℝ` and feature maps `f : Fin k → α → ℝ`:

  gibbsPmf f λ x := exp (∑ i, λ i · f i x) / Z(λ).

The denominator `Z(λ)` (`gibbsZ f lam`) is the partition function. -/
noncomputable def gibbsPmf (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : α → ℝ :=
  fun x => Real.exp (∑ i, lam i * f i x) / gibbsZ f lam

/-- The partition function `Z(λ)` is strictly positive (each summand is `exp _ > 0`
and there is at least one term by `[Nonempty α]`). -/
lemma gibbsZ_pos [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    0 < gibbsZ f lam := by
  unfold gibbsZ
  apply Finset.sum_pos
  · intro y _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Each component of `gibbsPmf f λ` is strictly positive. -/
lemma gibbsPmf_pos [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
    0 < gibbsPmf f lam x := by
  unfold gibbsPmf
  exact div_pos (Real.exp_pos _) (gibbsZ_pos f lam)

/-- `gibbsPmf f λ` is non-negative pointwise (corollary of positivity). -/
lemma gibbsPmf_nonneg [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
    0 ≤ gibbsPmf f lam x :=
  (gibbsPmf_pos f lam x).le

/-- The mass of `gibbsPmf f λ` sums to `1`. -/
lemma gibbsPmf_sum_eq_one [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    ∑ x, gibbsPmf f lam x = 1 := by
  unfold gibbsPmf
  rw [← Finset.sum_div]
  exact div_self (gibbsZ_pos f lam).ne'

/-- `gibbsPmf f λ ∈ stdSimplex ℝ α`. -/
lemma gibbsPmf_mem_stdSimplex [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    gibbsPmf f lam ∈ stdSimplex ℝ α :=
  ⟨fun x => gibbsPmf_nonneg f lam x, gibbsPmf_sum_eq_one f lam⟩

/-- Closed form for `log (gibbsPmf f λ x)`: the numerator's exponent minus `log Z(λ)`.
Phase B 核 identity の入口。 -/
lemma log_gibbsPmf [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
    Real.log (gibbsPmf f lam x)
      = (∑ i, lam i * f i x) - Real.log (gibbsZ f lam) := by
  unfold gibbsPmf
  rw [Real.log_div (Real.exp_ne_zero _) (gibbsZ_pos f lam).ne']
  rw [Real.log_exp]

/-! ## Phase B — 核 identity + Tier 1 主定理 -/

/-- **Core algebraic identity (Phase B の重力中心)** — for any `Q ∈ stdSimplex` on `α`,
the KL divergence from `Q` to `gibbsPmf f λ` decomposes into negative entropy,
the constraint inner product `⟨λ, 𝔼_Q[f]⟩`, and `log Z(λ)`:

  klDivPmf Q (gibbsPmf f λ)
    = -H(Q) - ⟨λ, 𝔼_Q[f]⟩ + log Z(λ).

Both the Tier 1 upper bound and the Tier 2 uniqueness recipe reduce to one application
of this identity at `Q := P` plus another at `Q := gibbsPmf f λ`. -/
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
    exact Finset.sum_congr rfl (fun x _ => h_per x)
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
  rw [Finset.sum_congr rfl (fun x _ => h_split x)]
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
      from Finset.sum_congr rfl (fun x _ => h_inner x)]
  rw [Finset.sum_sub_distrib]
  -- ∑ Q x * ⟨λ,f⟩(x) = ⟨λ, 𝔼_Q[f]⟩  (swap sum order)
  have h_lin : (∑ x, Q x * (∑ i, lam i * f i x))
                = ∑ i, lam i * (∑ x, Q x * f i x) := by
    -- Expand Q x * (∑ i, ...) to ∑ i, lam i * (Q x * f i x), swap sums, factor lam i.
    have step1 : (∑ x, Q x * (∑ i, lam i * f i x))
                  = ∑ x, ∑ i, lam i * (Q x * f i x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [step1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
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

/-- **T3-A 主定理 (Tier 1 上界)** — Cover–Thomas Theorem 12.1.1, pmf 形:
under moment constraints `∑ x, P x · f i x = c i` for all `i`, and assuming the same
constraints hold for the Boltzmann–Gibbs ansatz `gibbsPmf f λ` for some fixed Lagrange
parameter `lam : Fin k → ℝ`, the entropy of `P` is bounded by the entropy of the gibbs
distribution:

  H(P) ≤ H(gibbsPmf f λ).

The Lagrange parameter `lam` is **passed in as a hypothesis** (with the matching
constraint witness `h_gibbs_constraints`), so the proof does not need ψ(λ) convexity
or any Lagrange-multiplier existence theory. -/
@[entry_point]
theorem entropy_le_gibbs_of_constraints [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (gibbsPmf f lam x) := by
  -- Gibbs inequality: klDivPmf P G ≥ 0.
  have h_KL_P : 0 ≤ klDivPmf P (gibbsPmf f lam) :=
    klDivPmf_nonneg P (gibbsPmf f lam) hP.1 (fun a => gibbsPmf_nonneg f lam a)
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
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hP_constraints i]
  have h_inner_G : (∑ i, lam i * (∑ x, gibbsPmf f lam x * f i x))
                    = ∑ i, lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_gibbs_constraints i]
  rw [h_inner_P] at h_eq_P
  rw [h_inner_G] at h_eq_G
  -- Combine: H(G) - H(P) = klDivPmf P G - 0 ≥ 0.
  linarith

/-! ## Phase C — Tier 2 uniqueness -/

/-- Auxiliary: for a full-support reference pmf `Q`, `klDivPmf P Q = 0 ↔ P = Q`.
Used in `entropy_eq_gibbs_iff_of_constraints` to translate "KL = 0" into the pointwise
equality `P = gibbsPmf f λ`. -/
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
          0 ≤ Q a * InformationTheory.klFun (P a / Q a) := fun a _ =>
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

/-- **T3-A uniqueness (Tier 2)** — entropy equality `H(P) = H(gibbsPmf f λ)` is achieved
*if and only if* `P = gibbsPmf f λ` pointwise. -/
@[entry_point]
theorem entropy_eq_gibbs_iff_of_constraints [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (gibbsPmf f lam x)
      ↔ P = gibbsPmf f lam := by
  -- Core identity at Q := P and Q := gibbsPmf f lam (reuse B-2 setup).
  have h_eq_P := klDivPmf_gibbsPmf_eq f lam P hP
  have h_eq_G := klDivPmf_gibbsPmf_eq f lam (gibbsPmf f lam)
                    (gibbsPmf_mem_stdSimplex f lam)
  have h_inner_P : (∑ i, lam i * (∑ x, P x * f i x))
                    = ∑ i, lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hP_constraints i]
  have h_inner_G : (∑ i, lam i * (∑ x, gibbsPmf f lam x * f i x))
                    = ∑ i, lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
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

/-! ## Phase E — 特例展開 (Tier 3 stretch) -/

/-! ### E-1 Uniform 退化 (空制約 ⟹ uniform pmf, 教科書 12.1 trivial case)

`f := 0 : Fin k → α → ℝ` (例えば `k = 0` の空制約) のとき、`gibbsPmf` は uniform pmf
`x ↦ 1 / Fintype.card α` に等しい (`λ` の値に無依存)。エントロピーは `log (Fintype.card α)`
で、`MaxEntropy.entropy_le_log_card` の pmf 形に一致する。
-/

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
  rw [Finset.sum_congr rfl (fun y _ => h_term y)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- With the zero feature map, `gibbsPmf` is the uniform pmf `x ↦ 1 / Fintype.card α`. -/
lemma gibbsPmf_zero_eq_uniform [Nonempty α] (lam : Fin k → ℝ) :
    gibbsPmf (0 : Fin k → α → ℝ) lam = fun _ => (1 : ℝ) / Fintype.card α := by
  funext x
  unfold gibbsPmf
  rw [gibbsZ_zero lam]
  have h_num : Real.exp (∑ i, lam i * (0 : Fin k → α → ℝ) i x) = 1 := by
    have : (∑ i, lam i * (0 : Fin k → α → ℝ) i x) = 0 := by simp
    rw [this, Real.exp_zero]
  rw [h_num]

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

/-- **E-1 (Tier 3 特例)** — エントロピーの uniform pmf 評価値:
`∑ x, negMulLog (gibbsPmf 0 lam x) = log (Fintype.card α)`. これは
`MaxEntropy.entropy_le_log_card` の pmf 形 (sup) と一致する。 -/
@[entry_point]
theorem entropy_gibbsPmf_zero_eq_log_card [Nonempty α] (lam : Fin k → ℝ) :
    ∑ x : α, Real.negMulLog (gibbsPmf (0 : Fin k → α → ℝ) lam x)
      = Real.log (Fintype.card α) := by
  rw [show (fun x => Real.negMulLog (gibbsPmf (0 : Fin k → α → ℝ) lam x))
        = (fun _ : α => Real.negMulLog ((1 : ℝ) / Fintype.card α)) from by
        funext x
        rw [gibbsPmf_zero_eq_uniform lam]]
  exact entropy_uniform_pmf

/-! ### E-2 Two-point exponential (Bernoulli, 教科書 Ex. 12.1)

`α := Bool`, `k := 1`, `f 0 := fun b => if b then 1 else 0`, `c 0 := μ` のとき、
mean constraint `gibbsPmf f λ true * 1 + gibbsPmf f λ false * 0 = μ` を満たす ansatz `λ`
について、`gibbsPmf f λ true = μ`, `gibbsPmf f λ false = 1 - μ` で entropy が `binEntropy μ`
に等しい。Lagrange parameter の具体値 `λ 0 = log (μ / (1-μ))` は scope 外 (ansatz pass-through)。
-/

/-- The two-point feature map: indicator of `true`. -/
noncomputable def boolFeature : Fin 1 → Bool → ℝ :=
  fun _ b => if b then 1 else 0

/-- For any `λ : Fin 1 → ℝ`, `gibbsPmf boolFeature λ true + gibbsPmf boolFeature λ false = 1`
(restatement of `gibbsPmf_sum_eq_one` on `Bool`). -/
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
  simp [boolFeature] at h_mean
  exact h_mean

/-- Companion to the above: `gibbsPmf boolFeature λ false = 1 - μ`. -/
lemma gibbsPmf_bool_false_eq_of_mean
    (lam : Fin 1 → ℝ) (μ : ℝ)
    (h_mean : ∑ b : Bool, gibbsPmf boolFeature lam b * boolFeature 0 b = μ) :
    gibbsPmf boolFeature lam false = 1 - μ := by
  have h_sum := gibbsPmf_bool_sum_eq_one lam
  have h_true := gibbsPmf_bool_true_eq_of_mean lam μ h_mean
  linarith

/-- **E-2 (Tier 3 特例)** — Bernoulli ansatz: under mean constraint `μ`, the gibbs
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

/-! ### E-3 Discretized exponential (geometric ratio form, 教科書 Ex. 12.2)

`α := Fin (N+1)` (`Nonempty` 確保のため `Nat.succ`), `k := 1`,
`f 0 := fun x => (x : ℝ)` のとき、`gibbsPmf` は geometric ratio `q := exp (λ 0)` で
`x ↦ q^x / ∑ y, q^y` 形 (closed form)。Lagrange parameter `λ` の存在性 / mean `μ` との
具体的対応は scope 外 (ansatz pass-through、`gibbsPmf` の shape のみ確定する)。
-/

/-- The discrete "linear" feature map on `Fin (N+1)`: `f 0 x := (x.val : ℝ)`. -/
noncomputable def linearFeature {N : ℕ} : Fin 1 → Fin (N + 1) → ℝ :=
  fun _ x => (x : ℝ)

/-- **E-3 (Tier 3 特例)** — discretized exponential closed form: setting `q := exp (λ 0)`,
the Gibbs distribution with the linear feature is the geometric ratio
`x ↦ q^x.val / ∑ y, q^y.val` on `Fin (N+1)`. Lagrange parameter `λ` is left as an
ansatz; choosing `λ 0 = log q` then yields the geometric distribution with ratio `q`. -/
@[entry_point]
theorem gibbsPmf_linearFeature_eq_geometric {N : ℕ} (lam : Fin 1 → ℝ) :
    gibbsPmf (linearFeature (N := N)) lam
      = fun x : Fin (N + 1) =>
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
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have h_sum : (∑ i : Fin 1, lam i * (y : ℝ)) = lam 0 * (y : ℝ) := by
      rw [Fin.sum_univ_one]
    rw [h_sum, show ((y : Fin (N + 1)) : ℝ) = ((y : ℕ) : ℝ) from rfl,
        show lam 0 * ((y : ℕ) : ℝ) = ((y : ℕ) : ℝ) * lam 0 from mul_comm _ _,
        ← Real.exp_nat_mul]
  rw [h_num, h_den]

end InformationTheory.Shannon.MaxEntropyConstrained
