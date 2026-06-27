/-
Chernoff converse (Cover–Thomas Theorem 11.9.1, converse half).

The achievability half (`chernoff_lemma_achievability`, `Chernoff/Basic.lean`) gives
`chernoffInfo P₁ P₂ ≤ liminf_n -(1/n) log bayesErrorMinPmf`. This file builds the converse
`limsup_n -(1/n) log bayesErrorMinPmf ≤ chernoffInfo P₁ P₂`: the optimal Bayes error exponent
cannot exceed the Chernoff information.

Plan + phase breakdown: `docs/shannon/chernoff-converse-plan.md`. The conceptual crux — the
I-projection (Csiszár) Pythagorean theorem `CsiszarProjection.csiszar_pythagoras_inequality` —
is already genuine in-project; this file wires the exponential-tilt mediator
`chernoffMediator P₁ P₂ λ*` to it and to the Sanov LDP lower bound.
-/
import InformationTheory.Shannon.Chernoff.Basic

namespace InformationTheory.Shannon.Chernoff

open Real Filter
open InformationTheory.Shannon.CsiszarProjection
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Phase A — pmf-level variational identity

The divergence of the Chernoff mediator `T_λ = P₁^{1-λ}P₂^λ / Z(λ)` against `P₁` has the
closed form `λ · E_{T_λ}[log(P₂/P₁)] - log Z(λ)`. At the optimal `λ*` (interior, where the
mean log-likelihood-ratio vanishes — the first-order condition of the `chernoffInfo` inf) the
first term drops, giving `klDivPmf (T_λ*) P₁ = -log Z(λ*) = chernoffInfo P₁ P₂`. -/

omit [DecidableEq α] in
/-- Closed form for the mediator divergence:
`klDivPmf (chernoffMediator P₁ P₂ λ) P₁ = λ · (∑ a, T_λ(a)·log(P₂ a/P₁ a)) - log Z(λ)`. -/
lemma chernoffMediator_klDiv_eq
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (lam : ℝ) :
    klDivPmf (chernoffMediator P₁ P₂ lam) P₁
      = lam * (∑ a, chernoffMediator P₁ P₂ lam a * Real.log (P₂ a / P₁ a))
        - Real.log (chernoffZSum P₁ P₂ lam) := by
  have hT_pos : ∀ a, 0 < chernoffMediator P₁ P₂ lam a :=
    fun a ↦ chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a
  have hT_sum : ∑ a, chernoffMediator P₁ P₂ lam a = 1 :=
    chernoffMediator_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  rw [klDivPmf_eq_log_diff_sum hT_sum hP₁_sum hT_pos hP₁_pos]
  -- Per-term: T a · (log(T a) − log(P₁ a)) = T a · (λ·log(P₂ a/P₁ a) − log Z).
  have h_term : ∀ a : α,
      chernoffMediator P₁ P₂ lam a
          * (Real.log (chernoffMediator P₁ P₂ lam a) - Real.log (P₁ a))
        = chernoffMediator P₁ P₂ lam a
          * (lam * Real.log (P₂ a / P₁ a) - Real.log (chernoffZSum P₁ P₂ lam)) := by
    intro a
    have hnum_pos : 0 < P₁ a ^ (1 - lam) * P₂ a ^ lam :=
      mul_pos (Real.rpow_pos_of_pos (hP₁_pos a) _) (Real.rpow_pos_of_pos (hP₂_pos a) _)
    have hlogT : Real.log (chernoffMediator P₁ P₂ lam a)
        = (1 - lam) * Real.log (P₁ a) + lam * Real.log (P₂ a)
          - Real.log (chernoffZSum P₁ P₂ lam) := by
      unfold chernoffMediator
      rw [Real.log_div hnum_pos.ne' hZ_pos.ne',
          Real.log_mul (Real.rpow_pos_of_pos (hP₁_pos a) _).ne'
            (Real.rpow_pos_of_pos (hP₂_pos a) _).ne',
          Real.log_rpow (hP₁_pos a), Real.log_rpow (hP₂_pos a)]
    have hLLR : Real.log (P₂ a / P₁ a) = Real.log (P₂ a) - Real.log (P₁ a) :=
      Real.log_div (hP₂_pos a).ne' (hP₁_pos a).ne'
    rw [hlogT, hLLR]; ring
  rw [Finset.sum_congr rfl (fun a _ ↦ h_term a)]
  -- ∑ T·(λ·L − log Z) = λ·∑(T·L) − log Z·∑T = λ·∑(T·L) − log Z.
  have h_expand :
      (∑ a, chernoffMediator P₁ P₂ lam a
          * (lam * Real.log (P₂ a / P₁ a) - Real.log (chernoffZSum P₁ P₂ lam)))
        = lam * (∑ a, chernoffMediator P₁ P₂ lam a * Real.log (P₂ a / P₁ a))
          - Real.log (chernoffZSum P₁ P₂ lam)
            * (∑ a, chernoffMediator P₁ P₂ lam a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  rw [h_expand, hT_sum, mul_one]

/-! ### Phase B/C — Sanov lower bound + assembly

Target headline (lives in `docs/shannon/chernoff-converse-plan.md` until proven, to keep the
project's 0-`sorry` invariant — the README publicly claims "no sorry"):

`chernoff_converse : limsup_n -(1/n) log (bayesErrorMinPmf P₁ P₂ n) ≤ chernoffInfo P₁ P₂`.

Route: `chernoffMediator P₁ P₂ λ*` is the I-projection of `P₁` onto the half-space
`{p : ∑ p_a log(P₂ a/P₁ a) ≥ 0}`; `csiszar_pythagoras_inequality` identifies
`⨅_{p∈K} klDivPmf p P₁` with `klDivPmf (T_λ*) P₁ = chernoffInfo` (Phase A). The error region
`{x : P₁ⁿ(x) ≤ P₂ⁿ(x)}` is that half-space lifted to empirical type classes, so
`sanov_ldp_equality` supplies `(1/n) log P₁ⁿ(region) → -chernoffInfo`, and
`bayesErrorMinPmf ≥ (1/2)·P₁ⁿ(region)` closes the converse. -/

end InformationTheory.Shannon.Chernoff
