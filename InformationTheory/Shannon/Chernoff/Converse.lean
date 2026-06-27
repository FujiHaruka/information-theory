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
import InformationTheory.Shannon.Sanov.LDP
import InformationTheory.Shannon.Sanov.LiminfBound
import InformationTheory.Shannon.Sanov.RoundedTypeSequence
import InformationTheory.Shannon.KLDivContinuous
import InformationTheory.Shannon.Hoeffding.Tradeoff
import InformationTheory.Shannon.Hoeffding.TradeoffExp
import InformationTheory.Shannon.MaxEntropy.Constrained
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

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

/-! #### Per-term log identity, the `log Z` derivative, and the balance (FOC)

`chernoffMediator_log_sub` is the per-term identity already implicit in the atom;
`chernoffLogZ_hasDerivAt` differentiates `log Z` (the analytic core), and
`chernoffMediator_balance` reads off the first-order condition at an interior minimizer. -/

omit [DecidableEq α] in
/-- Per-term log identity: `log(T_λ a) - log(P₁ a) = λ·log(P₂ a/P₁ a) - log Z(λ)`. -/
lemma chernoffMediator_log_sub
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    Real.log (chernoffMediator P₁ P₂ lam a) - Real.log (P₁ a)
      = lam * Real.log (P₂ a / P₁ a) - Real.log (chernoffZSum P₁ P₂ lam) := by
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
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

omit [DecidableEq α] in
/-- The derivative of `λ ↦ log Z(λ)` is the mediator-weighted mean log-likelihood-ratio:
`d/dλ log Z(λ) = ∑ a, T_λ(a)·log(P₂ a/P₁ a)`. -/
lemma chernoffLogZ_hasDerivAt
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    HasDerivAt (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l))
      (∑ a, chernoffMediator P₁ P₂ lam a * Real.log (P₂ a / P₁ a)) lam := by
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  -- Per-term derivative: `d/dλ (P₁ a^(1-λ)·P₂ a^λ) = (P₁ a^(1-λ)·P₂ a^λ)·(log P₂ a − log P₁ a)`.
  have hterm : ∀ a : α, HasDerivAt (fun l : ℝ ↦ P₁ a ^ (1 - l) * P₂ a ^ l)
      ((P₁ a ^ (1 - lam) * P₂ a ^ lam) * (Real.log (P₂ a) - Real.log (P₁ a))) lam := by
    intro a
    have hf : HasDerivAt (fun l : ℝ ↦ 1 - l) (-1 : ℝ) lam :=
      HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id lam)
    have h1 : HasDerivAt (fun l : ℝ ↦ P₁ a ^ (1 - l))
        (Real.log (P₁ a) * (-1) * P₁ a ^ (1 - lam)) lam :=
      HasDerivAt.const_rpow (hP₁_pos a) hf
    have h2 : HasDerivAt (fun l : ℝ ↦ P₂ a ^ l)
        (Real.log (P₂ a) * 1 * P₂ a ^ lam) lam :=
      HasDerivAt.const_rpow (hP₂_pos a) (hasDerivAt_id lam)
    have hmul := HasDerivAt.mul h1 h2
    have hval : (P₁ a ^ (1 - lam) * P₂ a ^ lam) * (Real.log (P₂ a) - Real.log (P₁ a))
        = Real.log (P₁ a) * (-1) * P₁ a ^ (1 - lam) * P₂ a ^ lam
          + P₁ a ^ (1 - lam) * (Real.log (P₂ a) * 1 * P₂ a ^ lam) := by ring
    rw [hval]; exact hmul
  -- Sum over the alphabet: `d/dλ Z(λ) = ∑ a, (...)·(log P₂ a − log P₁ a)`.
  have hZ : HasDerivAt (fun l : ℝ ↦ ∑ a, P₁ a ^ (1 - l) * P₂ a ^ l)
      (∑ a, (P₁ a ^ (1 - lam) * P₂ a ^ lam) * (Real.log (P₂ a) - Real.log (P₁ a))) lam := by
    apply HasDerivAt.fun_sum
    intro a _
    exact hterm a
  -- The mediator-weighted sum equals `Z'(λ) / Z(λ)`.
  have hval :
      (∑ a, chernoffMediator P₁ P₂ lam a * Real.log (P₂ a / P₁ a))
        = (∑ a, (P₁ a ^ (1 - lam) * P₂ a ^ lam) * (Real.log (P₂ a) - Real.log (P₁ a)))
          / chernoffZSum P₁ P₂ lam := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    unfold chernoffMediator
    rw [Real.log_div (hP₂_pos a).ne' (hP₁_pos a).ne']
    ring
  rw [hval]
  exact HasDerivAt.log hZ hZ_pos.ne'

omit [DecidableEq α] in
/-- Balance / first-order condition at an interior minimizer `λ* ∈ (0,1)` of `log Z`:
`∑ a, T_λ*(a)·log(P₂ a/P₁ a) = 0` (Fermat: the derivative vanishes at an interior min). -/
lemma chernoffMediator_balance
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io : lam ∈ Set.Ioo (0:ℝ) 1) :
    ∑ a, chernoffMediator P₁ P₂ lam a * Real.log (P₂ a / P₁ a) = 0 := by
  have hderiv := chernoffLogZ_hasDerivAt P₁ P₂ hP₁_pos hP₂_pos lam
  have hIcc_nhds : Set.Icc (0:ℝ) 1 ∈ nhds lam :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hlam_io) Set.Ioo_subset_Icc_self
  have hlocal : IsLocalMin (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) lam :=
    hlam_min.isLocalMin hIcc_nhds
  exact hlocal.hasDerivAt_eq_zero hderiv

/-! #### The half-space `K` and the I-projection identities -/

/-- The Chernoff half-space `K = {p : full-support pmf with `∑ p_a log(P₂ a/P₁ a) ≥ 0`}`,
onto which `chernoffMediator P₁ P₂ λ*` is the Csiszár I-projection of `P₁`. -/
def chernoffHalfSpace (P₁ P₂ : α → ℝ) : Set (α → ℝ) :=
  {p | (∀ a, 0 < p a) ∧ (∑ a, p a = 1) ∧ 0 ≤ ∑ a, p a * Real.log (P₂ a / P₁ a)}

omit [DecidableEq α] in
/-- At an interior minimizer `λ*` of `log Z`, the mediator divergence equals the Chernoff
information: `chernoffInfo P₁ P₂ = klDivPmf (T_λ*) P₁`. -/
theorem chernoffInfo_eq_mediator_div
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io : lam ∈ Set.Ioo (0:ℝ) 1)
    (hinfo : chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam))) :
    chernoffInfo P₁ P₂ = klDivPmf (chernoffMediator P₁ P₂ lam) P₁ := by
  have hbal := chernoffMediator_balance P₁ P₂ hP₁_pos hP₂_pos lam hlam_min hlam_io
  rw [chernoffMediator_klDiv_eq P₁ P₂ hP₁_pos hP₂_pos hP₁_sum lam, hbal, mul_zero, zero_sub]
  exact hinfo

omit [DecidableEq α] in
/-- The Chernoff mediator at an interior minimizer `λ*` is the Csiszár I-projection of `P₁`
onto the half-space `K`: it minimizes `klDivPmf · P₁` over `K`. -/
theorem chernoffMediator_isMinOn
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io : lam ∈ Set.Ioo (0:ℝ) 1) :
    IsMinOn (fun p : α → ℝ ↦ klDivPmf p P₁) (chernoffHalfSpace P₁ P₂)
      (chernoffMediator P₁ P₂ lam) := by
  have hbal := chernoffMediator_balance P₁ P₂ hP₁_pos hP₂_pos lam hlam_min hlam_io
  have hT_pos : ∀ a, 0 < chernoffMediator P₁ P₂ lam a :=
    fun a ↦ chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a
  have hT_sum : ∑ a, chernoffMediator P₁ P₂ lam a = 1 :=
    chernoffMediator_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam
  have hlam_nonneg : (0:ℝ) ≤ lam := hlam_io.1.le
  rw [isMinOn_iff]
  intro P hP
  obtain ⟨hP_pos, hP_sum, hP_half⟩ := hP
  -- Decompose `klDivPmf P P₁` through the mediator.
  have hdecomp := klDivPmf_decomp_via_intermediate hP_sum hT_sum hP₁_sum
    hP_pos hT_pos hP₁_pos
  -- The intermediate sum collapses to `λ·∑ P·L − log Z`.
  have hsum2 :
      (∑ a, P a * (Real.log (chernoffMediator P₁ P₂ lam a) - Real.log (P₁ a)))
        = lam * (∑ a, P a * Real.log (P₂ a / P₁ a))
          - Real.log (chernoffZSum P₁ P₂ lam) := by
    have h_term : ∀ a : α,
        P a * (Real.log (chernoffMediator P₁ P₂ lam a) - Real.log (P₁ a))
          = lam * (P a * Real.log (P₂ a / P₁ a))
            - Real.log (chernoffZSum P₁ P₂ lam) * P a := by
      intro a
      rw [chernoffMediator_log_sub P₁ P₂ hP₁_pos hP₂_pos lam a]; ring
    rw [Finset.sum_congr rfl (fun a _ ↦ h_term a),
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hP_sum, mul_one]
  -- The mediator divergence is `−log Z` (balance kills the linear term).
  have hT_div : klDivPmf (chernoffMediator P₁ P₂ lam) P₁
      = -(Real.log (chernoffZSum P₁ P₂ lam)) := by
    rw [chernoffMediator_klDiv_eq P₁ P₂ hP₁_pos hP₂_pos hP₁_sum lam, hbal, mul_zero, zero_sub]
  change klDivPmf (chernoffMediator P₁ P₂ lam) P₁ ≤ klDivPmf P P₁
  rw [hdecomp, hsum2, hT_div]
  have h1 : 0 ≤ klDivPmf P (chernoffMediator P₁ P₂ lam) :=
    klDivPmf_nonneg P _ (fun a ↦ (hP_pos a).le) (fun a ↦ (hT_pos a).le)
  have h2 : 0 ≤ lam * (∑ a, P a * Real.log (P₂ a / P₁ a)) :=
    mul_nonneg hlam_nonneg hP_half
  linarith

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

section PhaseB

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingTradeoffExp
open InformationTheory.Shannon.MaxEntropyConstrained

variable [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Discretised error region (H1): count vectors `c` (with `∑ c = n`) whose type class lands in
the likelihood-ratio test region `{x | ∏ P₁(x_i) ≤ ∏ P₂(x_i)}`. (Clone of `Hoeffding.E_r`.) -/
noncomputable def chernoffErrorCounts
    (P₁ P₂ : α → ℝ) (n : ℕ) : Finset (TypeCountIndex α n) :=
  letI := Classical.decPred
    (fun c : TypeCountIndex α n ↦
      (∑ a, (c a : ℕ)) = n ∧
        ∏ a, P₁ a ^ (c a : ℕ) ≤ ∏ a, P₂ a ^ (c a : ℕ))
  Finset.univ.filter
    (fun c : TypeCountIndex α n ↦
      (∑ a, (c a : ℕ)) = n ∧
        ∏ a, P₁ a ^ (c a : ℕ) ≤ ∏ a, P₂ a ^ (c a : ℕ))

lemma mem_chernoffErrorCounts_iff (P₁ P₂ : α → ℝ) (n : ℕ) (c : TypeCountIndex α n) :
    c ∈ chernoffErrorCounts P₁ P₂ n ↔
      (∑ a, (c a : ℕ)) = n ∧
        ∏ a, P₁ a ^ (c a : ℕ) ≤ ∏ a, P₂ a ^ (c a : ℕ) := by
  unfold chernoffErrorCounts
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- H2: product aggregation by counts — for `x ∈ typeClassByCount c`,
`∏ i, f (x i) = ∏ a, (f a)^(c a)`. (Multiplicative analogue of `sum_const_aggr_of_mem_typeClassByCount`.) -/
lemma prod_aggr_of_mem_typeClassByCount
    {n : ℕ} {c : α → ℕ} {x : Fin n → α} (hx : x ∈ typeClassByCount c) (f : α → ℝ) :
    (∏ i : Fin n, f (x i)) = ∏ a : α, (f a) ^ (c a) := by
  classical
  have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
    fun i _ ↦ Finset.mem_univ _
  have h := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset α)) h_maps f
  rw [← h]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [Finset.prod_const]
  have h_count : typeCount x a = c a := hx a
  unfold typeCount at h_count
  rw [h_count]

/-- Every count `typeCount x a` is at most `n`. -/
lemma typeCount_le {n : ℕ} (x : Fin n → α) (a : α) : typeCount x a ≤ n := by
  classical
  unfold typeCount
  calc (Finset.univ.filter (fun i : Fin n ↦ x i = a)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- The empirical counts of `x` sum to `n`. -/
lemma typeCount_sum_eq {n : ℕ} (x : Fin n → α) : (∑ a : α, typeCount x a) = n := by
  classical
  unfold typeCount
  have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      x i ∈ (Finset.univ : Finset α) := fun i _ ↦ Finset.mem_univ _
  have h := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset α)) h_maps (fun _ : Fin n ↦ (1 : ℕ))
  have h_filter_card : ∀ a : α,
      ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a).card
        = ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a), (1 : ℕ) := by
    intro a
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  rw [show (∑ a : α, ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a).card)
        = ∑ a : α, ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a), (1 : ℕ)
      from Finset.sum_congr rfl fun a _ ↦ h_filter_card a]
  rw [h]
  simp

/-- H3 (W3): the likelihood-ratio error region equals the union of error type classes. -/
lemma chernoffErrorRegion_eq_union (P₁ P₂ : α → ℝ) (n : ℕ) :
    {x : Fin n → α | ∏ i, P₁ (x i) ≤ ∏ i, P₂ (x i)}
      = ⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
          typeClassByCount (α := α) (fun a ↦ (c a : ℕ)) := by
  classical
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    -- The canonical count index of `x`, clamped into `Fin (n+1)`.
    have hlt : ∀ a, typeCount x a < n + 1 := fun a ↦ Nat.lt_succ_of_le (typeCount_le x a)
    have e1 : ∏ i, P₁ (x i) = ∏ a, P₁ a ^ (typeCount x a) :=
      prod_aggr_of_mem_typeClassByCount (fun a ↦ rfl) P₁
    have e2 : ∏ i, P₂ (x i) = ∏ a, P₂ a ^ (typeCount x a) :=
      prod_aggr_of_mem_typeClassByCount (fun a ↦ rfl) P₂
    refine ⟨fun a ↦ ⟨typeCount x a, hlt a⟩, ?_, ?_⟩
    · rw [mem_chernoffErrorCounts_iff]
      refine ⟨typeCount_sum_eq x, ?_⟩
      calc ∏ a, P₁ a ^ (typeCount x a) = ∏ i, P₁ (x i) := e1.symm
        _ ≤ ∏ i, P₂ (x i) := hx
        _ = ∏ a, P₂ a ^ (typeCount x a) := e2
    · intro a; rfl
  · rintro ⟨c, hc, hxc⟩
    rw [mem_chernoffErrorCounts_iff] at hc
    have e1 : ∏ i, P₁ (x i) = ∏ a, P₁ a ^ (c a : ℕ) :=
      prod_aggr_of_mem_typeClassByCount hxc P₁
    have e2 : ∏ i, P₂ (x i) = ∏ a, P₂ a ^ (c a : ℕ) :=
      prod_aggr_of_mem_typeClassByCount hxc P₂
    rw [e1, e2]
    exact hc.2

/-- H4 (W4): the `Measure.pi Q` mass of a finite set of sequences as a finite real sum of
products of singleton masses. (Extracted from the inline block in `typeClass_Qn_le`.) -/
lemma measurePi_toReal_eq_sum (Q : Measure α) [IsProbabilityMeasure Q]
    {n : ℕ} (S : Finset (Fin n → α)) :
    ((Measure.pi (fun _ : Fin n ↦ Q)) (↑S : Set (Fin n → α))).toReal
      = ∑ x ∈ S, ∏ i : Fin n, Q.real {x i} := by
  have h_pi_singleton : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n ↦ Q)).real {x}) = ∏ i : Fin n, Q.real {x i} := by
    intro x
    show ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal = ∏ i : Fin n, Q.real {x i}
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  rw [← MeasureTheory.measureReal_def,
    ← MeasureTheory.sum_measureReal_singleton (μ := Measure.pi (fun _ : Fin n ↦ Q)) S]
  exact Finset.sum_congr rfl fun x _ ↦ h_pi_singleton x

/-- H5: the Bayes error dominates half the `P₁`-mass of any sub-region of the error region. -/
lemma bayesErrorMinPmf_ge_half_sum
    (P₁ P₂ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ)
    (S : Finset (Fin n → α))
    (hS : ∀ x ∈ S, ∏ i, P₁ (x i) ≤ ∏ i, P₂ (x i)) :
    (1 / 2 : ℝ) * ∑ x ∈ S, ∏ i : Fin n, P₁ (x i) ≤ bayesErrorMinPmf P₁ P₂ n := by
  unfold bayesErrorMinPmf
  have hstep1 : ∑ x ∈ S, ∏ i, P₁ (x i)
      = ∑ x ∈ S, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) :=
    Finset.sum_congr rfl fun x hx ↦ (min_eq_left (hS x hx)).symm
  have hstep2 : ∑ x ∈ S, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))
      ≤ ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x _ ↦ Finset.mem_univ x)
      (fun x _ _ ↦ le_min (Finset.prod_nonneg fun i _ ↦ hP₁_nn (x i))
        (Finset.prod_nonneg fun i _ ↦ hP₂_nn (x i)))
  have hcomb : ∑ x ∈ S, ∏ i, P₁ (x i)
      ≤ ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    rw [hstep1]; exact hstep2
  linarith [hcomb]

/-- H6 (rate bridge ii): the Sanov rate `klDivSumForm_ofVec T_λ (Q₁.real ∘ singleton)` equals the
pmf divergence `klDivPmf T_λ P₁`, where `Q₁ = pmfToMeasure P₁`. -/
lemma chernoffMediator_klDivSumForm_eq
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (lam : ℝ) :
    klDivSumForm_ofVec (chernoffMediator P₁ P₂ lam)
        (fun a ↦ (pmfToMeasure P₁ (fun a ↦ (hP₁_pos a).le) hP₁_sum).real {a})
      = klDivPmf (chernoffMediator P₁ P₂ lam) P₁ := by
  have hT_pos : ∀ a, 0 < chernoffMediator P₁ P₂ lam a :=
    fun a ↦ chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a
  have hT_sum : ∑ a, chernoffMediator P₁ P₂ lam a = 1 :=
    chernoffMediator_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam
  rw [klDivSumForm_ofVec, klDivPmf_eq_log_diff_sum hT_sum hP₁_sum hT_pos hP₁_pos]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [pmfToMeasure_real_singleton]

/-- H6 (rate identity): the Sanov rate at the optimal mediator equals the Chernoff information. -/
lemma chernoffMediator_klDivSumForm_eq_chernoffInfo
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io : lam ∈ Set.Ioo (0:ℝ) 1)
    (hinfo : chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam))) :
    klDivSumForm_ofVec (chernoffMediator P₁ P₂ lam)
        (fun a ↦ (pmfToMeasure P₁ (fun a ↦ (hP₁_pos a).le) hP₁_sum).real {a})
      = chernoffInfo P₁ P₂ := by
  rw [chernoffMediator_klDivSumForm_eq P₁ P₂ hP₁_pos hP₂_pos hP₁_sum lam]
  exact (chernoffInfo_eq_mediator_div P₁ P₂ hP₁_pos hP₂_pos hP₁_sum lam
    hlam_min hlam_io hinfo).symm

/-! #### H7 — perturbation membership + degenerate handling -/

/-- The likelihood-ratio membership `∏ P₁^c ≤ ∏ P₂^c` is equivalent to the log-form
`0 ≤ ∑ a, (c a)·log(P₂ a/P₁ a)` (both products positive under full support). -/
lemma prod_pow_le_iff_sum_log
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (c : α → ℕ) :
    (∏ a, P₁ a ^ (c a) ≤ ∏ a, P₂ a ^ (c a))
      ↔ 0 ≤ ∑ a, (c a : ℝ) * Real.log (P₂ a / P₁ a) := by
  have hP1_prod_pos : 0 < ∏ a, P₁ a ^ (c a) :=
    Finset.prod_pos (fun a _ ↦ pow_pos (hP₁_pos a) _)
  have hP2_prod_pos : 0 < ∏ a, P₂ a ^ (c a) :=
    Finset.prod_pos (fun a _ ↦ pow_pos (hP₂_pos a) _)
  rw [← Real.log_le_log_iff hP1_prod_pos hP2_prod_pos,
      Real.log_prod (fun a _ ↦ (pow_pos (hP₁_pos a) (c a)).ne'),
      Real.log_prod (fun a _ ↦ (pow_pos (hP₂_pos a) (c a)).ne')]
  simp_rw [Real.log_pow]
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  have hsum_eq : ∑ a, ((c a : ℝ) * Real.log (P₂ a) - (c a : ℝ) * Real.log (P₁ a))
      = ∑ a, (c a : ℝ) * Real.log (P₂ a / P₁ a) := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Real.log_div (hP₂_pos a).ne' (hP₁_pos a).ne']; ring
  rw [hsum_eq]

/-- Generic rate bridge: for any pmf `p` and a measure `Q` whose singleton masses recover `P₁`,
`klDivSumForm_ofVec p (Q.real ∘ singleton) = klDivPmf p P₁`. -/
lemma klDivSumForm_ofVec_eq_klDivPmf_left
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    (Q : Measure α) (hQ_real : ∀ a, Q.real {a} = P₁ a)
    {p : α → ℝ} (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    klDivSumForm_ofVec p (fun a ↦ Q.real {a}) = klDivPmf p P₁ := by
  rw [klDivSumForm_ofVec, klDivPmf_eq_log_diff_sum_of_Q_pos hp_nn hp_sum hP₁_sum hP₁_pos]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hQ_real]

/-- H7b: the perturbed mediator `T_ε = (1-ε)·T_λ* + ε·P₂` has strictly positive mean
log-likelihood-ratio when `P₁ ≠ P₂` (`0 < klDivPmf P₂ P₁`). -/
lemma chernoffMediator_perturb_llr_pos
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io : lam ∈ Set.Ioo (0:ℝ) 1)
    (h_nondeg : 0 < klDivPmf P₂ P₁)
    {ε : ℝ} (hε0 : 0 < ε) (_hε1 : ε ≤ 1) :
    0 < ∑ a, Qstar_perturb (chernoffMediator P₁ P₂ lam) P₂ ε a * Real.log (P₂ a / P₁ a) := by
  have hbal := chernoffMediator_balance P₁ P₂ hP₁_pos hP₂_pos lam hlam_min hlam_io
  -- `∑ P₂·log(P₂/P₁) = klDivPmf P₂ P₁`.
  have hP₂_div : ∑ a, P₂ a * Real.log (P₂ a / P₁ a) = klDivPmf P₂ P₁ := by
    rw [klDivPmf_eq_log_diff_sum hP₂_sum hP₁_sum hP₂_pos hP₁_pos]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Real.log_div (hP₂_pos a).ne' (hP₁_pos a).ne']
  -- Expand `∑ T_ε·L = (1-ε)·∑ T_λ·L + ε·∑ P₂·L`.
  have h_expand :
      ∑ a, Qstar_perturb (chernoffMediator P₁ P₂ lam) P₂ ε a * Real.log (P₂ a / P₁ a)
        = (1 - ε) * (∑ a, chernoffMediator P₁ P₂ lam a * Real.log (P₂ a / P₁ a))
          + ε * (∑ a, P₂ a * Real.log (P₂ a / P₁ a)) := by
    unfold Qstar_perturb
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  rw [h_expand, hbal, hP₂_div, mul_zero, zero_add]
  exact mul_pos hε0 h_nondeg

/-- H7c: a full-support pmf `T` strictly inside the error half-space
(`0 < ∑ T·log(P₂/P₁)`) has its rounded type eventually in the error region. -/
lemma roundedType_mem_chernoffErrorCounts_eventually
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {T : α → ℝ} (hT_sum : ∑ a, T a = 1) (hT_nn : ∀ a, 0 ≤ T a)
    (h_llr_pos : 0 < ∑ a, T a * Real.log (P₂ a / P₁ a)) :
    ∀ᶠ n : ℕ in atTop, roundedTypeIndex T n ∈ chernoffErrorCounts P₁ P₂ n := by
  -- The empirical mean log-likelihood-ratio `Φ (c_n/n) → Φ T > 0` (continuity + `c_n/n → T`).
  set Φ : (α → ℝ) → ℝ := fun p ↦ ∑ a, p a * Real.log (P₂ a / P₁ a) with hΦ
  have hΦ_cont : Continuous Φ := by
    apply continuous_finsetSum
    intro a _
    exact (continuous_apply a).mul continuous_const
  have h_emp_tendsto :
      Tendsto (fun n : ℕ ↦ Φ (fun a ↦ ((roundedTypeIndex T n a : ℕ) : ℝ) / n)) atTop (𝓝 (Φ T)) :=
    (hΦ_cont.tendsto T).comp (roundedTypeIndex_tendsto_vec T hT_sum hT_nn)
  have h_event_pos :
      ∀ᶠ n : ℕ in atTop, 0 < Φ (fun a ↦ ((roundedTypeIndex T n a : ℕ) : ℝ) / n) :=
    h_emp_tendsto.eventually_const_lt h_llr_pos
  filter_upwards [h_event_pos, eventually_gt_atTop 0] with n hΦn hn_pos
  rw [mem_chernoffErrorCounts_iff]
  refine ⟨roundedTypeIndex_sum T hT_sum hT_nn n hn_pos, ?_⟩
  rw [prod_pow_le_iff_sum_log P₁ P₂ hP₁_pos hP₂_pos]
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_scale :
      ∑ a, ((roundedTypeIndex T n a : ℕ) : ℝ) * Real.log (P₂ a / P₁ a)
        = (n : ℝ) * Φ (fun a ↦ ((roundedTypeIndex T n a : ℕ) : ℝ) / n) := by
    rw [hΦ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    field_simp
  rw [h_scale]
  exact le_of_lt (mul_pos hn_R hΦn)

/-- H8 step: the Bayes error dominates half the `P₁`-measure of the error region. -/
lemma bayesErrorMinPmf_ge_half_measurePi
    (P₁ P₂ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_nn : ∀ a, 0 ≤ P₂ a)
    (Q : Measure α) [IsProbabilityMeasure Q] (hQ_real : ∀ a, Q.real {a} = P₁ a) (n : ℕ) :
    (1 / 2 : ℝ) * ((Measure.pi (fun _ : Fin n ↦ Q))
        (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
          typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal
      ≤ bayesErrorMinPmf P₁ P₂ n := by
  classical
  set R : Set (Fin n → α) := ⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
    typeClassByCount (α := α) (fun a ↦ (c a : ℕ)) with hR
  set S : Finset (Fin n → α) := R.toFinset with hS
  have hSR : (↑S : Set (Fin n → α)) = R := by rw [hS, Set.coe_toFinset]
  have hM_eq : ((Measure.pi (fun _ : Fin n ↦ Q)) R).toReal = ∑ x ∈ S, ∏ i, P₁ (x i) := by
    rw [← hSR, measurePi_toReal_eq_sum Q S]
    exact Finset.sum_congr rfl fun x _ ↦ Finset.prod_congr rfl fun i _ ↦ hQ_real (x i)
  have hS_le : ∀ x ∈ S, ∏ i, P₁ (x i) ≤ ∏ i, P₂ (x i) := by
    intro x hx
    rw [hS, Set.mem_toFinset] at hx
    have hx' : x ∈ {y : Fin n → α | ∏ i, P₁ (y i) ≤ ∏ i, P₂ (y i)} := by
      rw [chernoffErrorRegion_eq_union P₁ P₂ n, ← hR]; exact hx
    exact hx'
  rw [hM_eq]
  exact bayesErrorMinPmf_ge_half_sum P₁ P₂ hP₁_nn hP₂_nn n S hS_le

private lemma chernoffRegion_meas_pos_eventually
    (P₁ P₂ : α → ℝ)
    (Q : Measure α) [IsProbabilityMeasure Q] (hQ_pos : ∀ a, 0 < Q.real {a})
    {T : α → ℝ} (hT_sum : ∑ a, T a = 1) (hT_nn : ∀ a, 0 ≤ T a)
    (h_inE : ∀ᶠ n : ℕ in atTop, roundedTypeIndex T n ∈ chernoffErrorCounts P₁ P₂ n) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      0 < ((Measure.pi (fun _ : Fin n ↦ Q))
          (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
            typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal := by
  filter_upwards [eventually_gt_atTop 0, h_inE] with n hn_pos h_inE_n
  refine ⟨hn_pos, ?_⟩
  obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
    (fun a ↦ (roundedTypeIndex T n a : ℕ))
    (roundedTypeIndex_sum T hT_sum hT_nn n hn_pos)
  have hx_in : x ∈ ⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
      typeClassByCount (α := α) (fun a ↦ (c a : ℕ)) := by
    simp only [Set.mem_iUnion]
    exact ⟨roundedTypeIndex T n, h_inE_n, hx⟩
  have h_sing_pos : (0 : ℝ) < ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal := by
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ ↦ hQ_pos (x i))
  have h_sing_le : ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal
      ≤ ((Measure.pi (fun _ : Fin n ↦ Q))
        (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
          typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal := by
    apply ENNReal.toReal_mono
    · exact measure_ne_top _ _
    · exact measure_mono (Set.singleton_subset_iff.mpr hx_in)
  linarith

private lemma chernoffRegion_rate_isBoundedUnder_below
    (P₁ P₂ : α → ℝ)
    (Q : Measure α) [IsProbabilityMeasure Q] (hQ_pos : ∀ a, 0 < Q.real {a})
    {T : α → ℝ} (hT_sum : ∑ a, T a = 1) (hT_nn : ∀ a, 0 ≤ T a)
    (h_meas_pos : ∀ᶠ n : ℕ in atTop, 0 < n ∧
      0 < ((Measure.pi (fun _ : Fin n ↦ Q))
          (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
            typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal)
    (h_inE : ∀ᶠ n : ℕ in atTop, roundedTypeIndex T n ∈ chernoffErrorCounts P₁ P₂ n) :
    Filter.IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ ↦
      (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n ↦ Q))
            (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
              typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal)) := by
  obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image (s := (Finset.univ : Finset α))
    (f := fun a ↦ Q.real {a}) ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
  set m : ℝ := Q.real {a₀} with hm
  have hm_pos : 0 < m := hQ_pos a₀
  refine ⟨Real.log m, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [h_meas_pos, h_inE] with n h_npos_meas h_inE_n
  obtain ⟨hn_pos, _⟩ := h_npos_meas
  obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
    (fun a ↦ (roundedTypeIndex T n a : ℕ))
    (roundedTypeIndex_sum T hT_sum hT_nn n hn_pos)
  have hx_in : x ∈ ⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
      typeClassByCount (α := α) (fun a ↦ (c a : ℕ)) := by
    simp only [Set.mem_iUnion]
    exact ⟨roundedTypeIndex T n, h_inE_n, hx⟩
  have h_sing_ge : m ^ n ≤ ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal := by
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    calc m ^ n = ∏ _i : Fin n, m := by rw [Finset.prod_const]; simp
      _ ≤ ∏ i : Fin n, Q.real {x i} :=
        Finset.prod_le_prod (fun i _ ↦ hm_pos.le)
          (fun i _ ↦ ha₀ (x i) (Finset.mem_univ _))
  have h_sing_le : ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal
      ≤ ((Measure.pi (fun _ : Fin n ↦ Q))
        (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
          typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal := by
    apply ENNReal.toReal_mono
    · exact measure_ne_top _ _
    · exact measure_mono (Set.singleton_subset_iff.mpr hx_in)
  have h_union_ge : m ^ n ≤ ((Measure.pi (fun _ : Fin n ↦ Q))
      (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
        typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal :=
    le_trans h_sing_ge h_sing_le
  have h_pow_pos : (0 : ℝ) < m ^ n := pow_pos hm_pos _
  have h_log_pow_le := Real.log_le_log h_pow_pos h_union_ge
  rw [Real.log_pow] at h_log_pow_le
  have h_n_inv_pos : 0 < 1 / (n : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left h_log_pow_le h_n_inv_pos.le
  rwa [show (1 / (n : ℝ)) * ((n : ℝ) * Real.log m) = Real.log m by field_simp] at h

/-- **Chernoff converse** (Cover–Thomas Theorem 11.9.1, converse half): the optimal Bayes
error exponent cannot exceed the Chernoff information. Proved on the interior `0 < λ* < 1`
(the overlapping-support / non-degenerate case; `hlam_io` is a non-degeneracy precondition,
not load-bearing). -/
theorem chernoff_converse
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io : lam ∈ Set.Ioo (0:ℝ) 1)
    (hinfo : chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam))) :
    Filter.limsup (fun n : ℕ ↦ -((1:ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
      ≤ chernoffInfo P₁ P₂ := by
  classical
  -- The measure lift `μ₁ = pmfToMeasure P₁` and its singleton masses.
  set μ₁ := pmfToMeasure P₁ (fun a ↦ (hP₁_pos a).le) hP₁_sum with hμ₁
  haveI : IsProbabilityMeasure μ₁ := by rw [hμ₁]; infer_instance
  have hμ₁_real : ∀ a, μ₁.real {a} = P₁ a := fun a ↦ by
    rw [hμ₁]; exact pmfToMeasure_real_singleton P₁ _ _ a
  have hμ₁_pos : ∀ a, 0 < μ₁.real {a} := fun a ↦ by rw [hμ₁_real]; exact hP₁_pos a
  -- The Sanov rate sequence `f` and the target sequence `b`.
  set f : ℕ → ℝ := fun n ↦ (1 / (n : ℝ)) * Real.log
    (((Measure.pi (fun _ : Fin n ↦ μ₁))
      (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
        typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal) with hf
  set b : ℕ → ℝ := fun n ↦ -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n) with hb
  have hmed_sum := chernoffMediator_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam
  have hmed_nn : ∀ a, 0 ≤ chernoffMediator P₁ P₂ lam a :=
    fun a ↦ (chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a).le
  -- ===== Shared limsup-flip tail (witness pmf `T₀` + the Sanov liminf bound). =====
  have key : ∀ (T₀ : α → ℝ), (∑ a, T₀ a = 1) → (∀ a, 0 ≤ T₀ a) →
      (∀ᶠ n : ℕ in atTop, roundedTypeIndex T₀ n ∈ chernoffErrorCounts P₁ P₂ n) →
      (-chernoffInfo P₁ P₂ ≤ Filter.liminf f atTop) →
      Filter.limsup b atTop ≤ chernoffInfo P₁ P₂ := by
    intro T₀ hT₀_sum hT₀_nn h_inE₀ h_liminf
    have h_meas_pos := chernoffRegion_meas_pos_eventually P₁ P₂ μ₁ hμ₁_pos hT₀_sum hT₀_nn h_inE₀
    have h_bdd_below_f : Filter.IsBoundedUnder (· ≥ ·) atTop f := by
      rw [hf]
      exact chernoffRegion_rate_isBoundedUnder_below P₁ P₂ μ₁ hμ₁_pos hT₀_sum hT₀_nn
        h_meas_pos h_inE₀
    -- `b` bounded below by `chernoffInfo` ⇒ cobounded under `(· ≤ ·)`.
    have h_bdd_below_b : Filter.IsBoundedUnder (· ≥ ·) atTop b := by
      refine ⟨chernoffInfo P₁ P₂, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [chernoff_rate_ge_chernoffInfo_eventually P₁ P₂ hP₁_pos hP₂_pos,
        eventually_gt_atTop 0] with n hn hn0
      have hn_R : (0 : ℝ) < n := by exact_mod_cast hn0
      have h2 : 0 < Real.log 2 / n := div_pos (Real.log_pos (by norm_num)) hn_R
      change chernoffInfo P₁ P₂ ≤ -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
      linarith [hn]
    have h_cobdd_b : Filter.IsCoboundedUnder (· ≤ ·) atTop b :=
      h_bdd_below_b.isCoboundedUnder_flip
    -- Eventually `b n ≤ (1/n)·log 2 - f n` (from `bayes ≥ (1/2)·μ₁ⁿ(region)`).
    have h_b_le_g : ∀ᶠ n : ℕ in atTop, b n ≤ (1 / (n : ℝ)) * Real.log 2 - f n := by
      filter_upwards [h_meas_pos] with n h_np
      obtain ⟨hn_pos, hM_pos⟩ := h_np
      have h_half_M_le := bayesErrorMinPmf_ge_half_measurePi P₁ P₂
        (fun a ↦ (hP₁_pos a).le) (fun a ↦ (hP₂_pos a).le) μ₁ hμ₁_real n
      set M : ℝ := ((Measure.pi (fun _ : Fin n ↦ μ₁))
        (⋃ c ∈ chernoffErrorCounts P₁ P₂ n,
          typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal with hM
      have h_half_pos : (0 : ℝ) < (1 / 2 : ℝ) * M := mul_pos (by norm_num) hM_pos
      have h_log_le : Real.log ((1 / 2 : ℝ) * M) ≤ Real.log (bayesErrorMinPmf P₁ P₂ n) :=
        Real.log_le_log h_half_pos h_half_M_le
      have h_log_expand : Real.log ((1 / 2 : ℝ) * M) = -Real.log 2 + Real.log M := by
        rw [Real.log_mul (by norm_num) hM_pos.ne',
          show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [h_log_expand] at h_log_le
      have h_neg_inv : -((1 : ℝ) / n) ≤ 0 := by
        have : (0 : ℝ) ≤ 1 / n := by positivity
        linarith
      have h_mul := mul_le_mul_of_nonpos_left h_log_le h_neg_inv
      change -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
          ≤ (1 / (n : ℝ)) * Real.log 2 - (1 / (n : ℝ)) * Real.log M
      calc -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
          ≤ -((1 : ℝ) / n) * (-Real.log 2 + Real.log M) := h_mul
        _ = (1 / (n : ℝ)) * Real.log 2 - (1 / (n : ℝ)) * Real.log M := by ring
    -- Contradiction-based limsup bound.
    by_contra h_lt
    rw [not_le] at h_lt
    set δ : ℝ := (Filter.limsup b atTop - chernoffInfo P₁ P₂) / 2 with hδ
    have hδ_pos : 0 < δ := by rw [hδ]; linarith
    have h_f_gt : ∀ᶠ n : ℕ in atTop, -chernoffInfo P₁ P₂ - δ / 2 < f n :=
      Filter.eventually_lt_of_lt_liminf (by linarith [h_liminf]) h_bdd_below_f
    have h_c_lt : ∀ᶠ n : ℕ in atTop, (1 / (n : ℝ)) * Real.log 2 < δ / 2 := by
      have h_tendsto : Tendsto (fun n : ℕ ↦ (1 / (n : ℝ)) * Real.log 2) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (Real.log 2)
      exact h_tendsto.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < δ / 2))
    have h_event_bδ : ∀ᶠ n : ℕ in atTop, b n ≤ chernoffInfo P₁ P₂ + δ := by
      filter_upwards [h_b_le_g, h_f_gt, h_c_lt] with n h1 h2 h3
      linarith
    have h_ub : Filter.limsup b atTop ≤ chernoffInfo P₁ P₂ + δ :=
      Filter.limsup_le_of_le h_cobdd_b h_event_bδ
    rw [hδ] at h_ub
    linarith
  -- ===== Case on degeneracy of `klDivPmf P₂ P₁`. =====
  rcases (klDivPmf_nonneg P₂ P₁ (fun a ↦ (hP₂_pos a).le) (fun a ↦ (hP₁_pos a).le)).eq_or_lt
    with h0 | hpos
  · -- Degenerate `P₂ = P₁`: membership is `le_refl`, witness = mediator.
    have hPeq : P₂ = P₁ :=
      (klDivPmf_eq_zero_iff_pmf ⟨fun a ↦ (hP₂_pos a).le, hP₂_sum⟩
        ⟨fun a ↦ (hP₁_pos a).le, hP₁_sum⟩ hP₁_pos).mp h0.symm
    have h_inE₀ : ∀ᶠ n : ℕ in atTop,
        roundedTypeIndex (chernoffMediator P₁ P₂ lam) n ∈ chernoffErrorCounts P₁ P₂ n := by
      filter_upwards [eventually_gt_atTop 0] with n hn_pos
      rw [mem_chernoffErrorCounts_iff]
      exact ⟨roundedTypeIndex_sum _ hmed_sum hmed_nn n hn_pos, by rw [hPeq]⟩
    have h_liminf : -chernoffInfo P₁ P₂ ≤ Filter.liminf f atTop := by
      have h_lb := sanov_ldp_lower_bound_pointwise μ₁ hμ₁_pos (chernoffMediator P₁ P₂ lam)
        hmed_sum (fun a ↦ chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a)
        (fun n ↦ chernoffErrorCounts P₁ P₂ n) h_inE₀
      have h_rate : klDivSumForm_ofVec (chernoffMediator P₁ P₂ lam)
          (fun a ↦ μ₁.real {a}) = chernoffInfo P₁ P₂ := by
        rw [klDivSumForm_ofVec_eq_klDivPmf_left P₁ hP₁_pos hP₁_sum μ₁ hμ₁_real hmed_nn hmed_sum]
        exact (chernoffInfo_eq_mediator_div P₁ P₂ hP₁_pos hP₂_pos hP₁_sum lam
          hlam_min hlam_io hinfo).symm
      rw [h_rate] at h_lb
      exact h_lb
    exact key (chernoffMediator P₁ P₂ lam) hmed_sum hmed_nn h_inE₀ h_liminf
  · -- Non-degenerate `0 < klDivPmf P₂ P₁`: perturb toward `P₂`, then `ε → 0`.
    set T₀ : α → ℝ := Qstar_perturb (chernoffMediator P₁ P₂ lam) P₂ (1 / 2) with hT₀
    have hT₀_sum : ∑ a, T₀ a = 1 := Qstar_perturb_sum hmed_sum hP₂_sum (1 / 2)
    have hT₀_nn : ∀ a, 0 ≤ T₀ a :=
      Qstar_perturb_nonneg hmed_nn (fun a ↦ (hP₂_pos a).le) (by norm_num) (by norm_num)
    have hT₀_llr : 0 < ∑ a, T₀ a * Real.log (P₂ a / P₁ a) :=
      chernoffMediator_perturb_llr_pos P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum lam
        hlam_min hlam_io hpos (by norm_num) (by norm_num)
    have h_inE₀ : ∀ᶠ n : ℕ in atTop, roundedTypeIndex T₀ n ∈ chernoffErrorCounts P₁ P₂ n :=
      roundedType_mem_chernoffErrorCounts_eventually P₁ P₂ hP₁_pos hP₂_pos
        hT₀_sum hT₀_nn hT₀_llr
    have h_liminf : -chernoffInfo P₁ P₂ ≤ Filter.liminf f atTop := by
      -- For every `ε ∈ (0,1)`: `-klDivPmf T_ε P₁ ≤ liminf f`.
      have h_event : ∀ᶠ ε : ℝ in 𝓝[>] 0,
          -klDivPmf (Qstar_perturb (chernoffMediator P₁ P₂ lam) P₂ ε) P₁
            ≤ Filter.liminf f atTop := by
        have h_lt1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
          eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num))
        have h_pos : ∀ᶠ ε : ℝ in 𝓝[>] 0, (0 : ℝ) < ε :=
          eventually_mem_nhdsWithin.mono (fun ε hε ↦ hε)
        filter_upwards [h_lt1, h_pos] with ε hε1 hε0
        set Pε := Qstar_perturb (chernoffMediator P₁ P₂ lam) P₂ ε with hPε
        have hPε_sum : ∑ a, Pε a = 1 := Qstar_perturb_sum hmed_sum hP₂_sum ε
        have hPε_full : ∀ a, 0 < Pε a := by
          intro a
          rw [hPε]; unfold Qstar_perturb
          have h1 : 0 ≤ (1 - ε) * chernoffMediator P₁ P₂ lam a :=
            mul_nonneg (by linarith) (hmed_nn a)
          have h2 : 0 < ε * P₂ a := mul_pos hε0 (hP₂_pos a)
          linarith
        have hPε_nn : ∀ a, 0 ≤ Pε a := fun a ↦ (hPε_full a).le
        have hPε_llr : 0 < ∑ a, Pε a * Real.log (P₂ a / P₁ a) :=
          chernoffMediator_perturb_llr_pos P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum lam
            hlam_min hlam_io hpos hε0 hε1.le
        have h_inE : ∀ᶠ n : ℕ in atTop, roundedTypeIndex Pε n ∈ chernoffErrorCounts P₁ P₂ n :=
          roundedType_mem_chernoffErrorCounts_eventually P₁ P₂ hP₁_pos hP₂_pos
            hPε_sum hPε_nn hPε_llr
        have h_lb := sanov_ldp_lower_bound_pointwise μ₁ hμ₁_pos Pε hPε_sum hPε_full
          (fun n ↦ chernoffErrorCounts P₁ P₂ n) h_inE
        rw [klDivSumForm_ofVec_eq_klDivPmf_left P₁ hP₁_pos hP₁_sum μ₁ hμ₁_real hPε_nn hPε_sum]
          at h_lb
        exact h_lb
      -- `ε → 0`: `-klDivPmf T_ε P₁ → -chernoffInfo`.
      have h_tendsto : Tendsto
          (fun ε : ℝ ↦ -klDivPmf (Qstar_perturb (chernoffMediator P₁ P₂ lam) P₂ ε) P₁)
          (𝓝[>] 0) (𝓝 (-chernoffInfo P₁ P₂)) := by
        rw [chernoffInfo_eq_mediator_div P₁ P₂ hP₁_pos hP₂_pos hP₁_sum lam hlam_min hlam_io hinfo]
        exact (klDivPmf_perturb_tendsto P₂ P₁ hP₁_pos
          (Qstar := chernoffMediator P₁ P₂ lam)).neg
      exact le_of_tendsto h_tendsto h_event
    exact key T₀ hT₀_sum hT₀_nn h_inE₀ h_liminf

end PhaseB

end InformationTheory.Shannon.Chernoff
