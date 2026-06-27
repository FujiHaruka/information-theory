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
import InformationTheory.Shannon.KLDivContinuous
import InformationTheory.Shannon.Hoeffding.Tradeoff
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

end PhaseB

end InformationTheory.Shannon.Chernoff
