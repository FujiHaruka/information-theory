import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.CsiszarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents

/-!
# Chernoff information and the Hoeffding tradeoff exponent

The Chernoff exponent `C(P₁, P₂)` and the Hoeffding tradeoff exponent `E₂(α)`
(Cover–Thomas 11.7 / 11.9) for finite-alphabet pmfs `P₁, P₂ : α → ℝ`, together with the
convexity of `λ ↦ log Z(λ)` and the achievability side of the Chernoff bound on the Bayes
error of an `n`-sample binary hypothesis test.

## Main definitions

* `chernoffZSum P₁ P₂ lam` — the Chernoff partition function `Z(λ) := ∑ a, P₁(a)^(1-λ) · P₂(a)^λ`.
* `chernoffInfo P₁ P₂` — the Chernoff information `-sInf ((log ∘ Z) '' Icc 0 1)`.
* `chernoffMediator P₁ P₂ lam` — the tilted mediator pmf `P₁(a)^(1-λ) · P₂(a)^λ / Z(λ)`.
* `hoeffdingE2 P₁ P₂ alpha` — the Hoeffding tradeoff exponent at Type I level `alpha`.
* `hoeffdingConstraintSet P₁ alpha` — the constraint set `{Q ∈ stdSimplex | klDivPmf Q P₁ ≤ alpha}`.
* `bayesErrorMinPmf P₁ P₂ n` — the optimal `n`-sample Bayes error with equal priors.

## Main statements

* `chernoffInfo_attained`, `chernoffInfo_nonneg` — the Chernoff information is attained and
  nonnegative.
* `convexOn_chernoffLogZ` — `λ ↦ log Z(λ)` is convex on `Icc 0 1`.
* `hoeffdingE2_attained`, `hoeffdingE2_nonneg`, `hoeffdingE2_unique` — existence, nonnegativity,
  and uniqueness of the Hoeffding minimizer.
* `bayesErrorMinPmf_le_half_Z_pow` — the Chernoff bound `bayesErrorMinPmf ≤ (1/2) · Z(λ)^n`.
* `chernoff_lemma_achievability` — the achievability rate `liminf ≥ chernoffInfo`.

## Implementation notes

Everything is stated in finite-alphabet pmf form (`α → ℝ`) so that `CsiszarProjection.klDivPmf`
can be reused directly. `chernoffInfo` and `hoeffdingE2` are stated as `sInf` over an image of a
compact set, so attainment follows from `IsCompact.exists_sInf_image_eq`. The convexity of
`log Z` is obtained from the multiplicative Hölder bound `Z(αλ₁ + βλ₂) ≤ Z(λ₁)^α · Z(λ₂)^β`.
-/

namespace InformationTheory.Shannon.Chernoff

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter
open InformationTheory.Shannon.CsiszarProjection
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Chernoff exponent: definition and basic properties -/

/-- The Chernoff partition function `Z(λ) := ∑_a P₁(a)^(1-λ) · P₂(a)^λ` (Cover–Thomas 11.9.1). -/
noncomputable def chernoffZSum (P₁ P₂ : α → ℝ) (lam : ℝ) : ℝ :=
  ∑ a : α, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam

/-- The Chernoff information `C(P₁, P₂) := -min_{λ ∈ [0,1]} log Z(λ)`, stated as `-sInf` of the
image; `chernoffInfo_attained` shows the minimum is realized. -/
noncomputable def chernoffInfo (P₁ P₂ : α → ℝ) : ℝ :=
  -(sInf ((fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1))

/-! ### Endpoint values `Z(0) = Z(1) = 1` -/

omit [DecidableEq α] in
/-- `Z(0) = ∑ P₁(a) = 1` for pmf P₁. -/
lemma chernoffZSum_lam_zero
    (P₁ P₂ : α → ℝ) (hP₁_sum : ∑ a, P₁ a = 1) (_hP₂_nn : ∀ a, 0 ≤ P₂ a) :
    chernoffZSum P₁ P₂ 0 = 1 := by
  unfold chernoffZSum
  -- (P₁ a) ^ (1 - 0) * (P₂ a) ^ 0 = P₁ a * 1 = P₁ a
  have h_term : ∀ a, (P₁ a) ^ (1 - (0:ℝ)) * (P₂ a) ^ (0:ℝ) = P₁ a := by
    intro a
    rw [Real.rpow_zero, mul_one]
    rw [sub_zero, Real.rpow_one]
  simp_rw [h_term]
  exact hP₁_sum

omit [DecidableEq α] in
/-- `Z(1) = ∑ P₂(a) = 1` for pmf P₂. -/
lemma chernoffZSum_lam_one
    (P₁ P₂ : α → ℝ) (_hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_sum : ∑ a, P₂ a = 1) :
    chernoffZSum P₁ P₂ 1 = 1 := by
  unfold chernoffZSum
  have h_term : ∀ a, (P₁ a) ^ (1 - (1:ℝ)) * (P₂ a) ^ (1:ℝ) = P₂ a := by
    intro a
    rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_one]
  simp_rw [h_term]
  exact hP₂_sum

/-! ### Strict positivity -/

omit [DecidableEq α] in
/-- Each summand `(P₁ a)^(1-λ) · (P₂ a)^λ` is strictly positive under full support. -/
lemma chernoffZSum_term_pos
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    0 < (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam :=
  mul_pos (Real.rpow_pos_of_pos (hP₁_pos a) _) (Real.rpow_pos_of_pos (hP₂_pos a) _)

omit [DecidableEq α] in
/-- `Z(λ) > 0` under full support (any `λ ∈ ℝ`). -/
lemma chernoffZSum_pos
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (lam : ℝ) :
    0 < chernoffZSum P₁ P₂ lam := by
  unfold chernoffZSum
  apply Finset.sum_pos
  · intro a _
    exact chernoffZSum_term_pos P₁ P₂ hP₁_pos hP₂_pos lam a
  · exact Finset.univ_nonempty

/-! ### Continuity -/

omit [DecidableEq α] in
/-- `λ ↦ Z(λ)` is continuous on `ℝ`. -/
lemma chernoffZSum_continuous
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Continuous (fun lam : ℝ ↦ chernoffZSum P₁ P₂ lam) := by
  unfold chernoffZSum
  refine continuous_finsetSum _ fun a _ ↦ ?_
  -- Each term: (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam.
  have h1 : Continuous (fun lam : ℝ ↦ (P₁ a) ^ (1 - lam)) := by
    have h_base : Continuous (fun lam : ℝ ↦ (1 - lam)) := continuous_const.sub continuous_id
    exact (Real.continuous_const_rpow (hP₁_pos a).ne').comp h_base
  have h2 : Continuous (fun lam : ℝ ↦ (P₂ a) ^ lam) :=
    Real.continuous_const_rpow (hP₂_pos a).ne'
  exact h1.mul h2

omit [DecidableEq α] in
/-- `λ ↦ log Z(λ)` is continuous on `ℝ` (under full-support strict positivity of `Z`). -/
lemma chernoffLogZ_continuous
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Continuous (fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) := by
  -- Z(λ) > 0 always (full support); use Real.continuousAt_log on each point.
  have hZ_cont : Continuous (fun lam : ℝ ↦ chernoffZSum P₁ P₂ lam) :=
    chernoffZSum_continuous P₁ P₂ hP₁_pos hP₂_pos
  refine continuous_iff_continuousAt.mpr fun lam ↦ ?_
  have h_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  exact (Real.continuousAt_log h_pos.ne').comp hZ_cont.continuousAt

/-! ### Attainment and nonnegativity of `chernoffInfo` -/

omit [DecidableEq α] in
/-- Chernoff information is attained: `∃ λ* ∈ Icc 0 1, chernoffInfo = -log Z(λ*)`. -/
@[entry_point]
theorem chernoffInfo_attained
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    ∃ lam ∈ Set.Icc (0:ℝ) 1, chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam)) := by
  -- `IsCompact.exists_sInf_image_eq` on the compact `Icc 0 1` for the continuous `log ∘ Z`.
  have h_compact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have h_ne : (Set.Icc (0:ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  have h_cont : Continuous (fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) :=
    chernoffLogZ_continuous P₁ P₂ hP₁_pos hP₂_pos
  obtain ⟨lam, hlam_mem, h_sInf_eq⟩ :=
    h_compact.exists_sInf_image_eq h_ne h_cont.continuousOn
  refine ⟨lam, hlam_mem, ?_⟩
  unfold chernoffInfo
  rw [h_sInf_eq]

omit [DecidableEq α] in
/-- `chernoffInfo P₁ P₂ ≥ 0`.

`chernoffInfo := -sInf (log Z '' Icc 0 1)`. At `λ = 0`, `log Z(0) = log 1 = 0`, so
`sInf (log Z '' Icc 0 1) ≤ 0` (compact + continuous gives `sInf` attained, and `0` is in
the image). Hence `chernoffInfo ≥ 0`. -/
@[entry_point]
theorem chernoffInfo_nonneg
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (_hP₂_sum : ∑ a, P₂ a = 1) :
    0 ≤ chernoffInfo P₁ P₂ := by
  -- 0 ∈ Icc 0 1 ⇒ log Z(0) = log 1 = 0 ∈ image.
  unfold chernoffInfo
  -- chernoffInfo = -sInf; want 0 ≤ -sInf ⇔ sInf ≤ 0.
  rw [neg_nonneg]
  -- Image is bounded below (compact ⇒ image compact ⇒ bdd below).
  have h_compact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have h_cont : Continuous (fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) :=
    chernoffLogZ_continuous P₁ P₂ hP₁_pos hP₂_pos
  have h_img_compact : IsCompact
      ((fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1) :=
    h_compact.image_of_continuousOn h_cont.continuousOn
  have h_bdd : BddBelow
      ((fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1) :=
    h_img_compact.bddBelow
  -- 0 ∈ Icc, so `log Z(0)` is in the image.
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have h_logZ0_in_img :
      Real.log (chernoffZSum P₁ P₂ 0)
        ∈ (fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1 :=
    ⟨0, h0_mem, rfl⟩
  have h_Z0 : chernoffZSum P₁ P₂ 0 = 1 :=
    chernoffZSum_lam_zero P₁ P₂ hP₁_sum (fun a ↦ (hP₂_pos a).le)
  have h_logZ0 : Real.log (chernoffZSum P₁ P₂ 0) = 0 := by
    rw [h_Z0, Real.log_one]
  -- sInf image ≤ log Z(0) = 0.
  calc sInf ((fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1)
      ≤ Real.log (chernoffZSum P₁ P₂ 0) := csInf_le h_bdd h_logZ0_in_img
    _ = 0 := h_logZ0

/-! ### Symmetry `Z_{P₁,P₂}(λ) = Z_{P₂,P₁}(1 - λ)` -/

omit [DecidableEq α] in
/-- Symmetry of `chernoffZSum` under `λ ↔ 1 - λ`: `Z_{P₁,P₂}(λ) = Z_{P₂,P₁}(1 - λ)`. -/
@[entry_point]
lemma chernoffZSum_swap (P₁ P₂ : α → ℝ) (lam : ℝ) :
    chernoffZSum P₁ P₂ lam = chernoffZSum P₂ P₁ (1 - lam) := by
  unfold chernoffZSum
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  -- (P₁ a)^(1-λ) * (P₂ a)^λ vs (P₂ a)^(1-(1-λ)) * (P₁ a)^(1-λ) = (P₂ a)^λ * (P₁ a)^(1-λ)
  rw [show (1 : ℝ) - (1 - lam) = lam by ring]
  ring

/-! ### Hoeffding tradeoff exponent -/

omit [DecidableEq α] in
/-- `klDivPmf P P = 0`: the Kullback–Leibler divergence of a positive pmf with itself is zero. -/
lemma klDivPmf_self_eq_zero
    (P : α → ℝ) (hP_pos : ∀ a, 0 < P a) :
    klDivPmf P P = 0 := by
  unfold klDivPmf
  refine Finset.sum_eq_zero (fun a _ ↦ ?_)
  -- P a * klFun (P a / P a) = P a * klFun 1 = P a * 0 = 0
  have h_div : P a / P a = 1 := div_self (hP_pos a).ne'
  rw [h_div, InformationTheory.klFun_one, mul_zero]

/-- Hoeffding tradeoff exponent at Type I level `alpha`:
`E₂(α) := min { klDivPmf Q P₂ | Q ∈ stdSimplex ∧ klDivPmf Q P₁ ≤ α }`. -/
noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ :=
  sInf ((fun Q : α → ℝ ↦ klDivPmf Q P₂) ''
    {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha})

/-- The Hoeffding constraint set
`K := {Q ∈ stdSimplex | klDivPmf Q P₁ ≤ α}`. -/
def hoeffdingConstraintSet (P₁ : α → ℝ) (alpha : ℝ) : Set (α → ℝ) :=
  {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}

omit [DecidableEq α] in
/-- The Hoeffding constraint set is non-empty when `α ≥ 0` and `P₁` is a positive pmf:
`P₁` itself satisfies `klDivPmf P₁ P₁ = 0 ≤ α`. -/
lemma hoeffdingConstraintSet_nonempty
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    (hoeffdingConstraintSet P₁ alpha).Nonempty := by
  refine ⟨P₁, ?_, ?_⟩
  · refine ⟨fun a ↦ (hP₁_pos a).le, hP₁_sum⟩
  · rw [klDivPmf_self_eq_zero P₁ hP₁_pos]
    exact h_alpha_nn

omit [DecidableEq α] in
/-- The Hoeffding constraint set is a subset of the simplex. -/
lemma hoeffdingConstraintSet_subset_stdSimplex
    (P₁ : α → ℝ) (alpha : ℝ) :
    hoeffdingConstraintSet P₁ alpha ⊆ stdSimplex ℝ α :=
  fun _ hQ ↦ hQ.1

omit [DecidableEq α] in
/-- The Hoeffding constraint set is closed (intersection of the closed simplex with
the closed sublevel set of the continuous function `Q ↦ klDivPmf Q P₁`). -/
lemma hoeffdingConstraintSet_isClosed
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha : ℝ) :
    IsClosed (hoeffdingConstraintSet P₁ alpha) := by
  classical
  -- K = stdSimplex ∩ {Q | klDivPmf Q P₁ ≤ alpha}.
  have h_simplex : IsClosed (stdSimplex ℝ α) := isClosed_stdSimplex ℝ α
  have h_cont : Continuous (fun Q : α → ℝ ↦ klDivPmf Q P₁) :=
    continuous_klDivPmf_left P₁ hP₁_pos
  have h_sublevel : IsClosed {Q : α → ℝ | klDivPmf Q P₁ ≤ alpha} :=
    isClosed_le h_cont continuous_const
  exact h_simplex.inter h_sublevel

omit [DecidableEq α] in
/-- The Hoeffding infimum is attained: there exists `Q* ∈ K` with
`hoeffdingE2 P₁ P₂ alpha = klDivPmf Q* P₂`. -/
@[entry_point]
theorem hoeffdingE2_attained
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha,
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ := by
  classical
  -- K = hoeffdingConstraintSet P₁ alpha: closed (continuous KL preimage ∩ closed simplex),
  -- nonempty (contains P₁), and a subset of the compact simplex.
  have h_closed : IsClosed (hoeffdingConstraintSet P₁ alpha) :=
    hoeffdingConstraintSet_isClosed P₁ hP₁_pos alpha
  have h_sub : hoeffdingConstraintSet P₁ alpha ⊆ stdSimplex ℝ α :=
    hoeffdingConstraintSet_subset_stdSimplex P₁ alpha
  have h_compact : IsCompact (hoeffdingConstraintSet P₁ alpha) :=
    isCompact_of_subset_stdSimplex h_closed h_sub
  have h_ne : (hoeffdingConstraintSet P₁ alpha).Nonempty :=
    hoeffdingConstraintSet_nonempty P₁ hP₁_pos hP₁_sum alpha h_alpha_nn
  have h_cont : Continuous (fun Q : α → ℝ ↦ klDivPmf Q P₂) :=
    continuous_klDivPmf_left P₂ hP₂_pos
  obtain ⟨Qstar, hQs_mem, h_sInf_eq⟩ :=
    h_compact.exists_sInf_image_eq h_ne h_cont.continuousOn
  refine ⟨Qstar, hQs_mem, ?_⟩
  unfold hoeffdingE2
  exact h_sInf_eq

omit [DecidableEq α] in
/-- `hoeffdingE2 P₁ P₂ alpha ≥ 0`.

`hoeffdingE2 := sInf (klDivPmf · P₂ '' K)`. Since `K` is nonempty and every element in
the image is `≥ 0` (`klDivPmf_nonneg`), the infimum is `≥ 0` by `le_csInf`. -/
@[entry_point]
theorem hoeffdingE2_nonneg
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    0 ≤ hoeffdingE2 P₁ P₂ alpha := by
  classical
  unfold hoeffdingE2
  have h_ne : (hoeffdingConstraintSet P₁ alpha).Nonempty :=
    hoeffdingConstraintSet_nonempty P₁ hP₁_pos hP₁_sum alpha h_alpha_nn
  have h_img_ne :
      ((fun Q : α → ℝ ↦ klDivPmf Q P₂) ''
        {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}).Nonempty :=
    h_ne.image _
  refine le_csInf h_img_ne ?_
  rintro y ⟨Q, hQ, rfl⟩
  have hQ_nn : ∀ a, 0 ≤ Q a := hQ.1.1
  have hP₂_nn : ∀ a, 0 ≤ P₂ a := fun a ↦ (hP₂_pos a).le
  exact klDivPmf_nonneg Q P₂ hQ_nn hP₂_nn

/-! ### Convexity of `log Z(λ)` via Hölder

The convexity of `λ ↦ log Z(λ)` on `Icc 0 1` (Cover–Thomas 11.9.1). From Hölder's inequality one
obtains the multiplicative form `Z(αλ₁ + βλ₂) ≤ Z(λ₁)^α · Z(λ₂)^β`; taking logarithms gives the
convexity. The endpoints `α = 0` and `α = 1` are handled separately, since they fall outside the
`1 < p` requirement of `Real.HolderConjugate`. -/

omit [DecidableEq α] in
/-- Hölder multiplicative form for the Chernoff partition function:
`Z(αλ₁ + βλ₂) ≤ Z(λ₁)^α · Z(λ₂)^β` for `α, β ∈ (0, 1)`, `α + β = 1`.

This is the engine of `convexOn_chernoffLogZ`. Stated under full-support `P₁, P₂ > 0`
to avoid `0^x` corner cases; this is the only setting we use it. -/
lemma chernoffZSum_holder_mul
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {lam₁ lam₂ a b : ℝ}
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hab : a + b = 1) :
    chernoffZSum P₁ P₂ (a * lam₁ + b * lam₂)
      ≤ (chernoffZSum P₁ P₂ lam₁) ^ a * (chernoffZSum P₁ P₂ lam₂) ^ b := by
  -- Setup: f_i := (P₁ i)^((1-λ₁)·a) * (P₂ i)^(λ₁·a),
  --        g_i := (P₁ i)^((1-λ₂)·b) * (P₂ i)^(λ₂·b).
  -- Then  f_i * g_i = (P₁ i)^(1 - (a λ₁ + b λ₂)) * (P₂ i)^(a λ₁ + b λ₂)
  -- with conjugate exponents (1/a, 1/b) (since a + b = 1).
  set f : α → ℝ := fun i ↦ (P₁ i) ^ ((1 - lam₁) * a) * (P₂ i) ^ (lam₁ * a) with hf_def
  set g : α → ℝ := fun i ↦ (P₁ i) ^ ((1 - lam₂) * b) * (P₂ i) ^ (lam₂ * b) with hg_def
  have hP₁_nn : ∀ a, 0 ≤ P₁ a := fun a ↦ (hP₁_pos a).le
  have hP₂_nn : ∀ a, 0 ≤ P₂ a := fun a ↦ (hP₂_pos a).le
  -- Hölder exponents.
  have ha_lt_one : a < 1 := by linarith
  have hb_eq : b = 1 - a := by linarith
  -- `HolderConjugate (1/a) (1/b)` via `Real.HolderConjugate.inv_one_sub_inv`.
  have hConj : (a⁻¹).HolderConjugate (b⁻¹) := by
    have h := Real.HolderConjugate.inv_one_sub_inv ha_pos ha_lt_one
    rw [show b⁻¹ = (1 - a)⁻¹ from by rw [hb_eq]]
    exact h
  have hConj_1div : Real.HolderConjugate (1 / a) (1 / b) := by
    rw [show (1 / a) = a⁻¹ from one_div a, show (1 / b) = b⁻¹ from one_div b]
    exact hConj
  -- Nonneg of f, g.
  have hf_nn : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ f i := by
    intro i _
    exact mul_nonneg (Real.rpow_nonneg (hP₁_nn i) _) (Real.rpow_nonneg (hP₂_nn i) _)
  have hg_nn : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ g i := by
    intro i _
    exact mul_nonneg (Real.rpow_nonneg (hP₁_nn i) _) (Real.rpow_nonneg (hP₂_nn i) _)
  -- Hölder: ∑ f i * g i ≤ (∑ f i ^ (1/a)) ^ a · (∑ g i ^ (1/b)) ^ b.
  have hHolder :
      ∑ i, f i * g i
        ≤ (∑ i, (f i) ^ (1 / a)) ^ (1 / (1 / a)) *
          (∑ i, (g i) ^ (1 / b)) ^ (1 / (1 / b)) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hConj_1div hf_nn hg_nn
  -- Simplify the exponents: 1 / (1 / a) = a, 1 / (1 / b) = b.
  have h_inv_inv_a : (1 / (1 / a)) = a := by field_simp
  have h_inv_inv_b : (1 / (1 / b)) = b := by field_simp
  rw [h_inv_inv_a, h_inv_inv_b] at hHolder
  -- Identify LHS with `chernoffZSum (a * lam₁ + b * lam₂)`.
  have h_lhs :
      (∑ i, f i * g i) = chernoffZSum P₁ P₂ (a * lam₁ + b * lam₂) := by
    unfold chernoffZSum
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show (P₁ i) ^ ((1 - lam₁) * a) * (P₂ i) ^ (lam₁ * a) *
            ((P₁ i) ^ ((1 - lam₂) * b) * (P₂ i) ^ (lam₂ * b))
          = (P₁ i) ^ (1 - (a * lam₁ + b * lam₂)) * (P₂ i) ^ (a * lam₁ + b * lam₂)
    -- Strategy: regroup as `(P₁ i)^A * (P₂ i)^B` where
    --   A := (1-λ₁)·a + (1-λ₂)·b   = 1 - (a·λ₁ + b·λ₂)   (using a+b=1)
    --   B := λ₁·a + λ₂·b           = a·λ₁ + b·λ₂
    have hA_eq : (1 - lam₁) * a + (1 - lam₂) * b = 1 - (a * lam₁ + b * lam₂) := by
      nlinarith [hab]
    have hB_eq : lam₁ * a + lam₂ * b = a * lam₁ + b * lam₂ := by ring
    rw [show (P₁ i) ^ ((1 - lam₁) * a) * (P₂ i) ^ (lam₁ * a) *
            ((P₁ i) ^ ((1 - lam₂) * b) * (P₂ i) ^ (lam₂ * b))
          = ((P₁ i) ^ ((1 - lam₁) * a) * (P₁ i) ^ ((1 - lam₂) * b)) *
            ((P₂ i) ^ (lam₁ * a) * (P₂ i) ^ (lam₂ * b)) by ring]
    rw [← Real.rpow_add (hP₁_pos i), ← Real.rpow_add (hP₂_pos i)]
    rw [hA_eq, hB_eq]
  -- Identify ∑ f^(1/a) with chernoffZSum lam₁.
  have h_f_pow_sum : (∑ i, (f i) ^ (1 / a)) = chernoffZSum P₁ P₂ lam₁ := by
    unfold chernoffZSum
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show ((P₁ i) ^ ((1 - lam₁) * a) * (P₂ i) ^ (lam₁ * a)) ^ (1 / a)
        = (P₁ i) ^ (1 - lam₁) * (P₂ i) ^ lam₁
    have hP₁_nn_i := hP₁_nn i
    have hP₂_nn_i := hP₂_nn i
    have hpow₁_nn : 0 ≤ (P₁ i) ^ ((1 - lam₁) * a) := Real.rpow_nonneg hP₁_nn_i _
    have hpow₂_nn : 0 ≤ (P₂ i) ^ (lam₁ * a) := Real.rpow_nonneg hP₂_nn_i _
    rw [Real.mul_rpow hpow₁_nn hpow₂_nn]
    rw [← Real.rpow_mul hP₁_nn_i, ← Real.rpow_mul hP₂_nn_i]
    congr 1
    · congr 1
      field_simp
    · congr 1
      field_simp
  -- Identify ∑ g^(1/b) with chernoffZSum lam₂.
  have h_g_pow_sum : (∑ i, (g i) ^ (1 / b)) = chernoffZSum P₁ P₂ lam₂ := by
    unfold chernoffZSum
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show ((P₁ i) ^ ((1 - lam₂) * b) * (P₂ i) ^ (lam₂ * b)) ^ (1 / b)
        = (P₁ i) ^ (1 - lam₂) * (P₂ i) ^ lam₂
    have hP₁_nn_i := hP₁_nn i
    have hP₂_nn_i := hP₂_nn i
    have hpow₁_nn : 0 ≤ (P₁ i) ^ ((1 - lam₂) * b) := Real.rpow_nonneg hP₁_nn_i _
    have hpow₂_nn : 0 ≤ (P₂ i) ^ (lam₂ * b) := Real.rpow_nonneg hP₂_nn_i _
    rw [Real.mul_rpow hpow₁_nn hpow₂_nn]
    rw [← Real.rpow_mul hP₁_nn_i, ← Real.rpow_mul hP₂_nn_i]
    congr 1
    · congr 1
      field_simp
    · congr 1
      field_simp
  rw [h_lhs, h_f_pow_sum, h_g_pow_sum] at hHolder
  exact hHolder

omit [DecidableEq α] in
/-- `λ ↦ log Z(λ)` is convex on `Icc 0 1` (Cover–Thomas 11.9.1). -/
@[entry_point]
theorem convexOn_chernoffLogZ
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro lam₁ _hlam₁ lam₂ _hlam₂ a b ha_nn hb_nn hab
  show Real.log (chernoffZSum P₁ P₂ (a • lam₁ + b • lam₂))
      ≤ a • Real.log (chernoffZSum P₁ P₂ lam₁) + b • Real.log (chernoffZSum P₁ P₂ lam₂)
  simp only [smul_eq_mul]
  -- Edge cases: a = 0 or b = 0 (= 1 - a).
  rcases eq_or_lt_of_le ha_nn with ha_eq | ha_pos
  · -- a = 0 ⇒ b = 1.
    have ha_eq' : a = 0 := ha_eq.symm
    have hb_eq : b = 1 := by linarith
    rw [ha_eq', hb_eq]; ring_nf; rfl
  rcases eq_or_lt_of_le hb_nn with hb_eq | hb_pos
  · -- b = 0 ⇒ a = 1.
    have hb_eq' : b = 0 := hb_eq.symm
    have ha_eq : a = 1 := by linarith
    rw [hb_eq', ha_eq]; ring_nf; rfl
  -- Both a, b ∈ (0,1): use the Hölder multiplicative form, then take log.
  have hZ_pos := fun l ↦ chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos l
  have h_mul := chernoffZSum_holder_mul (lam₁ := lam₁) (lam₂ := lam₂) P₁ P₂
    hP₁_pos hP₂_pos ha_pos hb_pos hab
  -- Take log on both sides; LHS > 0, RHS > 0.
  have hZ₁ := hZ_pos lam₁
  have hZ₂ := hZ_pos lam₂
  have hZl := hZ_pos (a * lam₁ + b * lam₂)
  have hPowProd_pos : 0 < (chernoffZSum P₁ P₂ lam₁) ^ a * (chernoffZSum P₁ P₂ lam₂) ^ b :=
    mul_pos (Real.rpow_pos_of_pos hZ₁ _) (Real.rpow_pos_of_pos hZ₂ _)
  have h_log_le :
      Real.log (chernoffZSum P₁ P₂ (a * lam₁ + b * lam₂))
        ≤ Real.log
            ((chernoffZSum P₁ P₂ lam₁) ^ a * (chernoffZSum P₁ P₂ lam₂) ^ b) :=
    Real.log_le_log hZl h_mul
  -- Expand `log (Z₁^a * Z₂^b) = a · log Z₁ + b · log Z₂`.
  have h_log_split :
      Real.log ((chernoffZSum P₁ P₂ lam₁) ^ a * (chernoffZSum P₁ P₂ lam₂) ^ b)
        = a * Real.log (chernoffZSum P₁ P₂ lam₁) + b * Real.log (chernoffZSum P₁ P₂ lam₂) := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hZ₁ _).ne' (Real.rpow_pos_of_pos hZ₂ _).ne']
    rw [Real.log_rpow hZ₁, Real.log_rpow hZ₂]
  rw [h_log_split] at h_log_le
  exact h_log_le

/-! ### Chernoff mediator `T_λ` (pmf form) -/

/-- The Chernoff mediator pmf `T_λ(a) := P₁(a)^(1-λ) · P₂(a)^λ / Z(λ)`. -/
noncomputable def chernoffMediator (P₁ P₂ : α → ℝ) (lam : ℝ) : α → ℝ :=
  fun a ↦ (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam / chernoffZSum P₁ P₂ lam

omit [DecidableEq α] in
/-- `T_λ(a) > 0` under full-support `P₁, P₂ > 0`. -/
lemma chernoffMediator_pos
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    0 < chernoffMediator P₁ P₂ lam a := by
  unfold chernoffMediator
  exact div_pos (chernoffZSum_term_pos P₁ P₂ hP₁_pos hP₂_pos lam a)
    (chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam)

omit [DecidableEq α] in
/-- `T_λ` is a pmf: `∑ a, T_λ(a) = 1` (by construction). -/
lemma chernoffMediator_sum_eq_one
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    (∑ a, chernoffMediator P₁ P₂ lam a) = 1 := by
  unfold chernoffMediator
  rw [← Finset.sum_div]
  -- ∑ a (P₁ a)^(1-lam) · (P₂ a)^lam / Z = Z / Z = 1.
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  rw [show chernoffZSum P₁ P₂ lam = ∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam from rfl]
  exact div_self hZ_pos.ne'

omit [DecidableEq α] in
/-- Mediator pmf bound: at endpoints `lam = 0` (resp `lam = 1`), `T_λ = P₁` (resp `P₂`)
under full support + probability conditions. -/
lemma chernoffMediator_lam_zero
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (_hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (a : α) :
    chernoffMediator P₁ P₂ 0 a = P₁ a := by
  unfold chernoffMediator
  rw [chernoffZSum_lam_zero P₁ P₂ hP₁_sum (fun a ↦ (hP₂_pos a).le)]
  rw [Real.rpow_zero, mul_one, sub_zero, Real.rpow_one, div_one]

omit [DecidableEq α] in
lemma chernoffMediator_lam_one
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (_hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₂_sum : ∑ a, P₂ a = 1) (a : α) :
    chernoffMediator P₁ P₂ 1 a = P₂ a := by
  unfold chernoffMediator
  rw [chernoffZSum_lam_one P₁ P₂ (fun a ↦ (hP₁_pos a).le) hP₂_sum]
  rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, div_one]

/-! ### Uniqueness of the Hoeffding minimizer -/

omit [DecidableEq α] in
/-- The Hoeffding minimizer is unique: `klDivPmf · P₂` is strictly convex on the convex constraint
set `K`, so the minimizer of `hoeffdingE2` is unique. -/
@[entry_point]
theorem hoeffdingE2_unique
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (_hP₁_sum : ∑ a, P₁ a = 1)
    (alpha : ℝ) (_h_alpha_nn : 0 ≤ alpha)
    {Q₁ Q₂ : α → ℝ}
    (hQ₁_mem : Q₁ ∈ hoeffdingConstraintSet P₁ alpha)
    (hQ₂_mem : Q₂ ∈ hoeffdingConstraintSet P₁ alpha)
    (hQ₁_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Q₁ P₂)
    (hQ₂_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Q₂ P₂) :
    Q₁ = Q₂ := by
  classical
  -- Strict convexity of `klDivPmf · P₂` on stdSimplex + both Q_i are minimizers ⇒ Q_1 = Q_2.
  -- Strategy: convex midpoint Q₃ := (Q₁ + Q₂) / 2 ∈ K (convexity of K).
  -- If Q₁ ≠ Q₂, then klDivPmf Q₃ P₂ < (klDivPmf Q₁ P₂ + klDivPmf Q₂ P₂) / 2 = hoeffdingE2,
  -- contradicting `hoeffdingE2 ≤ klDivPmf Q₃ P₂` (Q₃ ∈ K).
  by_contra hne
  -- Get a midpoint Q₃ := (1/2) • Q₁ + (1/2) • Q₂.
  have h_simplex_convex : Convex ℝ (stdSimplex ℝ α) := convex_stdSimplex ℝ α
  have hQ₁_simplex : Q₁ ∈ stdSimplex ℝ α := hQ₁_mem.1
  have hQ₂_simplex : Q₂ ∈ stdSimplex ℝ α := hQ₂_mem.1
  -- Strict convexity gives: klDivPmf ((1/2)•Q₁ + (1/2)•Q₂) P₂ <
  --   (1/2) klDivPmf Q₁ P₂ + (1/2) klDivPmf Q₂ P₂.
  have h_strict := klDivPmf_strictConvexOn_left P₂ hP₂_pos
  have h_half : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have h_half_sum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have h_strict_mid :
      klDivPmf ((1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂) P₂
        < (1 / 2 : ℝ) * klDivPmf Q₁ P₂ + (1 / 2 : ℝ) * klDivPmf Q₂ P₂ := by
    have := h_strict.2 hQ₁_simplex hQ₂_simplex hne h_half h_half h_half_sum
    simpa [smul_eq_mul] using this
  -- Substituting hQ₁_min, hQ₂_min: RHS = hoeffdingE2 P₁ P₂ alpha.
  rw [← hQ₁_min, ← hQ₂_min] at h_strict_mid
  have h_rhs_eq :
      (1 / 2 : ℝ) * hoeffdingE2 P₁ P₂ alpha + (1 / 2 : ℝ) * hoeffdingE2 P₁ P₂ alpha
        = hoeffdingE2 P₁ P₂ alpha := by ring
  rw [h_rhs_eq] at h_strict_mid
  -- But Q₃ ∈ K (convexity of K via convex Q ↦ klDivPmf Q P₁), so hoeffdingE2 ≤ klDivPmf Q₃ P₂.
  -- Step 1: midpoint is in stdSimplex.
  have hQ₃_simplex : (1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂ ∈ stdSimplex ℝ α :=
    h_simplex_convex hQ₁_simplex hQ₂_simplex h_half.le h_half.le h_half_sum
  -- Step 2: midpoint satisfies klDivPmf · P₁ ≤ alpha (convex sublevel set).
  have h_klmid_le :
      klDivPmf ((1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂) P₁ ≤ alpha := by
    -- Convexity of `klDivPmf · P₁` on stdSimplex.
    have h_conv := (klDivPmf_strictConvexOn_left P₁ hP₁_pos).convexOn
    have h_conv_mid := h_conv.2 hQ₁_simplex hQ₂_simplex h_half.le h_half.le h_half_sum
    have h_sumlift :
        klDivPmf ((1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂) P₁
          ≤ (1 / 2 : ℝ) * klDivPmf Q₁ P₁ + (1 / 2 : ℝ) * klDivPmf Q₂ P₁ := by
      simpa [smul_eq_mul] using h_conv_mid
    have h_kl₁_le : klDivPmf Q₁ P₁ ≤ alpha := hQ₁_mem.2
    have h_kl₂_le : klDivPmf Q₂ P₁ ≤ alpha := hQ₂_mem.2
    have h_avg :
        (1 / 2 : ℝ) * klDivPmf Q₁ P₁ + (1 / 2 : ℝ) * klDivPmf Q₂ P₁ ≤ alpha := by
      have h1 : (1 / 2 : ℝ) * klDivPmf Q₁ P₁ ≤ (1 / 2 : ℝ) * alpha :=
        mul_le_mul_of_nonneg_left h_kl₁_le h_half.le
      have h2 : (1 / 2 : ℝ) * klDivPmf Q₂ P₁ ≤ (1 / 2 : ℝ) * alpha :=
        mul_le_mul_of_nonneg_left h_kl₂_le h_half.le
      linarith
    linarith
  have hQ₃_in_K : (1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂ ∈ hoeffdingConstraintSet P₁ alpha :=
    ⟨hQ₃_simplex, h_klmid_le⟩
  -- Step 3: hoeffdingE2 ≤ klDivPmf Q₃ P₂ (Q₃ ∈ K).
  have h_E2_le : hoeffdingE2 P₁ P₂ alpha
      ≤ klDivPmf ((1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂) P₂ := by
    unfold hoeffdingE2
    have h_bdd : BddBelow ((fun Q : α → ℝ ↦ klDivPmf Q P₂) ''
        {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Q, hQ, rfl⟩
      exact klDivPmf_nonneg Q P₂ hQ.1.1 (fun a ↦ (hP₂_pos a).le)
    have h_in_img :
        klDivPmf ((1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂) P₂
          ∈ (fun Q : α → ℝ ↦ klDivPmf Q P₂) ''
              {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha} :=
      ⟨_, hQ₃_in_K, rfl⟩
    exact csInf_le h_bdd h_in_img
  linarith

/-! ### Chernoff achievability (Bayes error upper bound)

The achievability side of Cover–Thomas Theorem 11.9.1: the Chernoff bound
`bayesErrorMinPmf P₁ P₂ n ≤ (1/2) · Z(λ)^n` for every `λ ∈ Icc 0 1` yields
`liminf_n -(1/n) log bayesErrorMinPmf ≥ chernoffInfo P₁ P₂`. The `n`-fold IID structure is written
directly with a finite sum `∑_{x : Fin n → α}` of finite products `∏ i, P (x i)`. -/

/-- n-IID Bayes error in pmf form:
`bayesErrorMinPmf P₁ P₂ n := (1/2) · ∑_{x : Fin n → α} min(∏ P₁(x_i), ∏ P₂(x_i))`.

This is the optimal Bayes error for the 2-class hypothesis test with equal priors
`1/2 : 1/2` on `n` IID samples (Bayes-optimal rule decides `i := argmax_i P_i^n(x)`,
giving error contribution `(1/2) · min(P₁^n(x), P₂^n(x))` per `x`). -/
noncomputable def bayesErrorMinPmf (P₁ P₂ : α → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))

/-! ### Per-point bound `min(a, b) ≤ a^(1-λ) · b^λ` -/

omit [DecidableEq α] in
/-- Geometric mean inequality (degenerate Hölder form):
`min(a, b) ≤ a^{1-λ} · b^λ` for `a, b ≥ 0`, `λ ∈ [0, 1]`. -/
lemma min_le_rpow_mul_rpow
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {lam : ℝ}
    (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1) :
    min a b ≤ a ^ (1 - lam) * b ^ lam := by
  have h_min_nn : 0 ≤ min a b := le_min ha hb
  have h_one_sub : 0 ≤ 1 - lam := by linarith
  -- min a b ^ (1 - lam) ≤ a ^ (1 - lam) (since min ≤ a, both ≥ 0, exponent ≥ 0)
  have h1 : (min a b) ^ (1 - lam) ≤ a ^ (1 - lam) :=
    Real.rpow_le_rpow h_min_nn (min_le_left _ _) h_one_sub
  -- min a b ^ lam ≤ b ^ lam
  have h2 : (min a b) ^ lam ≤ b ^ lam :=
    Real.rpow_le_rpow h_min_nn (min_le_right _ _) hlam_nn
  -- Combine: min a b = min a b ^ ((1-lam) + lam) = min a b ^ (1-lam) * min a b ^ lam
  --   ≤ a^(1-lam) * b^lam
  have h_mul :
      (min a b) ^ (1 - lam) * (min a b) ^ lam ≤ a ^ (1 - lam) * b ^ lam := by
    have h_pow1_nn : 0 ≤ (min a b) ^ (1 - lam) := Real.rpow_nonneg h_min_nn _
    have h_pow_a_nn : 0 ≤ a ^ (1 - lam) := Real.rpow_nonneg ha _
    have h_pow_b_nn : 0 ≤ b ^ lam := Real.rpow_nonneg hb _
    have step1 : (min a b) ^ (1 - lam) * (min a b) ^ lam ≤ a ^ (1 - lam) * (min a b) ^ lam :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg h_min_nn _)
    have step2 : a ^ (1 - lam) * (min a b) ^ lam ≤ a ^ (1 - lam) * b ^ lam :=
      mul_le_mul_of_nonneg_left h2 h_pow_a_nn
    linarith
  have h_sum_eq : (min a b) ^ (1 - lam) * (min a b) ^ lam = min a b := by
    rw [← Real.rpow_add_of_nonneg h_min_nn h_one_sub hlam_nn]
    ring_nf
    exact Real.rpow_one _
  linarith [h_sum_eq ▸ h_mul]

/-! ### `bayesErrorMinPmf ≤ (1/2) Z(λ)^n` -/

omit [DecidableEq α] in
/-- Auxiliary: n-IID per-point factorization:
`∏ i, (P₁ (x i)) ^ (1-lam) * (P₂ (x i)) ^ lam = (∏ i, P₁ (x i)) ^ (1-lam) * (∏ i, P₂ (x i)) ^ lam`
under `P₁, P₂ ≥ 0`. -/
lemma prod_rpow_mul_rpow
    (P₁ P₂ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_nn : ∀ a, 0 ≤ P₂ a)
    {n : ℕ} (x : Fin n → α) (lam : ℝ) :
    ∏ i, (P₁ (x i)) ^ (1 - lam) * (P₂ (x i)) ^ lam
      = (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam := by
  -- Split the product, then push rpow through ∏.
  rw [Finset.prod_mul_distrib]
  -- ∏ i, (P₁ (x i))^(1-lam) = (∏ i, P₁ (x i))^(1-lam)
  have h1 : (∏ i, (P₁ (x i)) ^ (1 - lam)) = (∏ i, P₁ (x i)) ^ (1 - lam) :=
    Real.finsetProd_rpow Finset.univ (fun i ↦ P₁ (x i)) (fun i _ ↦ hP₁_nn (x i)) (1 - lam)
  have h2 : (∏ i, (P₂ (x i)) ^ lam) = (∏ i, P₂ (x i)) ^ lam :=
    Real.finsetProd_rpow Finset.univ (fun i ↦ P₂ (x i)) (fun i _ ↦ hP₂_nn (x i)) lam
  rw [h1, h2]

omit [DecidableEq α] in
/-- n-IID Chernoff partition function via product factorization:
`∑_{x : Fin n → α} (∏ i, P₁ (x i))^(1-lam) · (∏ i, P₂ (x i))^lam = Z(λ)^n`. -/
lemma sum_prod_rpow_eq_Z_pow
    (P₁ P₂ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_nn : ∀ a, 0 ≤ P₂ a)
    (lam : ℝ) (n : ℕ) :
    ∑ x : Fin n → α, (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam
      = (chernoffZSum P₁ P₂ lam) ^ n := by
  -- Rewrite each term as ∏ i, (P₁ (x i))^(1-lam) * (P₂ (x i))^lam (prod_rpow_mul_rpow)
  -- then ∑ over (Fin n → α) of ∏ i, f (x i) = (∑ a, f a)^n (Finset.prod_univ_sum or pi).
  have h_term_eq : ∀ x : Fin n → α,
      (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam
        = ∏ i, (P₁ (x i)) ^ (1 - lam) * (P₂ (x i)) ^ lam := by
    intro x
    rw [prod_rpow_mul_rpow P₁ P₂ hP₁_nn hP₂_nn x lam]
  simp_rw [h_term_eq]
  -- ∑ x : Fin n → α, ∏ i, f (x i) = (∑ a, f a) ^ n via Finset.sum_pow'.
  set g : α → ℝ := fun a ↦ (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam with hg_def
  show (∑ x : Fin n → α, ∏ i, g (x i)) = (chernoffZSum P₁ P₂ lam) ^ n
  have h_sum_pow := Finset.sum_pow' (s := (Finset.univ : Finset α)) (f := g) (n := n)
  -- h_sum_pow : (∑ a ∈ univ, g a) ^ n = ∑ p ∈ piFinset (fun _ : Fin n => univ), ∏ i, g (p i)
  rw [show chernoffZSum P₁ P₂ lam = ∑ a, g a from rfl]
  rw [h_sum_pow]
  -- Now: ∑ x : Fin n → α, ∏ i, g (x i) = ∑ p ∈ piFinset (fun _ => univ), ∏ i, g (p i).
  -- piFinset (fun _ => univ) = univ via Fintype.piFinset_univ.
  rw [Fintype.piFinset_univ]

omit [DecidableEq α] in
/-- The Chernoff bound `bayesErrorMinPmf ≤ (1/2) · Z(λ)^n` for each `λ ∈ Icc 0 1`. -/
@[entry_point]
theorem bayesErrorMinPmf_le_half_Z_pow
    (P₁ P₂ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_nn : ∀ a, 0 ≤ P₂ a)
    (n : ℕ) {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1) :
    bayesErrorMinPmf P₁ P₂ n ≤ (1 / 2 : ℝ) * (chernoffZSum P₁ P₂ lam) ^ n := by
  unfold bayesErrorMinPmf
  -- (1/2) ∑ min ≤ (1/2) ∑ (∏ P₁)^(1-λ) (∏ P₂)^λ = (1/2) Z(λ)^n
  have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  apply mul_le_mul_of_nonneg_left _ h_half_nn
  -- ∑ x, min(∏ P₁, ∏ P₂) ≤ ∑ x, (∏ P₁)^(1-λ) (∏ P₂)^λ = Z(λ)^n
  have h_pointwise : ∀ x : Fin n → α,
      min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))
        ≤ (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam := by
    intro x
    have h_prod_P₁_nn : 0 ≤ ∏ i, P₁ (x i) :=
      Finset.prod_nonneg (fun i _ ↦ hP₁_nn (x i))
    have h_prod_P₂_nn : 0 ≤ ∏ i, P₂ (x i) :=
      Finset.prod_nonneg (fun i _ ↦ hP₂_nn (x i))
    exact min_le_rpow_mul_rpow h_prod_P₁_nn h_prod_P₂_nn hlam_nn hlam_le
  have h_sum_le :
      ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))
        ≤ ∑ x : Fin n → α, (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam :=
    Finset.sum_le_sum (fun x _ ↦ h_pointwise x)
  rw [sum_prod_rpow_eq_Z_pow P₁ P₂ hP₁_nn hP₂_nn lam n] at h_sum_le
  exact h_sum_le

/-! ### Positivity of `bayesErrorMinPmf` -/

omit [DecidableEq α] in
/-- `bayesErrorMinPmf > 0` under full support `P₁, P₂ > 0`. -/
lemma bayesErrorMinPmf_pos
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (n : ℕ) :
    0 < bayesErrorMinPmf P₁ P₂ n := by
  unfold bayesErrorMinPmf
  have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
  refine mul_pos h_half_pos ?_
  -- ∑ x, min(∏ P₁, ∏ P₂) > 0: each term ≥ 0, and there exists x (e.g., const) with positive value.
  apply Finset.sum_pos
  · intro x _
    have h_prod_P₁_pos : 0 < ∏ i, P₁ (x i) :=
      Finset.prod_pos (fun i _ ↦ hP₁_pos (x i))
    have h_prod_P₂_pos : 0 < ∏ i, P₂ (x i) :=
      Finset.prod_pos (fun i _ ↦ hP₂_pos (x i))
    exact lt_min h_prod_P₁_pos h_prod_P₂_pos
  · exact Finset.univ_nonempty

/-! ### Per-`λ` rate lower bound -/

omit [DecidableEq α] in
/-- For each fixed `λ ∈ Icc 0 1`,
`-(1/n) log bayesErrorMinPmf ≥ -log Z(λ) + (log 2)/n` (eventually for `n ≥ 1`).

The `+ log 2 / n` slack term vanishes as `n → ∞`, leaving `-log Z(λ)` (and after `min`
over `λ`, `chernoffInfo`). -/
lemma chernoff_rate_ge_neg_log_Z_per_lam
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
      ≥ -Real.log (chernoffZSum P₁ P₂ lam) + Real.log 2 / n := by
  have hP₁_nn : ∀ a, 0 ≤ P₁ a := fun a ↦ (hP₁_pos a).le
  have hP₂_nn : ∀ a, 0 ≤ P₂ a := fun a ↦ (hP₂_pos a).le
  -- bayesErrorMinPmf ≤ (1/2) · Z(λ)^n
  have h_le := bayesErrorMinPmf_le_half_Z_pow P₁ P₂ hP₁_nn hP₂_nn n hlam_nn hlam_le
  have h_pos := bayesErrorMinPmf_pos P₁ P₂ hP₁_pos hP₂_pos n
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  have hZ_pow_pos : (0 : ℝ) < (chernoffZSum P₁ P₂ lam) ^ n := pow_pos hZ_pos n
  have h_half_Z_pos : (0 : ℝ) < (1 / 2 : ℝ) * (chernoffZSum P₁ P₂ lam) ^ n :=
    mul_pos (by norm_num) hZ_pow_pos
  -- Take log of both sides (positives).
  have h_log_le :
      Real.log (bayesErrorMinPmf P₁ P₂ n)
        ≤ Real.log ((1 / 2 : ℝ) * (chernoffZSum P₁ P₂ lam) ^ n) :=
    Real.log_le_log h_pos h_le
  -- Expand RHS: log((1/2) · Z^n) = log(1/2) + n · log Z = -log 2 + n · log Z.
  have h_log_expand :
      Real.log ((1 / 2 : ℝ) * (chernoffZSum P₁ P₂ lam) ^ n)
        = -Real.log 2 + (n : ℝ) * Real.log (chernoffZSum P₁ P₂ lam) := by
    rw [Real.log_mul (by norm_num) hZ_pow_pos.ne']
    rw [Real.log_pow]
    congr 1
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
    rw [Real.log_inv]
  rw [h_log_expand] at h_log_le
  -- Multiply by -(1/n) (negative, flips inequality).
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_neg_inv : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_mul :
      -((1 : ℝ) / n) * (-Real.log 2 + (n : ℝ) * Real.log (chernoffZSum P₁ P₂ lam))
        ≤ -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n) :=
    mul_le_mul_of_nonpos_left h_log_le h_neg_inv
  -- Simplify LHS: -(1/n) * (-log 2 + n · log Z) = (log 2)/n - log Z
  have h_simp :
      -((1 : ℝ) / n) * (-Real.log 2 + (n : ℝ) * Real.log (chernoffZSum P₁ P₂ lam))
        = Real.log 2 / n - Real.log (chernoffZSum P₁ P₂ lam) := by
    field_simp
    ring
  rw [h_simp] at h_mul
  linarith

omit [DecidableEq α] in
/-- For each fixed `λ* ∈ Icc 0 1` attaining `chernoffInfo` (= `-log Z(λ*)`),
`-(1/n) log bayesErrorMinPmf ≥ chernoffInfo + (log 2)/n` (eventually for `n ≥ 1`). -/
lemma chernoff_rate_ge_chernoffInfo_eventually
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    ∀ᶠ n : ℕ in atTop,
      -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
        ≥ chernoffInfo P₁ P₂ + Real.log 2 / n := by
  obtain ⟨lam_star, hlam_mem, hlam_eq⟩ := chernoffInfo_attained P₁ P₂ hP₁_pos hP₂_pos
  -- chernoffInfo = -log Z(λ*), λ* ∈ Icc 0 1
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h := chernoff_rate_ge_neg_log_Z_per_lam P₁ P₂ hP₁_pos hP₂_pos hlam_mem.1 hlam_mem.2 hn
  rw [hlam_eq]
  linarith

omit [DecidableEq α] in
/-- Auxiliary upper bound: `rate n ≤ -log p_min - (log 2)/n` (loose, just to get
boundedness for `liminf` plumbing). Here `p_min := min over a of (min (P₁ a) (P₂ a))`. -/
private lemma chernoff_rate_le_aux_upper
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    ∃ M : ℝ, ∀ᶠ n : ℕ in atTop,
      -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n) ≤ M := by
  -- p_min := min over a of min(P₁ a, P₂ a) > 0.
  classical
  obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image (s := (Finset.univ : Finset α))
    (f := fun a ↦ min (P₁ a) (P₂ a)) ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
  set p_min : ℝ := min (P₁ a₀) (P₂ a₀) with hpmin_def
  have hpmin_pos : 0 < p_min := lt_min (hP₁_pos a₀) (hP₂_pos a₀)
  -- Lower bound: bayesErrorMinPmf ≥ (1/2) · p_min^n · (#α)^n... actually simpler:
  -- bayesErrorMinPmf ≥ (1/2) * min(∏ P₁(x_0), ∏ P₂(x_0)) for x_0 = const a₀.
  -- = (1/2) * min((P₁ a₀)^n, (P₂ a₀)^n) ≥ (1/2) * p_min^n.
  refine ⟨-Real.log p_min + Real.log 2, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
  -- Lower bound on bayesErrorMinPmf via const a₀ vector.
  -- bayesErrorMinPmf = (1/2) * ∑ x, min(∏ P₁(x_i), ∏ P₂(x_i))
  -- Take x := fun _ => a₀: ∏ P₁(x_i) = (P₁ a₀)^n, ∏ P₂(x_i) = (P₂ a₀)^n.
  -- min((P₁ a₀)^n, (P₂ a₀)^n) ≥ p_min^n (using p_min ≤ both).
  have h_pmin_le_P₁_a₀ : p_min ≤ P₁ a₀ := min_le_left _ _
  have h_pmin_le_P₂_a₀ : p_min ≤ P₂ a₀ := min_le_right _ _
  have h_pmin_pow_le : ∀ x : Fin n → α, p_min ^ n ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    intro x
    refine le_min ?_ ?_
    · -- p_min^n ≤ ∏ i, P₁ (x i). Use ∀ i, p_min ≤ P₁ (x i).
      calc p_min ^ n = ∏ _i : Fin n, p_min := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ i : Fin n, P₁ (x i) := by
            refine Finset.prod_le_prod (fun i _ ↦ hpmin_pos.le) (fun i _ ↦ ?_)
            have := ha₀ (x i) (Finset.mem_univ _)
            exact le_trans this (min_le_left _ _)
    · calc p_min ^ n = ∏ _i : Fin n, p_min := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ i : Fin n, P₂ (x i) := by
            refine Finset.prod_le_prod (fun i _ ↦ hpmin_pos.le) (fun i _ ↦ ?_)
            have := ha₀ (x i) (Finset.mem_univ _)
            exact le_trans this (min_le_right _ _)
  -- Sum lower bound: ∑ x, min(...) ≥ #(Fin n → α) · p_min^n ≥ 1 · p_min^n (taking just one term).
  have h_sum_ge :
      ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) ≥ p_min ^ n := by
    -- ∑ ≥ const vector term ≥ p_min^n.
    set x_const : Fin n → α := fun _ ↦ a₀
    have h_term_ge : min (∏ i, P₁ (x_const i)) (∏ i, P₂ (x_const i)) ≥ p_min ^ n :=
      h_pmin_pow_le x_const
    have h_term_nn : ∀ x : Fin n → α, 0 ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
      intro x
      refine le_min ?_ ?_
      · exact Finset.prod_nonneg (fun i _ ↦ (hP₁_pos (x i)).le)
      · exact Finset.prod_nonneg (fun i _ ↦ (hP₂_pos (x i)).le)
    have h_le_sum :=
      Finset.single_le_sum (s := (Finset.univ : Finset (Fin n → α)))
        (f := fun x ↦ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)))
        (fun x _ ↦ h_term_nn x) (Finset.mem_univ x_const)
    linarith
  -- So bayesErrorMinPmf ≥ (1/2) p_min^n.
  have h_bayes_ge : bayesErrorMinPmf P₁ P₂ n ≥ (1 / 2 : ℝ) * p_min ^ n := by
    unfold bayesErrorMinPmf
    have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have := mul_le_mul_of_nonneg_left h_sum_ge h_half_nn
    linarith
  -- log bayesErrorMinPmf ≥ log((1/2) p_min^n) = -log 2 + n · log p_min.
  have h_bayes_pos : (0 : ℝ) < bayesErrorMinPmf P₁ P₂ n :=
    bayesErrorMinPmf_pos P₁ P₂ hP₁_pos hP₂_pos n
  have h_lb_pos : (0 : ℝ) < (1 / 2 : ℝ) * p_min ^ n :=
    mul_pos (by norm_num) (pow_pos hpmin_pos n)
  have h_log_ge :
      Real.log ((1 / 2 : ℝ) * p_min ^ n) ≤ Real.log (bayesErrorMinPmf P₁ P₂ n) :=
    Real.log_le_log h_lb_pos h_bayes_ge
  have h_log_expand :
      Real.log ((1 / 2 : ℝ) * p_min ^ n) = -Real.log 2 + (n : ℝ) * Real.log p_min := by
    rw [Real.log_mul (by norm_num) (pow_pos hpmin_pos n).ne']
    rw [Real.log_pow]
    congr 1
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
    rw [Real.log_inv]
  rw [h_log_expand] at h_log_ge
  -- Multiply by -(1/n) (negative), flips:
  --   -(1/n) * log bayes ≤ -(1/n) * (-log 2 + n · log p_min)
  --   = log 2 / n - log p_min ≤ -log p_min + log 2.
  have h_neg_inv : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_mul :
      -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
        ≤ -((1 : ℝ) / n) * (-Real.log 2 + (n : ℝ) * Real.log p_min) :=
    mul_le_mul_of_nonpos_left h_log_ge h_neg_inv
  have h_simp :
      -((1 : ℝ) / n) * (-Real.log 2 + (n : ℝ) * Real.log p_min)
        = Real.log 2 / n - Real.log p_min := by
    field_simp
    ring
  rw [h_simp] at h_mul
  -- log 2 / n - log p_min ≤ log 2 - log p_min = -log p_min + log 2.
  -- (since log 2 / n ≤ log 2 for n ≥ 1, with log 2 > 0)
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_log2_div_le : Real.log 2 / n ≤ Real.log 2 := by
    have h_div : Real.log 2 / n = Real.log 2 * (1 / n) := by ring
    rw [h_div]
    have h_inv_le : (1 / (n : ℝ)) ≤ 1 := by
      rw [div_le_one hn_R]
      exact_mod_cast hn
    have := mul_le_mul_of_nonneg_left h_inv_le h_log2_pos.le
    linarith [this]
  linarith

omit [DecidableEq α] in
/-- Chernoff achievability (rate-side lower bound):
`liminf_n -(1/n) log bayesErrorMinPmf ≥ chernoffInfo P₁ P₂`. -/
theorem chernoff_achievability
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    chernoffInfo P₁ P₂ ≤ Filter.liminf
      (fun n : ℕ ↦ -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop := by
  -- Strategy: Eventually `chernoffInfo ≤ rate n` (since `chernoffInfo + log 2 / n ≤ rate n`,
  -- and `log 2 / n > 0`). Use `le_liminf_of_le`. The required `IsCoboundedUnder (·≥·)`
  -- follows from a uniform upper bound on `rate n` (via `IsBoundedUnder.isCoboundedUnder_flip`).
  have h_event := chernoff_rate_ge_chernoffInfo_eventually P₁ P₂ hP₁_pos hP₂_pos
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Get an upper bound for cobounded.
  obtain ⟨M, hM⟩ := chernoff_rate_le_aux_upper P₁ P₂ hP₁_pos hP₂_pos
  apply Filter.le_liminf_of_le
  · -- IsCoboundedUnder (·≥·): use the flip of IsBoundedUnder (·≤·).
    have h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun n : ℕ ↦ -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) := ⟨M, hM⟩
    exact h_bdd_above.isCoboundedUnder_ge
  · -- ∀ᶠ n in atTop, chernoffInfo ≤ rate n.
    filter_upwards [h_event, eventually_gt_atTop 0] with n h_event_n hn
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
    have h_pos : (0 : ℝ) < Real.log 2 / n := div_pos h_log2_pos hn_R
    linarith

/-! ### Achievability main statement -/

omit [DecidableEq α] in
/-- The achievability half of the Chernoff bound (Cover–Thomas Theorem 11.9.1): the exponential
convergence rate of `bayesErrorMinPmf` is at least `chernoffInfo P₁ P₂`. -/
@[entry_point]
theorem chernoff_lemma_achievability
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    chernoffInfo P₁ P₂ ≤ Filter.liminf
      (fun n : ℕ ↦ -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop :=
  chernoff_achievability P₁ P₂ hP₁_pos hP₂_pos

end InformationTheory.Shannon.Chernoff
