import Common2026.Shannon.CsiszarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-!
# Chernoff information + Hoeffding tradeoff exponent (T1-B + T1-D, Tier 0)

textbook (Cover-Thomas 11.7 / 11.9) の Chernoff exponent `C(P₁, P₂)` と
Hoeffding tradeoff exponent `E₂(α)` を **finite-alphabet pmf** 形 (`α → ℝ`)
で定義し、最も基本的な性質 (端点値、非負性、`Icc 0 1` 上の連続性、`min` 達成性)
を publish する Tier 0 baseline.

## 主定義

* `chernoffZSum P₁ P₂ lam := ∑ a, (P₁ a)^(1-lam) · (P₂ a)^lam` (textbook `Z(λ)`)
* `chernoffInfo P₁ P₂ := -sInf ((Real.log ∘ chernoffZSum P₁ P₂) '' Icc 0 1)`
  (Chernoff information; achievement & non-negativity below)
* `hoeffdingE2 P₁ P₂ alpha := sInf ((klDivPmf · P₂) '' {Q ∈ stdSimplex ∧ klDivPmf Q P₁ ≤ alpha})`
  (Hoeffding tradeoff exponent at Type I level `alpha`)

## Tier 0 publish 内容

- `chernoffZSum_lam_zero`, `chernoffZSum_lam_one` — 端点 `Z(0) = Z(1) = 1`
- `chernoffZSum_pos` — full-support 下で `Z(λ) > 0`
- `chernoffZSum_continuous` — `Icc 0 1` 上の連続性
- `chernoffInfo_attained` — `∃ λ ∈ Icc 0 1, chernoffInfo = -log Z(λ)`
- `chernoffInfo_nonneg` — `chernoffInfo ≥ 0`
- `klDivPmf_self_eq_zero` — `klDivPmf P P = 0` (Hoeffding 側で再利用)
- `hoeffdingE2_constraint_nonempty` — 制約集合非空 (`P₁ ∈ K`)
- `hoeffdingE2_attained` — Csiszar projection 経由で達成性
- `hoeffdingE2_nonneg` — `hoeffdingE2 ≥ 0`

Tier 1+ (achievability / converse for Chernoff、tradeoff `Tendsto` 形) は本ファイル
では未着手 (judgement log + plan §進捗 参照).

## 設計判断

- **finite-alphabet pmf 形 (`α → ℝ`)** に統一: Tier 0 で `Measure` 経路は不要、
  `CsiszarProjection.klDivPmf` を素直に再利用できる
- **Mathlib-shape-driven**: `chernoffInfo` は `sInf (... '' Icc 0 1)` 形で定義し、
  `IsCompact.exists_isMinOn` + `Real.sInf_image_Icc_*` 系で達成性を取る
- **撤退ライン L-S3** (定義 + 基本性質のみ publish) を確実に通すスコープに絞った。
  Tier 1+ (Sanov LDP per-tilt / tilted LRT) は別セッション
-/

namespace InformationTheory.Shannon.Chernoff

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter
open InformationTheory.Shannon.CsiszarProjection
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Phase A — Chernoff exponent 定義 + 基本性質 -/

/-- **Chernoff partition function** `Z(λ) := ∑_a P₁(a)^{1-λ} · P₂(a)^λ`
(Cover-Thomas 11.9.1). textbook 形そのまま、`Real.rpow` 算術で書く. -/
noncomputable def chernoffZSum (P₁ P₂ : α → ℝ) (lam : ℝ) : ℝ :=
  ∑ a : α, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam

/-- **Chernoff information** `C(P₁, P₂) := -min_{λ ∈ [0,1]} log Z(λ)`.

`sInf` で書き、`chernoffInfo_attained` で実際に `min` が達成されることを別途証明. -/
noncomputable def chernoffInfo (P₁ P₂ : α → ℝ) : ℝ :=
  -(sInf ((fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1))

/-! ### A-1 端点値 `Z(0) = Z(1) = 1` -/

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

/-! ### A-2 strict positivity -/

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

/-! ### A-3 連続性 -/

omit [DecidableEq α] in
/-- `λ ↦ Z(λ)` is continuous on `ℝ`. -/
lemma chernoffZSum_continuous
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Continuous (fun lam : ℝ => chernoffZSum P₁ P₂ lam) := by
  unfold chernoffZSum
  refine continuous_finsetSum _ fun a _ => ?_
  -- Each term: (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam.
  have h1 : Continuous (fun lam : ℝ => (P₁ a) ^ (1 - lam)) := by
    have h_base : Continuous (fun lam : ℝ => (1 - lam)) := continuous_const.sub continuous_id
    exact (Real.continuous_const_rpow (hP₁_pos a).ne').comp h_base
  have h2 : Continuous (fun lam : ℝ => (P₂ a) ^ lam) :=
    Real.continuous_const_rpow (hP₂_pos a).ne'
  exact h1.mul h2

omit [DecidableEq α] in
/-- `λ ↦ log Z(λ)` is continuous on `ℝ` (under full-support strict positivity of `Z`). -/
lemma chernoffLogZ_continuous
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Continuous (fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) := by
  -- Z(λ) > 0 always (full support); use Real.continuousAt_log on each point.
  have hZ_cont : Continuous (fun lam : ℝ => chernoffZSum P₁ P₂ lam) :=
    chernoffZSum_continuous P₁ P₂ hP₁_pos hP₂_pos
  refine continuous_iff_continuousAt.mpr fun lam => ?_
  have h_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  exact (Real.continuousAt_log h_pos.ne').comp hZ_cont.continuousAt

/-! ### A-4 `chernoffInfo` 達成性 + 非負性 -/

omit [DecidableEq α] in
/-- The image set `(log ∘ Z) '' Icc 0 1` is nonempty (since `Icc 0 1` is). -/
lemma chernoffLogZ_image_nonempty
    (P₁ P₂ : α → ℝ) :
    ((fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1).Nonempty :=
  Set.Nonempty.image _ ⟨0, by norm_num⟩

/-- Chernoff information is attained: `∃ λ* ∈ Icc 0 1, chernoffInfo = -log Z(λ*)`. -/
theorem chernoffInfo_attained
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    ∃ lam ∈ Set.Icc (0:ℝ) 1, chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam)) := by
  -- `IsCompact.exists_sInf_image_eq` on the compact `Icc 0 1` for the continuous `log ∘ Z`.
  have h_compact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have h_ne : (Set.Icc (0:ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  have h_cont : Continuous (fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) :=
    chernoffLogZ_continuous P₁ P₂ hP₁_pos hP₂_pos
  obtain ⟨lam, hlam_mem, h_sInf_eq⟩ :=
    h_compact.exists_sInf_image_eq h_ne h_cont.continuousOn
  refine ⟨lam, hlam_mem, ?_⟩
  unfold chernoffInfo
  rw [h_sInf_eq]

/-- `chernoffInfo P₁ P₂ ≥ 0`.

`chernoffInfo := -sInf (log Z '' Icc 0 1)`. At `λ = 0`, `log Z(0) = log 1 = 0`, so
`sInf (log Z '' Icc 0 1) ≤ 0` (compact + continuous gives `sInf` attained, and `0` is in
the image). Hence `chernoffInfo ≥ 0`. -/
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
  have h_cont : Continuous (fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) :=
    chernoffLogZ_continuous P₁ P₂ hP₁_pos hP₂_pos
  have h_img_compact : IsCompact
      ((fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1) :=
    h_compact.image_of_continuousOn h_cont.continuousOn
  have h_bdd : BddBelow
      ((fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1) :=
    h_img_compact.bddBelow
  -- 0 ∈ Icc, so `log Z(0)` is in the image.
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have h_logZ0_in_img :
      Real.log (chernoffZSum P₁ P₂ 0)
        ∈ (fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1 :=
    ⟨0, h0_mem, rfl⟩
  have h_Z0 : chernoffZSum P₁ P₂ 0 = 1 :=
    chernoffZSum_lam_zero P₁ P₂ hP₁_sum (fun a => (hP₂_pos a).le)
  have h_logZ0 : Real.log (chernoffZSum P₁ P₂ 0) = 0 := by
    rw [h_Z0, Real.log_one]
  -- sInf image ≤ log Z(0) = 0.
  calc sInf ((fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1)
      ≤ Real.log (chernoffZSum P₁ P₂ 0) := csInf_le h_bdd h_logZ0_in_img
    _ = 0 := h_logZ0

/-! ## Phase D — Hoeffding tradeoff exponent (Tier 0: 定義 + min 達成性) -/

/-- `klDivPmf P P = 0`: KL divergence of any pmf with itself is zero.
Useful for Hoeffding constraint set non-emptiness (`P₁ ∈ {Q : klDivPmf Q P₁ ≤ alpha}`). -/
lemma klDivPmf_self_eq_zero
    (P : α → ℝ) (hP_pos : ∀ a, 0 < P a) :
    klDivPmf P P = 0 := by
  unfold klDivPmf
  refine Finset.sum_eq_zero (fun a _ => ?_)
  -- P a * klFun (P a / P a) = P a * klFun 1 = P a * 0 = 0
  have h_div : P a / P a = 1 := div_self (hP_pos a).ne'
  rw [h_div, InformationTheory.klFun_one, mul_zero]

/-- **Hoeffding tradeoff exponent** at Type I level `alpha`:
`E₂(α) := min { klDivPmf Q P₂ | Q ∈ stdSimplex ∧ klDivPmf Q P₁ ≤ α }`. -/
noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ :=
  sInf ((fun Q : α → ℝ => klDivPmf Q P₂) ''
    {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha})

/-- The Hoeffding constraint set
`K := {Q ∈ stdSimplex | klDivPmf Q P₁ ≤ α}`. -/
def hoeffdingConstraintSet (P₁ : α → ℝ) (alpha : ℝ) : Set (α → ℝ) :=
  {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}

/-- The Hoeffding constraint set is **non-empty** when `α ≥ 0` and `P₁` is a positive pmf:
`P₁` itself satisfies `klDivPmf P₁ P₁ = 0 ≤ α`. -/
lemma hoeffdingConstraintSet_nonempty
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    (hoeffdingConstraintSet P₁ alpha).Nonempty := by
  refine ⟨P₁, ?_, ?_⟩
  · refine ⟨fun a => (hP₁_pos a).le, hP₁_sum⟩
  · rw [klDivPmf_self_eq_zero P₁ hP₁_pos]
    exact h_alpha_nn

/-- The Hoeffding constraint set is a **subset of the simplex**. -/
lemma hoeffdingConstraintSet_subset_stdSimplex
    (P₁ : α → ℝ) (alpha : ℝ) :
    hoeffdingConstraintSet P₁ alpha ⊆ stdSimplex ℝ α :=
  fun _ hQ => hQ.1

/-- The Hoeffding constraint set is **closed** (intersection of the closed simplex with
the closed sublevel set of the continuous function `Q ↦ klDivPmf Q P₁`). -/
lemma hoeffdingConstraintSet_isClosed
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha : ℝ) :
    IsClosed (hoeffdingConstraintSet P₁ alpha) := by
  -- K = stdSimplex ∩ {Q | klDivPmf Q P₁ ≤ alpha}.
  have h_simplex : IsClosed (stdSimplex ℝ α) := isClosed_stdSimplex ℝ α
  have h_cont : Continuous (fun Q : α → ℝ => klDivPmf Q P₁) :=
    continuous_klDivPmf_left P₁ hP₁_pos
  have h_sublevel : IsClosed {Q : α → ℝ | klDivPmf Q P₁ ≤ alpha} :=
    isClosed_le h_cont continuous_const
  exact h_simplex.inter h_sublevel

/-- **Hoeffding `min` 達成性**: there exists `Q* ∈ K` realizing the infimum
`hoeffdingE2 P₁ P₂ alpha = klDivPmf Q* P₂`.

Strategy: the constraint set `K` is compact (closed subset of the simplex). The functional
`Q ↦ klDivPmf Q P₂` is continuous in `Q` (`continuous_klDivPmf_left`). Apply
`IsCompact.exists_sInf_image_eq` directly. -/
theorem hoeffdingE2_attained
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha,
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ := by
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
  have h_cont : Continuous (fun Q : α → ℝ => klDivPmf Q P₂) :=
    continuous_klDivPmf_left P₂ hP₂_pos
  obtain ⟨Qstar, hQs_mem, h_sInf_eq⟩ :=
    h_compact.exists_sInf_image_eq h_ne h_cont.continuousOn
  refine ⟨Qstar, hQs_mem, ?_⟩
  unfold hoeffdingE2
  exact h_sInf_eq

/-- `hoeffdingE2 P₁ P₂ alpha ≥ 0`.

`hoeffdingE2 := sInf (klDivPmf · P₂ '' K)`. Since `K` is nonempty and every element in
the image is `≥ 0` (`klDivPmf_nonneg`), the infimum is `≥ 0` by `le_csInf`. -/
theorem hoeffdingE2_nonneg
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    0 ≤ hoeffdingE2 P₁ P₂ alpha := by
  unfold hoeffdingE2
  have h_ne : (hoeffdingConstraintSet P₁ alpha).Nonempty :=
    hoeffdingConstraintSet_nonempty P₁ hP₁_pos hP₁_sum alpha h_alpha_nn
  have h_img_ne :
      ((fun Q : α → ℝ => klDivPmf Q P₂) ''
        {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}).Nonempty :=
    h_ne.image _
  refine le_csInf h_img_ne ?_
  rintro y ⟨Q, hQ, rfl⟩
  have hQ_nn : ∀ a, 0 ≤ Q a := hQ.1.1
  have hP₂_nn : ∀ a, 0 ≤ P₂ a := fun a => (hP₂_pos a).le
  exact klDivPmf_nonneg Q P₂ hQ_nn hP₂_nn

end InformationTheory.Shannon.Chernoff
