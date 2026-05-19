import Common2026.Shannon.CsiszarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents

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

/-! ### A-5 Chernoff information symmetry `C(P₁, P₂) = C(P₂, P₁)` -/

omit [DecidableEq α] in
/-- **Symmetry of `chernoffZSum`** in `λ ↔ 1 - λ`:
`Z_{P₁,P₂}(λ) = Z_{P₂,P₁}(1 - λ)` (just swap the exponents). -/
lemma chernoffZSum_swap (P₁ P₂ : α → ℝ) (lam : ℝ) :
    chernoffZSum P₁ P₂ lam = chernoffZSum P₂ P₁ (1 - lam) := by
  unfold chernoffZSum
  refine Finset.sum_congr rfl fun a _ => ?_
  -- (P₁ a)^(1-λ) * (P₂ a)^λ vs (P₂ a)^(1-(1-λ)) * (P₁ a)^(1-λ) = (P₂ a)^λ * (P₁ a)^(1-λ)
  rw [show (1 : ℝ) - (1 - lam) = lam by ring]
  ring

/-- **Chernoff information is symmetric**: `chernoffInfo P₁ P₂ = chernoffInfo P₂ P₁`.

Proof: the image `(log ∘ Z_{P₁,P₂}) '' Icc 0 1` equals `(log ∘ Z_{P₂,P₁}) '' Icc 0 1`
via the change of variable `λ ↔ 1 - λ` (which is a self-bijection on `Icc 0 1`). -/
theorem chernoffInfo_symm (P₁ P₂ : α → ℝ) :
    chernoffInfo P₁ P₂ = chernoffInfo P₂ P₁ := by
  unfold chernoffInfo
  congr 1
  -- Show the two images are equal (under the same sInf).
  refine congrArg sInf ?_
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨lam, hlam, rfl⟩
    refine ⟨1 - lam, ⟨by linarith [hlam.2], by linarith [hlam.1]⟩, ?_⟩
    simp only
    rw [← chernoffZSum_swap P₁ P₂ lam]
  · rintro y ⟨lam, hlam, rfl⟩
    refine ⟨1 - lam, ⟨by linarith [hlam.2], by linarith [hlam.1]⟩, ?_⟩
    simp only
    rw [← chernoffZSum_swap P₂ P₁ lam]

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

/-! ### A-5 (Tier 1 入口) `log Z(λ)` の凸性 (Hölder 経路)

Cover-Thomas 11.9.1 の核となる凸性: `λ ↦ log Z(λ)` は `Icc 0 1` 上で凸。
Hölder 不等式 `∑ f_i g_i ≤ (∑ f_i^p)^{1/p} · (∑ g_i^q)^{1/q}` で
`Z(αλ₁ + βλ₂) ≤ Z(λ₁)^α · Z(λ₂)^β` を取り、対数で
`log Z(αλ₁ + βλ₂) ≤ α log Z(λ₁) + β log Z(λ₂)` を結論する。

端点 `α = 0` または `α = 1` (i.e., `β = 0`) は degenerate (凸結合が片方の端点に
退化) で `Real.HolderConjugate` の `1 < p` 要件に乗らないため、別 case 化する。 -/

omit [DecidableEq α] in
/-- **Hölder multiplicative form** for the Chernoff partition function:
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
  set f : α → ℝ := fun i => (P₁ i) ^ ((1 - lam₁) * a) * (P₂ i) ^ (lam₁ * a) with hf_def
  set g : α → ℝ := fun i => (P₁ i) ^ ((1 - lam₂) * b) * (P₂ i) ^ (lam₂ * b) with hg_def
  have hP₁_nn : ∀ a, 0 ≤ P₁ a := fun a => (hP₁_pos a).le
  have hP₂_nn : ∀ a, 0 ≤ P₂ a := fun a => (hP₂_pos a).le
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
    refine Finset.sum_congr rfl fun i _ => ?_
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
    refine Finset.sum_congr rfl fun i _ => ?_
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
    refine Finset.sum_congr rfl fun i _ => ?_
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

/-- **`log Z(λ)` is convex on `Icc 0 1`**.

Mediator of `chernoffInfo` 達成性 + 凸性 (Cover-Thomas 11.9.1 setup). -/
theorem convexOn_chernoffLogZ
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) := by
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
  have hZ_pos := fun l => chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos l
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

/-! ### A-8 (Tier 1 入口) Chernoff mediator `T_λ` (pmf form)

`T_λ(a) := (P₁ a)^{1-λ} · (P₂ a)^λ / Z(λ)`. Phase B/C で Sanov LDP per-tilt や
tilted LRT を起動する際の入口分布。判断ログ #5 に従い **pmf 形 (`α → ℝ`) で統一**
(Measure 経路は Tier 1+ の Sanov per-tilt 起動段階で必要なら追加)。 -/

/-- **Chernoff mediator** in pmf form: `T_λ(a) := P₁(a)^{1-λ} · P₂(a)^λ / Z(λ)`. -/
noncomputable def chernoffMediator (P₁ P₂ : α → ℝ) (lam : ℝ) : α → ℝ :=
  fun a => (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam / chernoffZSum P₁ P₂ lam

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
/-- **Mediator pmf bound**: at endpoints `lam = 0` (resp `lam = 1`), `T_λ = P₁` (resp `P₂`)
under full support + probability conditions. -/
lemma chernoffMediator_lam_zero
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (_hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (a : α) :
    chernoffMediator P₁ P₂ 0 a = P₁ a := by
  unfold chernoffMediator
  rw [chernoffZSum_lam_zero P₁ P₂ hP₁_sum (fun a => (hP₂_pos a).le)]
  rw [Real.rpow_zero, mul_one, sub_zero, Real.rpow_one, div_one]

omit [DecidableEq α] in
lemma chernoffMediator_lam_one
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (_hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₂_sum : ∑ a, P₂ a = 1) (a : α) :
    chernoffMediator P₁ P₂ 1 a = P₂ a := by
  unfold chernoffMediator
  rw [chernoffZSum_lam_one P₁ P₂ (fun a => (hP₁_pos a).le) hP₂_sum]
  rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, div_one]

/-! ### Phase D 残 — `hoeffdingE2` 一意性 (Csiszar projection + strict convexity 経由) -/

/-- **Hoeffding `min` 達成点の一意性**: the constraint set `K` is convex (closed +
sub-simplex の preimage of convex sublevel under convex `klDivPmf · P₁` is closed +
convex), `klDivPmf · P₂` は `K` 上で strictly convex (full-support `P₂` から `stdSimplex` 上
で strictly convex)、よって最小値達成点は一意。 -/
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
  -- Strict convexity of `klDivPmf · P₂` on stdSimplex + both Q_i are minimizers ⇒ Q_1 = Q_2.
  -- Strategy: convex midpoint Q₃ := (Q₁ + Q₂) / 2 ∈ K (convexity of K).
  -- If Q₁ ≠ Q₂, then klDivPmf Q₃ P₂ < (klDivPmf Q₁ P₂ + klDivPmf Q₂ P₂) / 2 = hoeffdingE2,
  -- contradicting `hoeffdingE2 ≤ klDivPmf Q₃ P₂` (Q₃ ∈ K).
  by_contra hne
  -- Get a midpoint Q₃ := (1/2) • Q₁ + (1/2) • Q₂.
  have h_simplex_convex : Convex ℝ (stdSimplex ℝ α) := convex_stdSimplex ℝ α
  have hQ₁_simplex : Q₁ ∈ stdSimplex ℝ α := hQ₁_mem.1
  have hQ₂_simplex : Q₂ ∈ stdSimplex ℝ α := hQ₂_mem.1
  -- Strict convexity gives: klDivPmf ((1/2)•Q₁ + (1/2)•Q₂) P₂ < (1/2) klDivPmf Q₁ P₂ + (1/2) klDivPmf Q₂ P₂.
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
    have h_bdd : BddBelow ((fun Q : α → ℝ => klDivPmf Q P₂) ''
        {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Q, hQ, rfl⟩
      exact klDivPmf_nonneg Q P₂ hQ.1.1 (fun a => (hP₂_pos a).le)
    have h_in_img :
        klDivPmf ((1 / 2 : ℝ) • Q₁ + (1 / 2 : ℝ) • Q₂) P₂
          ∈ (fun Q : α → ℝ => klDivPmf Q P₂) ''
              {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha} :=
      ⟨_, hQ₃_in_K, rfl⟩
    exact csInf_le h_bdd h_in_img
  linarith

end InformationTheory.Shannon.Chernoff
