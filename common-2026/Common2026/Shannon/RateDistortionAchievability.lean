import Common2026.Shannon.RateDistortionConverse
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.Compact

/-!
# Rate-distortion achievability (E-3 Phase A 完全形)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)
の Phase A 完全形。Cover-Thomas 10.5 achievability 半分のための **structure 部分
+ pmf 直接形 R(D)** を publish:

## 既存 (skeleton MVP)

- `DistortionFn α β := α → β → NNReal`
- `blockDistortion d n x y : ℝ` — `(1/n) ∑ d(x_i, y_i)`
- `LossyCode M n α β` structure
- `LossyCode.expectedBlockDistortion μ d c : ℝ`

## 新規 (Phase A 完全形)

- `expectedDistortionPmf d q : ℝ` — `∑ a, b, q(a,b) · d(a,b)` (pmf 直接形)
- `marginalFst q : α → ℝ` / `marginalSnd q : β → ℝ` — joint pmf の marginals
- `RDConstraint P_X d D : Set (α × β → ℝ)` — feasible joint pmf 集合
- `mutualInfoPmf q : ℝ` — entropy 形 `H(fst) + H(snd) - H(q)` (`negMulLog` ベース連続)
- `rateDistortionFunctionPmf P_X d D : ℝ` — `⨅ q ∈ RDConstraint, mutualInfoPmf q`
- **`RDConstraint_isCompact`** / `RDConstraint_isClosed` / `RDConstraint_convex`
- **`mutualInfoPmf_continuous`** — `negMulLog` 連続性経由
- **`rateDistortionFunctionPmf_attained`** — `IsCompact.exists_isMinOn`
- `RDConstraint.nonempty_of_le` — `D ≥ D_max` で全 stdSimplex が in (point に依らず)
  ＋ `D ≥ achievable D` 系の自然性
- `rateDistortionFunctionPmf_antitone`

## 設計判断

- **MI を `negMulLog` (entropy) 形で定義**: `H(X)+H(Y)−H(X,Y)` は `negMulLog` の
  finite sum で書け、`Real.continuous_negMulLog` から全 `α×β → ℝ` 上連続が出る。
  KL/log 比形は marginal 0 で連続性が崩れるので採用しない。
- **`RDConstraint` は `Set (α × β → ℝ)`**: stdSimplex `α × β` 上の affine constraint。
  closed convex で `IsCompact.exists_isMinOn` が直接効く。
- **非空性は `D ≥ D_max`** で discharge: 任意の `q ∈ stdSimplex` で `expectedDistortion ≤ D_max`。
  textbook の `D ≥ D_min` 形は別補題で出せるが本 Phase は不要。
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Distortion function (既存 skeleton) -/

/-- 単文字 distortion 関数 `d : α → β → ℝ≥0`. -/
abbrev DistortionFn (α β : Type*) := α → β → NNReal

/-- ブロック距離 `d^n((x_i), (y_i)) := (1/n) ∑ d(x_i, y_i)`. 戻り値は `ℝ`. -/
noncomputable def blockDistortion {α β : Type*} (d : DistortionFn α β) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ((d (x i) (y i) : NNReal) : ℝ)

/-- ブロック距離は非負. `NNReal` 値の和は非負、`1/n ≥ 0`. -/
theorem blockDistortion_nonneg
    {α β : Type*} (d : DistortionFn α β) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) :
    0 ≤ blockDistortion d n x y := by
  unfold blockDistortion
  refine mul_nonneg ?_ ?_
  · by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · exact div_nonneg zero_le_one (le_of_lt (lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)))
  · exact Finset.sum_nonneg (fun i _ => NNReal.coe_nonneg _)

/-! ## Block lossy code (既存 skeleton) -/

/-- A **block lossy code** of length `n` with `M` codewords over source alphabet `α`
and reconstruction alphabet `β`: a deterministic encoder `(Fin n → α) → Fin M` and
decoder `Fin M → (Fin n → β)`. -/
structure LossyCode (M n : ℕ) (α β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M → (Fin n → β)

namespace LossyCode

variable {M n : ℕ}

/-- Expected block distortion of a lossy code under an i.i.d. source `P_X` on `α`. -/
noncomputable def expectedBlockDistortion
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) : ℝ :=
  ∫ x : Fin n → α,
      blockDistortion d n x (c.decoder (c.encoder x))
    ∂(Measure.pi (fun _ : Fin n => P_X))

/-- Expected block distortion is non-negative. -/
theorem expectedBlockDistortion_nonneg
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) :
    0 ≤ c.expectedBlockDistortion P_X d := by
  unfold expectedBlockDistortion
  exact integral_nonneg (fun x => blockDistortion_nonneg d n x _)

end LossyCode

/-! ## Phase A 完全形: pmf 形 expectedDistortion / marginal / RDConstraint -/

section PmfForm

variable [Fintype α] [Fintype β]

/-- pmf 形 expected distortion `∑ a, b, q(a,b) · d(a,b)` for a joint pmf
`q : α × β → ℝ` and `NNReal`-valued distortion `d`. -/
noncomputable def expectedDistortionPmf
    (d : DistortionFn α β) (q : α × β → ℝ) : ℝ :=
  ∑ a, ∑ b, q (a, b) * ((d a b : NNReal) : ℝ)

/-- First (source-side) marginal of a joint pmf `q : α × β → ℝ`. -/
noncomputable def marginalFst (q : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, q (a, b)

/-- Second (reconstruction-side) marginal of a joint pmf `q : α × β → ℝ`. -/
noncomputable def marginalSnd (q : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, q (a, b)

/-- `expectedDistortionPmf` is linear in `q`: 線形 functional `∑ q(a,b) c(a,b)`. -/
lemma expectedDistortionPmf_nonneg
    (d : DistortionFn α β) (q : α × β → ℝ)
    (hq : q ∈ stdSimplex ℝ (α × β)) :
    0 ≤ expectedDistortionPmf d q := by
  unfold expectedDistortionPmf
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  exact mul_nonneg (hq.1 (a, b)) (NNReal.coe_nonneg _)

/-- Continuity of `expectedDistortionPmf` in `q` (linear in finite sum). -/
lemma continuous_expectedDistortionPmf (d : DistortionFn α β) :
    Continuous (fun q : α × β → ℝ => expectedDistortionPmf d q) := by
  unfold expectedDistortionPmf
  refine continuous_finsetSum _ fun a _ => ?_
  refine continuous_finsetSum _ fun b _ => ?_
  exact (continuous_apply (a, b)).mul continuous_const

/-- Continuity of `marginalFst` in `q`. -/
lemma continuous_marginalFst :
    Continuous (fun q : α × β → ℝ => marginalFst q) := by
  unfold marginalFst
  refine continuous_pi fun a => ?_
  refine continuous_finsetSum _ fun b _ => ?_
  exact continuous_apply (a, b)

/-- Continuity of `marginalSnd` in `q`. -/
lemma continuous_marginalSnd :
    Continuous (fun q : α × β → ℝ => marginalSnd q) := by
  unfold marginalSnd
  refine continuous_pi fun b => ?_
  refine continuous_finsetSum _ fun a _ => ?_
  exact continuous_apply (a, b)

/-- Marginal-fst is non-negative on the simplex. -/
lemma marginalFst_nonneg {q : α × β → ℝ} (hq : q ∈ stdSimplex ℝ (α × β)) (a : α) :
    0 ≤ marginalFst q a := by
  unfold marginalFst
  exact Finset.sum_nonneg fun b _ => hq.1 (a, b)

/-- Marginal-snd is non-negative on the simplex. -/
lemma marginalSnd_nonneg {q : α × β → ℝ} (hq : q ∈ stdSimplex ℝ (α × β)) (b : β) :
    0 ≤ marginalSnd q b := by
  unfold marginalSnd
  exact Finset.sum_nonneg fun a _ => hq.1 (a, b)

/-- **`RDConstraint`** — feasible joint pmf set `{q ∈ stdSimplex | marginalFst q = P_X ∧
expectedDistortionPmf d q ≤ D}`. -/
def RDConstraint
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : Set (α × β → ℝ) :=
  {q | q ∈ stdSimplex ℝ (α × β) ∧ marginalFst q = P_X ∧ expectedDistortionPmf d q ≤ D}

lemma mem_RDConstraint_iff {P_X : α → ℝ} {d : DistortionFn α β} {D : ℝ}
    {q : α × β → ℝ} :
    q ∈ RDConstraint P_X d D ↔
      q ∈ stdSimplex ℝ (α × β) ∧ marginalFst q = P_X ∧
        expectedDistortionPmf d q ≤ D := Iff.rfl

/-- `RDConstraint ⊆ stdSimplex ℝ (α × β)`. -/
lemma RDConstraint_subset_stdSimplex (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    RDConstraint P_X d D ⊆ stdSimplex ℝ (α × β) :=
  fun _ hq => hq.1

/-- `RDConstraint` is closed: intersection of closed sets (stdSimplex closed,
linear constraints closed). -/
lemma RDConstraint_isClosed (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    IsClosed (RDConstraint P_X d D) := by
  -- {q | q ∈ stdSimplex} ∩ {q | marginalFst q = P_X} ∩ {q | expectedDistortionPmf d q ≤ D}
  have h1 : IsClosed (stdSimplex ℝ (α × β)) := isClosed_stdSimplex ℝ (α × β)
  have h2 : IsClosed {q : α × β → ℝ | marginalFst q = P_X} :=
    isClosed_eq continuous_marginalFst continuous_const
  have h3 : IsClosed {q : α × β → ℝ | expectedDistortionPmf d q ≤ D} :=
    isClosed_le (continuous_expectedDistortionPmf d) continuous_const
  have heq : RDConstraint P_X d D
      = stdSimplex ℝ (α × β) ∩ {q | marginalFst q = P_X} ∩
          {q | expectedDistortionPmf d q ≤ D} := by
    ext q; constructor
    · rintro ⟨h1', h2', h3'⟩; exact ⟨⟨h1', h2'⟩, h3'⟩
    · rintro ⟨⟨h1', h2'⟩, h3'⟩; exact ⟨h1', h2', h3'⟩
  rw [heq]
  exact (h1.inter h2).inter h3

/-- `RDConstraint` is compact (closed subset of compact stdSimplex). -/
lemma RDConstraint_isCompact (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    IsCompact (RDConstraint P_X d D) :=
  IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ (α × β))
    (RDConstraint_isClosed P_X d D)
    (RDConstraint_subset_stdSimplex P_X d D)

/-- `RDConstraint` is convex (intersection of convex sets). -/
lemma RDConstraint_convex (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    Convex ℝ (RDConstraint P_X d D) := by
  intro q₁ hq₁ q₂ hq₂ s t hs ht hst
  obtain ⟨hq₁_simp, hq₁_marg, hq₁_dist⟩ := hq₁
  obtain ⟨hq₂_simp, hq₂_marg, hq₂_dist⟩ := hq₂
  refine ⟨?_, ?_, ?_⟩
  · -- stdSimplex is convex
    exact convex_stdSimplex ℝ (α × β) hq₁_simp hq₂_simp hs ht hst
  · -- marginalFst linear ⟹ marginal of mix = mix of marginals = P_X
    funext a
    simp only [marginalFst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ b, (s * q₁ (a, b) + t * q₂ (a, b))
        = s * (∑ b, q₁ (a, b)) + t * (∑ b, q₂ (a, b)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [this]
    have h1' : (∑ b, q₁ (a, b)) = marginalFst q₁ a := rfl
    have h2' : (∑ b, q₂ (a, b)) = marginalFst q₂ a := rfl
    rw [h1', h2', hq₁_marg, hq₂_marg]
    -- Now: s * P_X a + t * P_X a = P_X a (using hst : s + t = 1)
    have : s * P_X a + t * P_X a = (s + t) * P_X a := by ring
    rw [this, hst, one_mul]
  · -- expectedDistortionPmf linear ⟹ mix ≤ s * D + t * D = D
    have h_lin : expectedDistortionPmf d (s • q₁ + t • q₂)
        = s * expectedDistortionPmf d q₁ + t * expectedDistortionPmf d q₂ := by
      unfold expectedDistortionPmf
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      -- LHS: ∑ a, ∑ b, (s * q₁ (a,b) + t * q₂ (a,b)) * d(a,b)
      -- RHS: s * ∑ a, ∑ b, q₁ (a,b) * d(a,b) + t * ∑ a, ∑ b, q₂ (a,b) * d(a,b)
      simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum]
    rw [h_lin]
    calc s * expectedDistortionPmf d q₁ + t * expectedDistortionPmf d q₂
        ≤ s * D + t * D :=
          add_le_add (mul_le_mul_of_nonneg_left hq₁_dist hs)
            (mul_le_mul_of_nonneg_left hq₂_dist ht)
      _ = (s + t) * D := by ring
      _ = D := by rw [hst, one_mul]

/-! ## pmf 形 mutual information (entropy 形、`negMulLog` 経由連続) -/

/-- `mutualInfoPmf q := H(fst) + H(snd) − H(joint)` written via `negMulLog`:
`I(X;Y) = ∑_a negMulLog(q.fst a) + ∑_b negMulLog(q.snd b) − ∑_{a,b} negMulLog(q(a,b))`.
This formulation is **continuous on all of `α × β → ℝ`** because `Real.negMulLog`
is continuous everywhere (with `negMulLog 0 = 0`). -/
noncomputable def mutualInfoPmf (q : α × β → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (marginalFst q a))
    + (∑ b, Real.negMulLog (marginalSnd q b))
    - (∑ p, Real.negMulLog (q p))

/-- `mutualInfoPmf` is continuous on `α × β → ℝ`. -/
lemma continuous_mutualInfoPmf :
    Continuous (fun q : α × β → ℝ => mutualInfoPmf q) := by
  unfold mutualInfoPmf
  refine Continuous.sub (Continuous.add ?_ ?_) ?_
  · refine continuous_finsetSum _ fun a _ => ?_
    have h_marg : Continuous (fun q : α × β → ℝ => marginalFst q a) :=
      (continuous_apply a).comp continuous_marginalFst
    exact Real.continuous_negMulLog.comp h_marg
  · refine continuous_finsetSum _ fun b _ => ?_
    have h_marg : Continuous (fun q : α × β → ℝ => marginalSnd q b) :=
      (continuous_apply b).comp continuous_marginalSnd
    exact Real.continuous_negMulLog.comp h_marg
  · refine continuous_finsetSum _ fun p _ => ?_
    exact Real.continuous_negMulLog.comp (continuous_apply p)

/-! ## pmf 形 rate-distortion function `R(D)` -/

/-- **`rateDistortionFunctionPmf P_X d D`**:
`R(D) := sInf {mutualInfoPmf q | q ∈ RDConstraint P_X d D}`.
This is the pmf-direct formulation of the rate-distortion function. When the
constraint set is non-empty the infimum is attained (see `rateDistortionFunctionPmf_attained`)
since `RDConstraint` is compact and `mutualInfoPmf` is continuous.

We use `sInf` of the image (rather than predicate-`⨅`) to avoid the
`ConditionallyCompleteLattice` `BddBelow` side conditions that plague
`⨅ q ∈ S, f q` reasoning over `ℝ`. -/
noncomputable def rateDistortionFunctionPmf
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : ℝ :=
  sInf (mutualInfoPmf '' RDConstraint P_X d D)

/-! ## Phase A 達成性 (existence of minimizer) -/

/-- **Achievability** of `rateDistortionFunctionPmf`: when the constraint set
`RDConstraint P_X d D` is non-empty, the infimum is attained by some `q* ∈ RDConstraint`. -/
theorem rateDistortionFunctionPmf_attained
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ)
    (h_ne : (RDConstraint P_X d D).Nonempty) :
    ∃ qStar ∈ RDConstraint P_X d D,
      IsMinOn (fun q => mutualInfoPmf q) (RDConstraint P_X d D) qStar := by
  have h_compact : IsCompact (RDConstraint P_X d D) := RDConstraint_isCompact P_X d D
  have h_cont : Continuous (fun q : α × β → ℝ => mutualInfoPmf q) := continuous_mutualInfoPmf
  exact h_compact.exists_isMinOn h_ne h_cont.continuousOn

/-- **Achievability — value form**: when the constraint set is non-empty, the
infimum value `rateDistortionFunctionPmf P_X d D` equals `mutualInfoPmf qStar` at
the minimizer. -/
theorem rateDistortionFunctionPmf_eq_min
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ)
    (h_ne : (RDConstraint P_X d D).Nonempty) :
    ∃ qStar ∈ RDConstraint P_X d D,
      rateDistortionFunctionPmf P_X d D = mutualInfoPmf qStar := by
  obtain ⟨qStar, hqStar_mem, hqStar_min⟩ :=
    rateDistortionFunctionPmf_attained P_X d D h_ne
  refine ⟨qStar, hqStar_mem, ?_⟩
  -- sInf (image f S) = f qStar where qStar attains min on S.
  unfold rateDistortionFunctionPmf
  have h_bdd : BddBelow (Set.image mutualInfoPmf (RDConstraint P_X d D)) :=
    ((RDConstraint_isCompact P_X d D).image continuous_mutualInfoPmf).bddBelow
  apply le_antisymm
  · -- sInf ≤ f qStar (qStar in image)
    exact csInf_le h_bdd ⟨qStar, hqStar_mem, rfl⟩
  · -- f qStar ≤ sInf: f qStar is a lower bound on the image.
    refine le_csInf (h_ne.image _) ?_
    rintro v ⟨q, hq, rfl⟩
    exact hqStar_min hq

/-! ## Witness for non-emptyness: 単純 reconstruction `q(a,b) = P_X(a) · 𝟙[b = b₀]` -/

section Witness

variable [DecidableEq β]

/-- For a chosen reconstruction symbol `b₀ : β` and `P_X ∈ stdSimplex ℝ α`,
the **deterministic-reconstruction witness** `wit P_X b₀ (a, b) := if b = b₀ then P_X a else 0`
is in the stdSimplex `α × β`, has `marginalFst = P_X`, and yields
`expectedDistortionPmf d wit = ∑ a, P_X a · d(a, b₀)`. -/
noncomputable def detReconstructionWitness
    (P_X : α → ℝ) (b₀ : β) : α × β → ℝ :=
  fun p => if p.2 = b₀ then P_X p.1 else 0

/-- `detReconstructionWitness` is in the standard simplex on `α × β`
(provided `P_X ∈ stdSimplex ℝ α`). -/
lemma detReconstructionWitness_mem_stdSimplex
    (P_X : α → ℝ) (hP_X : P_X ∈ stdSimplex ℝ α) (b₀ : β) :
    detReconstructionWitness P_X b₀ ∈ stdSimplex ℝ (α × β) := by
  refine ⟨?_, ?_⟩
  · intro p
    unfold detReconstructionWitness
    split_ifs with h
    · exact hP_X.1 p.1
    · exact le_refl 0
  · -- ∑ p, witness p = ∑ a, ∑ b, witness (a, b) = ∑ a, P_X a = 1
    rw [Fintype.sum_prod_type]
    have h_inner : ∀ a, ∑ b, detReconstructionWitness P_X b₀ (a, b) = P_X a := by
      intro a
      unfold detReconstructionWitness
      simp only
      rw [Finset.sum_ite_eq' Finset.univ b₀ (fun _ => P_X a)]
      simp
    simp_rw [h_inner]
    exact hP_X.2

/-- `marginalFst` of the deterministic-reconstruction witness is `P_X`. -/
lemma marginalFst_detReconstructionWitness
    (P_X : α → ℝ) (b₀ : β) :
    marginalFst (detReconstructionWitness P_X b₀) = P_X := by
  funext a
  unfold marginalFst detReconstructionWitness
  simp only
  rw [Finset.sum_ite_eq' Finset.univ b₀ (fun _ => P_X a)]
  simp

/-- Expected distortion of the deterministic-reconstruction witness is
`∑ a, P_X a · d(a, b₀)`. -/
lemma expectedDistortionPmf_detReconstructionWitness
    (P_X : α → ℝ) (d : DistortionFn α β) (b₀ : β) :
    expectedDistortionPmf d (detReconstructionWitness P_X b₀)
      = ∑ a, P_X a * ((d a b₀ : NNReal) : ℝ) := by
  unfold expectedDistortionPmf detReconstructionWitness
  simp only
  refine Finset.sum_congr rfl fun a _ => ?_
  -- ∑ b, (if b = b₀ then P_X a else 0) * d(a,b) = P_X a * d(a, b₀)
  have h_inner : ∀ b, (if b = b₀ then P_X a else (0 : ℝ)) * ((d a b : NNReal) : ℝ)
        = if b = b₀ then P_X a * ((d a b : NNReal) : ℝ) else 0 := by
    intro b
    split_ifs with hb
    · rfl
    · ring
  rw [Finset.sum_congr rfl (fun b _ => h_inner b)]
  rw [Finset.sum_ite_eq' Finset.univ b₀
    (fun b => P_X a * ((d a b : NNReal) : ℝ))]
  simp

/-- **Non-emptyness of `RDConstraint`** via deterministic-reconstruction witness:
if `P_X ∈ stdSimplex` and some `b₀ : β` satisfies
`∑ a, P_X a · d(a, b₀) ≤ D`, then `RDConstraint P_X d D` is non-empty. -/
lemma RDConstraint_nonempty_of_witness
    (P_X : α → ℝ) (hP_X : P_X ∈ stdSimplex ℝ α) (d : DistortionFn α β)
    (D : ℝ) (b₀ : β)
    (h_bound : ∑ a, P_X a * ((d a b₀ : NNReal) : ℝ) ≤ D) :
    (RDConstraint P_X d D).Nonempty :=
  ⟨detReconstructionWitness P_X b₀,
    detReconstructionWitness_mem_stdSimplex P_X hP_X b₀,
    marginalFst_detReconstructionWitness P_X b₀,
    by
      rw [expectedDistortionPmf_detReconstructionWitness]
      exact h_bound⟩

end Witness

/-! ## Phase A 単調性 (antitone in `D`) -/

/-- `RDConstraint` is monotone in `D`: enlarging the distortion budget gives
a larger feasible set. -/
lemma RDConstraint_mono (P_X : α → ℝ) (d : DistortionFn α β)
    {D₁ D₂ : ℝ} (h : D₁ ≤ D₂) :
    RDConstraint P_X d D₁ ⊆ RDConstraint P_X d D₂ := by
  intro q hq
  refine ⟨hq.1, hq.2.1, ?_⟩
  exact le_trans hq.2.2 h

/-- **Antitonicity** of `rateDistortionFunctionPmf` in `D` (no boundedness side
condition required: when `RDConstraint P_X d D₁` is non-empty, all subsequent iInfs
over the larger feasible set are bounded by the same `mutualInfoPmf` evaluations).

We package this in the standard `D₁ ≤ D₂ ⟹ R(D₂) ≤ R(D₁)` form. -/
lemma rateDistortionFunctionPmf_antitone
    (P_X : α → ℝ) (d : DistortionFn α β)
    {D₁ D₂ : ℝ} (h : D₁ ≤ D₂)
    (h_ne₁ : (RDConstraint P_X d D₁).Nonempty) :
    rateDistortionFunctionPmf P_X d D₂ ≤ rateDistortionFunctionPmf P_X d D₁ := by
  -- For the conditionally-complete-lattice iInf, antitone in the index set needs
  -- BddBelow of the larger iInf set. We bound below by 0 via mutualInfo nonneg
  -- (no nonneg lemma yet, but for the inequality we use the direct argument:
  --  every q ∈ RDConstraint D₁ is in RDConstraint D₂, so iInf over D₂ ≤ value at
  --  that q, hence ≤ iInf over D₁).
  -- With `rateDistortionFunctionPmf := sInf (mutualInfoPmf '' RDConstraint)`,
  -- antitonicity is direct via `csInf_le_csInf`.
  unfold rateDistortionFunctionPmf
  have hS₁_sub_S₂ : RDConstraint P_X d D₁ ⊆ RDConstraint P_X d D₂ :=
    RDConstraint_mono P_X d h
  have h_image_sub :
      Set.image mutualInfoPmf (RDConstraint P_X d D₁)
        ⊆ Set.image mutualInfoPmf (RDConstraint P_X d D₂) :=
    Set.image_mono hS₁_sub_S₂
  have h_image₁_ne : (Set.image mutualInfoPmf (RDConstraint P_X d D₁)).Nonempty :=
    h_ne₁.image _
  have h_bdd_below_image₂ :
      BddBelow (Set.image mutualInfoPmf (RDConstraint P_X d D₂)) :=
    ((RDConstraint_isCompact P_X d D₂).image continuous_mutualInfoPmf).bddBelow
  exact csInf_le_csInf h_bdd_below_image₂ h_image₁_ne h_image_sub

end PmfForm

end InformationTheory.Shannon
