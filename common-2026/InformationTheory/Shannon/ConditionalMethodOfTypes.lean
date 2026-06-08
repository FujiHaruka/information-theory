import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.StrongTypicality
import InformationTheory.Shannon.Sanov.LDPEquality
import InformationTheory.Shannon.TypeClassLowerBound
import InformationTheory.Shannon.RateDistortionAchievabilityPhaseEStrong

/-!
# Conditional method of types — `conditionalStronglyTypicalSlice_mass_ge`

タスク: rate-distortion strong achievability (Phase 3) を unblock するための
**Cover-Thomas 10.6.1 (method-of-types, conditional form)** publishable form。

For a fixed X-strongly-typical `x : Fin n → α`, lower-bound the Y-product mass of
the conditional strongly-typical slice
`{y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε}` under `μ_Y^n`:

  `exp(-n · (entropy μ (Z₀) - entropy μ (X₀) + slack))
     ≤ (Measure.pi (μ.map (Ys 0))^n).real (conditionalStronglyTypicalSlice ...)`

ここで `entropy μ Z₀ - entropy μ X₀ = H(Y|X)` (条件付きエントロピー、joint - marginal
の chain-rule 形)、`slack = O(ε)`。

## 戦略

直接の経路 (Cover-Thomas 10.6.1) は **conditional type-class** を中心にした multinomial
counting。本ファイルは Phase A-E の inventory を確立 (定義 + 関連補題)。
最終 Phase E の per-x deterministic bound は次セッションでの assembly target として
statement のみ publish (sorry で残す)。

## 設計判断

* Final form expresses `H(Y|X)` as `entropy μ Z₀ - entropy μ X₀` (the chain-rule form),
  which is what the inventory comment in `RateDistortionAchievabilityPhaseEStrong.lean`
  promises and what downstream (rate-distortion achievability assembly) consumes.
* Avoids `mutualInfoOfChannel` reshape — that bridge is a separate concern.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Real Filter
open InformationTheory.Shannon.ChannelCoding
  (jointSequence jointSequence_apply measurable_jointSequence)
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-! ## Phase A — Conditional type-class basics + joint type bridge -/

/-- **Conditional type class.** Sequences `y : Fin n → β` whose joint type with
the fixed X-block `x` equals the count vector `c : α × β → ℕ`. -/
def conditionalTypeClass {n : ℕ} (x : Fin n → α) (c : α × β → ℕ) :
    Set (Fin n → β) :=
  { y | ∀ a b, (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card = c (a, b) }

lemma conditionalTypeClass_finite {n : ℕ} (x : Fin n → α) (c : α × β → ℕ) :
    (conditionalTypeClass (β := β) x c).Finite :=
  Set.toFinite _

/-- **Membership bridge to joint type-class.** `y ∈ conditionalTypeClass x c` iff
the joint sequence `i ↦ (x i, y i)` lies in `typeClassByCount c` on `α × β`. -/
lemma mem_conditionalTypeClass_iff_joint {n : ℕ} (x : Fin n → α) (c : α × β → ℕ)
    (y : Fin n → β) :
    y ∈ conditionalTypeClass x c ↔
      (fun i => (x i, y i)) ∈ typeClassByCount (α := α × β) (n := n) c := by
  classical
  constructor
  · intro h p
    obtain ⟨a, b⟩ := p
    have h_eq : (Finset.univ.filter (fun i : Fin n => (x i, y i) = (a, b))).card
        = (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card := by
      congr 1
      ext i
      simp [Prod.mk.injEq]
    show typeCount (fun i => (x i, y i)) (a, b) = c (a, b)
    unfold typeCount
    rw [h_eq]
    exact h a b
  · intro h a b
    have h_p := h (a, b)
    show (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card = c (a, b)
    have h_eq : (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card
        = (Finset.univ.filter (fun i : Fin n => (x i, y i) = (a, b))).card := by
      congr 1
      ext i
      simp [Prod.mk.injEq]
    rw [h_eq]
    unfold typeCount at h_p
    exact h_p

/-! ## Phase B — Marginal sums of joint type -/

/-- **X-marginal recovery.** If `y ∈ conditionalTypeClass x c`, then for each `a`,
`∑ b, c (a, b) = typeCount x a`. -/
@[entry_point]
lemma conditionalTypeClass_xMarginal {n : ℕ} (x : Fin n → α) (c : α × β → ℕ)
    {y : Fin n → β} (hy : y ∈ conditionalTypeClass x c) (a : α) :
    (∑ b : β, c (a, b)) = typeCount x a := by
  classical
  have h_each : ∀ b, c (a, b)
      = (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card :=
    fun b => (hy a b).symm
  have h_sum :
      (∑ b : β, (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card)
        = (Finset.univ.filter (fun i : Fin n => x i = a)).card := by
    have h_partition : (Finset.univ.filter (fun i : Fin n => x i = a))
        = (Finset.univ : Finset β).biUnion (fun b =>
            Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      refine ⟨fun h_xi => ⟨y i, h_xi, rfl⟩, ?_⟩
      rintro ⟨b, h_xi, _⟩
      exact h_xi
    have h_disjoint :
        ((Finset.univ : Finset β) : Set β).PairwiseDisjoint (fun b =>
          Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)) := by
      intro b₁ _ b₂ _ hb
      refine Finset.disjoint_filter.mpr ?_
      intro i _ ⟨_, hb₁⟩ ⟨_, hb₂⟩
      apply hb
      rw [← hb₁, hb₂]
    rw [h_partition, Finset.card_biUnion h_disjoint]
  rw [show (∑ b : β, c (a, b)) =
        ∑ b : β, (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card from
        Finset.sum_congr rfl fun b _ => h_each b]
  rw [h_sum]
  rfl

/-! ## Phase C — Slice partition by joint type -/

/-- **Slice partition indices.** Count vectors `c : α × β → Fin (n+1)` whose
empirical type is within `ε` of `qZ := μ.map (jointSequence Xs Ys 0)`. -/
noncomputable def sliceTypeIndices (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) : Finset (TypeCountIndex (α × β) n) := by
  classical
  exact (Finset.univ : Finset (TypeCountIndex (α × β) n)).filter (fun c =>
    ∀ p : α × β, |((c p : ℕ) : ℝ) / n - (μ.map (jointSequence Xs Ys 0)).real {p}| ≤ ε)

/-- Slice = union of conditional type classes over consistent indices. -/
lemma conditionalStronglyTypicalSlice_eq_biUnion
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    conditionalStronglyTypicalSlice μ Xs Ys n ε x
      = ⋃ c ∈ sliceTypeIndices μ Xs Ys n ε,
          conditionalTypeClass (β := β) x (fun p => (c p : ℕ)) := by
  classical
  ext y
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hy
    rw [mem_conditionalStronglyTypicalSlice_iff] at hy
    rw [mem_jointStronglyTypicalSet_iff] at hy
    rw [mem_stronglyTypicalSet_iff] at hy
    set z : Fin n → α × β := fun i => (x i, y i) with hz_def
    refine ⟨fun p => ⟨typeCount z p, ?_⟩, ?_, ?_⟩
    · -- typeCount z p ≤ n
      unfold typeCount
      have h1 : (Finset.univ.filter (fun i : Fin n => z i = p)).card ≤
          (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    · -- c ∈ sliceTypeIndices
      unfold sliceTypeIndices
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro p
      exact hy p
    · -- y ∈ conditionalTypeClass x (fun p => (c p : ℕ))
      rw [mem_conditionalTypeClass_iff_joint]
      intro p
      rfl
  · rintro ⟨c, hc_mem, hy⟩
    unfold sliceTypeIndices at hc_mem
    have hc_close := (Finset.mem_filter.mp hc_mem).2
    rw [mem_conditionalTypeClass_iff_joint] at hy
    rw [mem_conditionalStronglyTypicalSlice_iff]
    rw [mem_jointStronglyTypicalSet_iff]
    rw [mem_stronglyTypicalSet_iff]
    intro p
    have h_eq : typeCount (fun i => (x i, y i)) p = (c p : ℕ) := hy p
    rw [show ((typeCount (fun i => (x i, y i)) p : ℕ) : ℝ) = ((c p : ℕ) : ℝ) from by
        exact_mod_cast congrArg (Nat.cast (R := ℝ)) h_eq]
    exact hc_close p

/-! ## Phase D — Slice cardinality (polynomial number of joint types) -/

/-! ## Phase E — Per-fiber slice mass lower bound (main theorem)

**Status (final)**: Phases E.1–E.4 + main assembly **0 sorry**. The entropy-
concentration helper `conditional_KL_concentration_ge` is discharged via the
χ²-style KL upper bound and Archimedean N-choice for the three vanishing slack
terms (`log(n+1)/n → 0`, `1/n → 0`, and the constant Lipschitz amplification).

The Phase E inventory established here (`floorMatrix` + `floorMatrix_row_sum` +
`floorMatrix_total` + `productMass_eq_columnProd` + `conditionalTypeClass_card_ge`
+ `conditionalStronglyTypicalSlice_mass_ge` assembly) is the publishable
Cover-Thomas 10.6.1 form for downstream consumers.

### Note on the entropy form

Some prior inventory comments (e.g. `RateDistortionAchievabilityPhaseEStrong.lean`)
described the bound as `exp(-n · (H(Z) - H(X) + slack)) = exp(-n · (H(Y|X) + slack))`.
That paraphrase is **incorrect**: when `X = Y` deterministically (a degenerate
but legal case), `H(Y|X) = 0` so the paraphrased bound demands `mass ≥ exp(-n·slack)
≈ 1`, but the actual mass is `≈ exp(-n · H(X))`. The correct form (used here)
is `exp(-n · I(X;Y))`, which yields `mass ≥ exp(-n·H(X)) · poly(n)⁻¹` in that
case (consistent with the truth). -/

/-! ### Phase E.1 — Floor matrix construction

We construct an integer joint count `floorMatrix x` such that
* Row sums match `typeCount x` (so the conditional class is nonempty).
* Total is `n`.
* Each entry is within `ε_X + |β|/n` of `n · qZ` when `x` is X-strongly typical
  and the X-marginal of `qZ` matches `qX`.

The construction proceeds per-row: for each `a`, distribute `typeCount x a` over
`β` proportionally to the conditional `qZ(a, ·)/qX_from_Z(a)`, using the absorber-
letter rounding scheme. -/

/-- Absorber letter for the per-row rounding. -/
private noncomputable def absorberLetterβ (β : Type*) [Nonempty β] : β :=
  Classical.choice (inferInstance : Nonempty β)

/-- **Per-row floor** for splitting `typeCount x a` over `β` proportionally
to `qZ(a, ·) / qX_from_Z(a)`. -/
noncomputable def floorMatrix
    (qZ : α × β → ℝ) {n : ℕ} (x : Fin n → α) (a : α) (b : β) : ℕ :=
  let b₀ := absorberLetterβ β
  let qXa : ℝ := ∑ b' : β, qZ (a, b')
  if b = b₀ then
    typeCount x a -
      ∑ b' ∈ Finset.univ.erase b₀,
        Nat.floor ((typeCount x a : ℝ) * (qZ (a, b') / qXa))
  else
    min (Nat.floor ((typeCount x a : ℝ) * (qZ (a, b) / qXa))) (typeCount x a)

/-- **Sum of off-absorber floor entries ≤ typeCount x a** when qZ row is a sub-probability. -/
private lemma sum_floorMatrix_erase_le
    (qZ : α × β → ℝ) (hqZ_nn : ∀ p, 0 ≤ qZ p)
    {n : ℕ} (x : Fin n → α) (a : α) :
    (∑ b' ∈ Finset.univ.erase (absorberLetterβ β),
        Nat.floor ((typeCount x a : ℝ)
          * (qZ (a, b') / ∑ b'' : β, qZ (a, b''))))
      ≤ typeCount x a := by
  classical
  set qXa : ℝ := ∑ b'' : β, qZ (a, b'') with hqXa_def
  have hqXa_nn : 0 ≤ qXa := Finset.sum_nonneg fun b'' _ => hqZ_nn (a, b'')
  -- Each summand is ≤ (typeCount x a : ℝ) · (qZ(a,b')/qXa); sum ≤ (typeCount x a) · 1 = typeCount x a.
  have h_real_le :
      (∑ b' ∈ Finset.univ.erase (absorberLetterβ β),
          ((Nat.floor ((typeCount x a : ℝ)
            * (qZ (a, b') / qXa))) : ℝ))
        ≤ (typeCount x a : ℝ) := by
    by_cases hqXa_zero : qXa = 0
    · -- qXa = 0: each qZ(a,b'') = 0 (since nonneg sum to 0), so each term = 0.
      have h_each_zero : ∀ b' ∈ (Finset.univ : Finset β).erase (absorberLetterβ β),
          ((Nat.floor ((typeCount x a : ℝ)
            * (qZ (a, b') / qXa))) : ℝ) = 0 := by
        intro b' _
        rw [hqXa_zero, div_zero, mul_zero, Nat.floor_zero, Nat.cast_zero]
      rw [Finset.sum_congr rfl h_each_zero, Finset.sum_const_zero]
      exact Nat.cast_nonneg _
    have hqXa_pos : 0 < qXa := lt_of_le_of_ne hqXa_nn (Ne.symm hqXa_zero)
    calc (∑ b' ∈ Finset.univ.erase (absorberLetterβ β),
          ((Nat.floor ((typeCount x a : ℝ)
            * (qZ (a, b') / qXa))) : ℝ))
        ≤ ∑ b' ∈ Finset.univ.erase (absorberLetterβ β),
              ((typeCount x a : ℝ) * (qZ (a, b') / qXa)) := by
          refine Finset.sum_le_sum fun b' _ => ?_
          refine Nat.floor_le ?_
          exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hqZ_nn _) hqXa_nn)
      _ = (typeCount x a : ℝ) *
            (∑ b' ∈ Finset.univ.erase (absorberLetterβ β), qZ (a, b') / qXa) := by
          rw [← Finset.mul_sum]
      _ ≤ (typeCount x a : ℝ) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have h_sum_le : (∑ b' ∈ Finset.univ.erase (absorberLetterβ β), qZ (a, b') / qXa)
              ≤ ∑ b' : β, qZ (a, b') / qXa := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
            intros b' _ _; exact div_nonneg (hqZ_nn _) hqXa_nn
          have h_full : (∑ b' : β, qZ (a, b') / qXa) = 1 := by
            rw [← Finset.sum_div]
            -- ∑ b', qZ (a, b') = qXa
            have h_eq : (∑ b' : β, qZ (a, b')) = qXa := hqXa_def.symm
            rw [h_eq]
            exact div_self hqXa_pos.ne'
          linarith
      _ = (typeCount x a : ℝ) := by ring
  exact_mod_cast h_real_le

/-- **Row-sum preservation**: `∑ b, floorMatrix qZ x a b = typeCount x a` when qZ ≥ 0. -/
lemma floorMatrix_row_sum
    (qZ : α × β → ℝ) (hqZ_nn : ∀ p, 0 ≤ qZ p)
    {n : ℕ} (x : Fin n → α) (a : α) :
    (∑ b : β, floorMatrix qZ x a b) = typeCount x a := by
  classical
  set b₀ := absorberLetterβ β with hb₀_def
  set S : ℕ := ∑ b' ∈ Finset.univ.erase b₀,
      Nat.floor ((typeCount x a : ℝ)
        * (qZ (a, b') / ∑ b'' : β, qZ (a, b''))) with hS_def
  have hS_le : S ≤ typeCount x a := sum_floorMatrix_erase_le qZ hqZ_nn x a
  -- Split the sum at b = b₀.
  rw [← Finset.sum_erase_add (Finset.univ : Finset β) _ (Finset.mem_univ b₀)]
  have h_abs : floorMatrix qZ x a b₀ = typeCount x a - S := by
    unfold floorMatrix
    dsimp only
    rw [if_pos rfl]
  -- For b' ≠ b₀, floorMatrix qZ x a b' = min (Nat.floor ...) (typeCount x a).
  -- We need to show that = Nat.floor ... (i.e., the min isn't truncating).
  have h_off : ∀ b' ∈ (Finset.univ : Finset β).erase b₀,
      floorMatrix qZ x a b'
        = Nat.floor ((typeCount x a : ℝ)
            * (qZ (a, b') / ∑ b'' : β, qZ (a, b''))) := by
    intro b' hb'
    have hb'_ne : b' ≠ b₀ := (Finset.mem_erase.mp hb').1
    unfold floorMatrix
    dsimp only
    rw [if_neg hb'_ne]
    -- min (Nat.floor ...) (typeCount x a) = Nat.floor ... since each summand ≤ S ≤ typeCount x a
    have h_each_le : Nat.floor ((typeCount x a : ℝ)
        * (qZ (a, b') / ∑ b'' : β, qZ (a, b'')))
        ≤ typeCount x a := by
      have h_one := Finset.single_le_sum (f := fun b'' =>
        Nat.floor ((typeCount x a : ℝ) * (qZ (a, b'') / ∑ b''' : β, qZ (a, b'''))))
        (fun _ _ => Nat.zero_le _) hb'
      exact le_trans h_one hS_le
    exact min_eq_left h_each_le
  rw [Finset.sum_congr rfl h_off]
  rw [show (∑ b' ∈ (Finset.univ : Finset β).erase b₀,
        Nat.floor ((typeCount x a : ℝ)
          * (qZ (a, b') / ∑ b'' : β, qZ (a, b''))))
      = S from rfl]
  rw [h_abs]
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel hS_le

/-- **Total**: `∑ p, floorMatrix qZ x p.1 p.2 = n` when qZ ≥ 0. -/
lemma floorMatrix_total (qZ : α × β → ℝ) (hqZ_nn : ∀ p, 0 ≤ qZ p)
    {n : ℕ} (x : Fin n → α) :
    (∑ p : α × β, floorMatrix qZ x p.1 p.2) = n := by
  classical
  have h_split : (∑ p : α × β, floorMatrix qZ x p.1 p.2)
      = ∑ a : α, ∑ b : β, floorMatrix qZ x a b := by
    rw [← Finset.sum_product']
    rfl
  rw [h_split]
  rw [Finset.sum_congr rfl (fun a _ => floorMatrix_row_sum qZ hqZ_nn x a)]
  -- ∑ a, typeCount x a = n (standard).
  unfold typeCount
  have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      x i ∈ (Finset.univ : Finset α) := fun _ _ => Finset.mem_univ _
  have h_fiber := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset α)) h_maps (fun _ : Fin n => (1 : ℕ))
  have h_card : ∀ a : α,
      ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card
        = ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i => x i = a), (1 : ℕ) := by
    intro a
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  rw [show (∑ a : α, ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card)
        = ∑ a : α, ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i => x i = a), (1 : ℕ)
      from Finset.sum_congr rfl fun a _ => h_card a]
  rw [h_fiber]
  simp

/-- **Joint type close to qZ**: For `x` X-strongly-typical at slack `ε_X` with
matching X-marginals, each entry of `floorMatrix qZ x` satisfies
`|floorMatrix x a b / n - qZ(a,b)| ≤ ε_X + |β|/n`.

**Status**: scaffolded but proof not completed in this session. The proof goes:
* `c(a,b)/n - qZ(a,b) = (c(a,b)/n - (T_a/n)·(qZ(a,b)/qXa)) + (T_a/n - qXa)·(qZ(a,b)/qXa)`
  where `T_a = typeCount x a` and `qXa = ∑ b', qZ(a,b')`.
* First term: floor error, bounded by `|β|/n`.
* Second term: bounded by `ε_X` using `hx` (X-strong-typical) and `hmarg_X` (qXa = qX(a)). -/
lemma floorMatrix_dist_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    {n : ℕ} (hn : 0 < n) {ε_X : ℝ} (hε_X : 0 ≤ ε_X)
    (x : Fin n → α) (hx : x ∈ stronglyTypicalSet μ Xs n ε_X) (a : α) (b : β) :
    |((floorMatrix (fun p => (μ.map (jointSequence Xs Ys 0)).real {p}) x a b : ℕ) : ℝ) / n
        - (μ.map (jointSequence Xs Ys 0)).real {(a, b)}|
      ≤ ε_X + (Fintype.card β : ℝ) / n := by
  classical
  set qZ : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
  set qX : α → ℝ := fun a' => (μ.map (Xs 0)).real {a'} with hqX_def
  have hqZ_nn : ∀ p, 0 ≤ qZ p := fun p => (hposZ p).le
  set qXa : ℝ := ∑ b' : β, qZ (a, b') with hqXa_def
  have hqXa_pos : 0 < qXa := by
    -- qXa is a sum of strictly-positive terms over a nonempty type.
    refine Finset.sum_pos (fun b' _ => hposZ (a, b')) ?_
    exact Finset.univ_nonempty
  have hqXa_nn : 0 ≤ qXa := hqXa_pos.le
  -- X-marginal identification: qXa = qX a.
  have h_qXa_eq : qXa = qX a := by
    have h_pre : (Prod.fst ⁻¹' ({a} : Set α) : Set (α × β))
        = ⋃ b' ∈ (Finset.univ : Finset β), ({(a, b')} : Set (α × β)) := by
      ext ⟨x', y'⟩
      constructor
      · intro hx'
        have : x' = a := hx'
        subst this
        refine Set.mem_iUnion.mpr ⟨y', Set.mem_iUnion.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      · intro hx'
        rcases Set.mem_iUnion.mp hx' with ⟨b', hb'⟩
        rcases Set.mem_iUnion.mp hb' with ⟨_, hb''⟩
        simp only [Set.mem_singleton_iff] at hb''
        simp [Set.mem_preimage, hb'']
    have h_map : ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a}
        = (μ.map (jointSequence Xs Ys 0)).real (Prod.fst ⁻¹' {a}) :=
      map_measureReal_apply measurable_fst (MeasurableSet.singleton a)
    have h_qX_eq : ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a} = qX a := by
      rw [hmarg_X]
    have h_disj : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint
        (fun b' => ({(a, b')} : Set (α × β))) := by
      intro b₁ _ b₂ _ hb s hs1 hs2 p hp
      have hp1 := hs1 hp
      have hp2 := hs2 hp
      simp only [Set.mem_singleton_iff] at hp1 hp2
      have heq : (a, b₁) = (a, b₂) := hp1.symm.trans hp2
      exact (hb (Prod.mk.injEq _ _ _ _ |>.mp heq).2).elim
    have h_meas : ∀ b' ∈ (Finset.univ : Finset β),
        MeasurableSet ({(a, b')} : Set (α × β)) := fun _ _ => measurableSet_singleton _
    have h_sum : (μ.map (jointSequence Xs Ys 0)).real (Prod.fst ⁻¹' {a})
        = ∑ b' : β, qZ (a, b') := by
      rw [h_pre]
      rw [measureReal_biUnion_finset h_disj h_meas]
    rw [← h_qX_eq, h_map, h_sum]
  -- typeCount x a / n - qX a slack bound from X-strong typicality.
  have hx_slack : |(typeCount x a : ℝ) / n - qX a| ≤ ε_X := hx a
  set Ta : ℕ := typeCount x a with hTa_def
  have hTa_nn : (0 : ℝ) ≤ (Ta : ℝ) := Nat.cast_nonneg _
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Ratio r(b) := qZ(a,b) / qXa; r ≥ 0, ∑ r = 1.
  set r : β → ℝ := fun b' => qZ (a, b') / qXa with hr_def
  have hr_nn : ∀ b', 0 ≤ r b' := fun b' => div_nonneg (hqZ_nn _) hqXa_nn
  have hr_le_one : ∀ b', r b' ≤ 1 := by
    intro b'
    rw [hr_def]
    rw [div_le_one hqXa_pos]
    -- qZ(a,b') ≤ ∑ b'', qZ(a,b'') = qXa
    exact Finset.single_le_sum (f := fun b'' => qZ (a, b''))
      (fun b'' _ => hqZ_nn _) (Finset.mem_univ b')
  -- (T_a / n - qXa) * r(b) bound: ≤ ε_X (since |r| ≤ 1).
  have h_slack_mul : ∀ b', |((Ta : ℝ) / n - qXa) * r b'| ≤ ε_X := by
    intro b'
    rw [abs_mul]
    have h_abs_r : |r b'| = r b' := abs_of_nonneg (hr_nn b')
    rw [h_abs_r]
    have h_slack : |(Ta : ℝ) / n - qXa| ≤ ε_X := by
      rw [h_qXa_eq]; exact hx_slack
    calc |(Ta : ℝ) / n - qXa| * r b'
        ≤ ε_X * r b' := by
          refine mul_le_mul_of_nonneg_right h_slack (hr_nn b')
      _ ≤ ε_X * 1 := by
          refine mul_le_mul_of_nonneg_left (hr_le_one b') hε_X
      _ = ε_X := by ring
  -- Floor inequalities: for any nonneg r ≥ 0, T_a · r - 1 < floor(T_a · r) ≤ T_a · r.
  have h_floor_le : ∀ b',
      (Nat.floor ((Ta : ℝ) * r b') : ℝ) ≤ (Ta : ℝ) * r b' := by
    intro b'
    exact Nat.floor_le (by exact mul_nonneg hTa_nn (hr_nn b'))
  have h_floor_lt_succ : ∀ b',
      (Ta : ℝ) * r b' < (Nat.floor ((Ta : ℝ) * r b') : ℝ) + 1 :=
    fun b' => Nat.lt_floor_add_one _
  -- Helper bound: |c/n - qZ(a,b)| ≤ ε_X + 1/n when c = floor(T_a · r(b)) and b ≠ b₀.
  have h_off_bound : ∀ b' : β,
      |((Nat.floor ((Ta : ℝ) * r b') : ℕ) : ℝ) / n - qZ (a, b')|
        ≤ ε_X + 1 / n := by
    intro b'
    -- c/n - qZ(a,b) = (c/n - (T_a · r(b))/n) + ((T_a/n) · r(b) - qXa · r(b))
    --              = floor_err / n + (T_a/n - qXa) · r(b)
    -- with qZ(a,b) = qXa · r(b) (since qXa > 0).
    have h_qZ_eq : qZ (a, b') = qXa * r b' := by
      rw [hr_def]; field_simp
    rw [h_qZ_eq]
    -- Decompose.
    have h_decomp : ((Nat.floor ((Ta : ℝ) * r b') : ℕ) : ℝ) / n - qXa * r b'
        = ((Nat.floor ((Ta : ℝ) * r b') : ℝ) - (Ta : ℝ) * r b') / n
          + ((Ta : ℝ) / n - qXa) * r b' := by
      field_simp
      ring
    rw [h_decomp]
    refine (abs_add_le _ _).trans ?_
    have h1 : |((Nat.floor ((Ta : ℝ) * r b') : ℝ) - (Ta : ℝ) * r b') / n| ≤ 1 / n := by
      rw [abs_div, abs_of_pos hn_pos]
      apply div_le_div_of_nonneg_right _ hn_pos.le
      have h_lb : (Ta : ℝ) * r b' - 1 < (Nat.floor ((Ta : ℝ) * r b') : ℝ) := by
        linarith [h_floor_lt_succ b']
      have h_ub : (Nat.floor ((Ta : ℝ) * r b') : ℝ) ≤ (Ta : ℝ) * r b' := h_floor_le b'
      rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    have h2 := h_slack_mul b'
    linarith
  -- Distinguish b₀ vs b ≠ b₀.
  set b₀ : β := absorberLetterβ β with hb₀_def
  set S : ℕ := ∑ b' ∈ Finset.univ.erase b₀,
      Nat.floor ((Ta : ℝ) * r b') with hS_def
  have hS_le : S ≤ Ta := by
    have := sum_floorMatrix_erase_le (β := β) qZ hqZ_nn x a
    exact this
  by_cases hb : b = b₀
  · -- b = b₀: c = Ta - S. Need |(Ta - S)/n - qZ(a, b₀)| ≤ ε_X + |β|/n.
    subst hb
    have h_val : floorMatrix qZ x a b₀ = Ta - S := by
      unfold floorMatrix
      dsimp only
      rw [if_pos rfl]
    rw [show floorMatrix qZ x a b₀ = Ta - S from h_val]
    -- Cast: ((Ta - S : ℕ) : ℝ) = Ta - S since S ≤ Ta.
    rw [Nat.cast_sub hS_le]
    -- Fold (Measure.map …).real {(a, b₀)} = qZ (a, b₀).
    show |(↑Ta - (S : ℝ)) / ↑n - qZ (a, b₀)| ≤ ε_X + ↑(Fintype.card β) / ↑n
    -- (Ta - S)/n - qZ(a, b₀) = (Ta - S)/n - qXa · r(b₀)
    -- We use: ∑_{b'} r(b') = 1, i.e. r(b₀) = 1 - ∑_{b' ≠ b₀} r(b').
    have h_qZ_eq : qZ (a, b₀) = qXa * r b₀ := by
      rw [hr_def]; field_simp
    rw [h_qZ_eq]
    -- (Ta - S)/n - qXa · r(b₀)
    --   = Ta/n - qXa · r(b₀) - S/n
    --   = (Ta/n - qXa) + qXa · (1 - r(b₀)) - S/n        [if Ta/n + qXa · (1 - r) = Ta/n - qXa · r + qXa]
    --   = (Ta/n - qXa)·r(b₀) + (Ta/n)·(1 - r(b₀)) - S/n + (qXa - qXa)·... — let me redo
    -- Strategy: write as (Ta/n - qXa)·r(b₀) + (per-b' error sum) / n.
    -- Note ∑_b' r(b') = 1 means qXa · ∑ r = qXa, hence qXa · (1 - r(b₀)) = qXa · ∑_{b' ≠ b₀} r(b').
    have h_sum_r : (∑ b' : β, r b') = 1 := by
      rw [hr_def]
      rw [← Finset.sum_div]
      rw [show (∑ b' : β, qZ (a, b')) = qXa from rfl]
      field_simp
    have h_sum_r_split : (1 : ℝ) = r b₀ + ∑ b' ∈ Finset.univ.erase b₀, r b' := by
      rw [← h_sum_r]
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ b₀)).symm
    -- (Ta - S)/n - qXa · r(b₀)
    --   = (Ta/n) · 1 - qXa · r(b₀) - S/n
    --   = (Ta/n) · (r(b₀) + ∑_{b' ≠ b₀} r(b')) - qXa · r(b₀) - S/n
    --   = (Ta/n - qXa) · r(b₀) + (Ta/n) · ∑_{b' ≠ b₀} r(b') - S/n
    --   = (Ta/n - qXa) · r(b₀) + ∑_{b' ≠ b₀} ((Ta · r(b'))/n - (floor (Ta · r(b'))/n))
    --   = (Ta/n - qXa) · r(b₀) + (∑_{b' ≠ b₀} (Ta · r(b') - floor(...))) / n
    -- Each summand of the latter is in [0, 1), summed |β|-1 terms ≤ |β|-1 ≤ |β|.
    have h_decomp :
        ((Ta : ℝ) - (S : ℝ)) / n - qXa * r b₀
          = ((Ta : ℝ) / n - qXa) * r b₀
              + (∑ b' ∈ Finset.univ.erase b₀,
                  ((Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ))) / n := by
      have h_S_real : (S : ℝ)
          = ∑ b' ∈ Finset.univ.erase b₀, (Nat.floor ((Ta : ℝ) * r b') : ℝ) := by
        rw [hS_def]; push_cast; rfl
      rw [h_S_real]
      have h_Ta_r_sum : (Ta : ℝ) * r b₀ + ∑ b' ∈ Finset.univ.erase b₀, (Ta : ℝ) * r b'
          = (Ta : ℝ) := by
        have h_pull : ∑ b' ∈ Finset.univ.erase b₀, (Ta : ℝ) * r b'
            = (Ta : ℝ) * ∑ b' ∈ Finset.univ.erase b₀, r b' := by
          rw [Finset.mul_sum]
        rw [h_pull, ← mul_add]
        rw [Finset.add_sum_erase _ (fun b' => r b') (Finset.mem_univ b₀)]
        rw [h_sum_r, mul_one]
      have h_Ta_split : (Ta : ℝ)
          = (Ta : ℝ) * r b₀ + ∑ b' ∈ Finset.univ.erase b₀, (Ta : ℝ) * r b' := h_Ta_r_sum.symm
      rw [Finset.sum_sub_distrib]
      field_simp
      linarith [h_Ta_r_sum]
    rw [h_decomp]
    refine (abs_add_le _ _).trans ?_
    -- Bound first term by ε_X.
    have h_first := h_slack_mul b₀
    -- Bound second term by (|β| - 1)/n ≤ |β|/n.
    have h_each_nn : ∀ b' ∈ (Finset.univ : Finset β).erase b₀,
        0 ≤ (Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ) := by
      intro b' _; linarith [h_floor_le b']
    have h_each_lt : ∀ b' ∈ (Finset.univ : Finset β).erase b₀,
        (Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ) ≤ 1 := by
      intro b' _; linarith [h_floor_lt_succ b']
    have h_sum_nn :
        0 ≤ ∑ b' ∈ Finset.univ.erase b₀,
            ((Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ)) :=
      Finset.sum_nonneg h_each_nn
    have h_sum_le_card :
        (∑ b' ∈ Finset.univ.erase b₀,
            ((Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ)))
          ≤ ((Finset.univ : Finset β).erase b₀).card := by
      have h := Finset.sum_le_sum (s := ((Finset.univ : Finset β).erase b₀))
        (f := fun b' => (Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ))
        (g := fun _ => (1 : ℝ)) h_each_lt
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    have h_card_erase :
        ((Finset.univ : Finset β).erase b₀).card = Fintype.card β - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl
    have h_card_le : (((Finset.univ : Finset β).erase b₀).card : ℝ)
        ≤ (Fintype.card β : ℝ) := by
      rw [h_card_erase]
      exact_mod_cast Nat.sub_le _ _
    have h_second : |(∑ b' ∈ Finset.univ.erase b₀,
            ((Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ))) / n|
        ≤ (Fintype.card β : ℝ) / n := by
      rw [abs_div, abs_of_pos hn_pos]
      apply div_le_div_of_nonneg_right _ hn_pos.le
      rw [abs_of_nonneg h_sum_nn]
      exact h_sum_le_card.trans h_card_le
    linarith
  · -- b ≠ b₀: c = min(floor(...), Ta) = floor(...) [argument from row_sum proof].
    have h_val : floorMatrix qZ x a b
        = Nat.floor ((Ta : ℝ) * r b) := by
      unfold floorMatrix
      dsimp only
      rw [if_neg hb]
      -- min(floor, Ta) = floor since each summand ≤ S ≤ Ta. Use single ∈ erase b₀.
      have h_mem : b ∈ (Finset.univ : Finset β).erase b₀ :=
        Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
      have h_one := Finset.single_le_sum
        (f := fun b'' => Nat.floor ((Ta : ℝ) * r b''))
        (fun _ _ => Nat.zero_le _) h_mem
      have h_each_le : Nat.floor ((Ta : ℝ) * r b) ≤ Ta := h_one.trans hS_le
      rw [show min (Nat.floor ((typeCount x a : ℝ)
            * (qZ (a, b) / ∑ b'' : β, qZ (a, b'')))) (typeCount x a) =
              Nat.floor ((typeCount x a : ℝ)
                * (qZ (a, b) / ∑ b'' : β, qZ (a, b''))) from
        min_eq_left h_each_le]
    rw [h_val]
    have h_off := h_off_bound b
    -- ε_X + 1/n ≤ ε_X + |β|/n since |β| ≥ 1.
    have h_card_ge_one : (1 : ℝ) ≤ Fintype.card β := by
      have : (1 : ℕ) ≤ Fintype.card β := Fintype.card_pos
      exact_mod_cast this
    have h_div_mono : (1 : ℝ) / n ≤ (Fintype.card β : ℝ) / n :=
      div_le_div_of_nonneg_right h_card_ge_one hn_pos.le
    linarith

/-! ### Phase E.2 — Per-row multinomial cardinality

For the floor matrix, the conditional type class equals a product (over rows)
of per-row type classes on `β`, and we lower-bound its cardinality via the
per-row multinomial Stirling-free bound. -/

/-- **Bijection cardinality**: the conditional type class card equals
the product over `a` of per-row type class cards on `Fin (typeCount x a) → β`.

Construction: composition of three Equivs.
1. `e_fib : (Fin n → β) ≃ ∀ a, ({i // x i = a} → β)` (direct construction).
2. `e_card : ({i // x i = a} → β) ≃ (Fin (typeCount x a) → β)` via cardinality.
3. Transport the membership condition through these. -/
lemma conditionalTypeClass_card_eq_prod_typeClass
    {n : ℕ} (x : Fin n → α) (c : α × β → ℕ) :
    (∏ a : α, (typeClassByCount (α := β) (n := typeCount x a)
        (fun b => c (a, b))).toFinite.toFinset.card)
      = (conditionalTypeClass (β := β) x c).toFinite.toFinset.card := by
  classical
  set Ta : α → ℕ := fun a => typeCount x a with hTa_def
  -- Step 1: cardinality of subtype S a = Fin (Ta a).
  -- Build per-a equiv: ({i : Fin n // x i = a} ≃ Fin (Ta a)).
  have hcard_S : ∀ a : α,
      Fintype.card {i : Fin n // x i = a} = Ta a := by
    intro a
    -- {i : Fin n // x i = a} = filter (x i = a) Finset.univ
    have : Fintype.card {i : Fin n // x i = a}
        = (Finset.univ.filter (fun i : Fin n => x i = a)).card := by
      rw [Fintype.card_subtype]
    rw [this]
    rfl
  -- Pointwise card: card ({i // x i = a} → β) and card (Fin (Ta a) → β) all match.
  -- We don't construct the explicit Equiv; instead, we work via card_pi and Fintype.card_subtype.
  -- The conditionalTypeClass x c is in bijection with {y : Fin n → β // ∀ a, restr ∈ T_row a},
  -- which is in bijection with ∀ a, {g_a : (S a → β) // typeClass-condition}.
  -- We use Fintype.card_eq_of_equiv (Equiv-based card equality).
  -- Build the Equiv directly.
  set Sa : α → Type _ := fun a => {i : Fin n // x i = a} with hSa_def
  -- Equiv #1: (Fin n → β) ≃ (∀ a, Sa a → β).
  -- Direct construction via Equiv mk.
  let φ : (Fin n → β) ≃ (∀ a, Sa a → β) :=
    { toFun := fun y a i => y i.val
      invFun := fun g i => g (x i) ⟨i, rfl⟩
      left_inv := fun y => by funext i; rfl
      right_inv := fun g => by
        funext a i
        rcases i with ⟨k, hk⟩
        subst hk
        rfl }
  -- Check forward direction: φ y a ⟨i, hi⟩ = y i.
  have hφ_apply : ∀ (y : Fin n → β) (a : α) (i : Sa a), φ y a i = y i.val := by
    intros; rfl
  -- Build the constrained bijection.
  -- We use `Equiv.subtypeEquiv φ ...`.
  set P : (Fin n → β) → Prop :=
    fun y => ∀ a b, (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card = c (a, b)
  set Q : (∀ a, Sa a → β) → Prop :=
    fun g => ∀ a b, (Finset.univ.filter (fun i : Sa a => g a i = b)).card = c (a, b)
  -- Membership condition equivalence under φ.
  have hPQ : ∀ y, P y ↔ Q (φ y) := by
    intro y
    constructor
    · intro hP a b
      -- card {i : Sa a | φ y a i = b} = card {i : Sa a | y i.val = b}
      --   = card {i : Fin n | x i = a ∧ y i = b} = c (a, b)
      have h_filter_card :
          (Finset.univ.filter (fun i : Sa a => φ y a i = b)).card
            = (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card := by
        -- Bijection: i : Sa a (i.e. ⟨k, x k = a⟩) ↔ k : Fin n with x k = a ∧ y k = b.
        rw [show (Finset.univ.filter (fun i : Sa a => φ y a i = b))
              = (Finset.univ.filter (fun i : Sa a => y i.val = b))
            from Finset.filter_congr (fun i _ => by rw [hφ_apply])]
        -- Now use subtype filter card = filter on Fin n.
        apply Finset.card_bij
          (fun (i : Sa a) (_ : i ∈ Finset.univ.filter (fun i : Sa a => y i.val = b)) => i.val)
        · -- mapsTo
          intro i hi
          rcases Finset.mem_filter.mp hi with ⟨_, h_yb⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, h_yb⟩
          exact i.property
        · -- injective on
          intro i hi j hj heq
          exact Subtype.ext heq
        · -- surjective on
          intro k hk
          rcases Finset.mem_filter.mp hk with ⟨_, hxk_a, hyk_b⟩
          refine ⟨⟨k, hxk_a⟩, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk_b⟩
      rw [h_filter_card]
      exact hP a b
    · intro hQ a b
      have h_filter_card :
          (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card
            = (Finset.univ.filter (fun i : Sa a => φ y a i = b)).card := by
        rw [show (Finset.univ.filter (fun i : Sa a => φ y a i = b))
              = (Finset.univ.filter (fun i : Sa a => y i.val = b))
            from Finset.filter_congr (fun i _ => by rw [hφ_apply])]
        apply Finset.card_bij
          (fun (k : Fin n) (hk : k ∈ Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)) =>
            (⟨k, (Finset.mem_filter.mp hk).2.1⟩ : Sa a))
        · intro k hk
          rcases Finset.mem_filter.mp hk with ⟨_, _, h_yb⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_yb⟩
        · intro k₁ hk₁ k₂ hk₂ heq
          exact Subtype.ext_iff.mp heq
        · intro j hj
          rcases Finset.mem_filter.mp hj with ⟨_, h_yb⟩
          refine ⟨j.val, ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property, h_yb⟩
      rw [h_filter_card]; exact hQ a b
  -- ψ : {y // P y} ≃ {g // Q g}
  let ψ : {y // P y} ≃ {g // Q g} := φ.subtypeEquiv hPQ
  -- {g // Q g} ≃ ∀ a, {ga : Sa a → β // ∀ b, (filter ... ).card = c (a, b)}
  let χ : {g : ∀ a, Sa a → β // Q g} ≃
      ∀ a, {ga : Sa a → β // ∀ b, (Finset.univ.filter (fun i : Sa a => ga i = b)).card = c (a, b)} :=
    { toFun := fun g a => ⟨g.val a, fun b => g.property a b⟩
      invFun := fun g => ⟨fun a => (g a).val, fun a b => (g a).property b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  -- For each a, the subtype `{ga // ∀ b, count = c (a, b)}` is in bijection with
  -- `typeClassByCount (n := Ta a) (fun b => c (a, b))` on `Fin (Ta a) → β`,
  -- via the cardinality equiv Sa a ≃ Fin (Ta a).
  -- We construct the per-a equiv.
  let eSa : ∀ a, Sa a ≃ Fin (Ta a) := fun a =>
    Fintype.equivFinOfCardEq (hcard_S a)
  -- Helper: per-a filter card equality between Sa a and Fin (Ta a) via eSa.
  have h_filter_transport : ∀ a (ga : Sa a → β) (b : β),
      (Finset.univ.filter (fun j : Fin (Ta a) => ga ((eSa a).symm j) = b)).card
        = (Finset.univ.filter (fun i : Sa a => ga i = b)).card := by
    intros a ga b
    apply Finset.card_bij
      (fun (j : Fin (Ta a))
        (_ : j ∈ Finset.univ.filter (fun j : Fin (Ta a) => ga ((eSa a).symm j) = b)) =>
        (eSa a).symm j)
    · intro j hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (Finset.mem_filter.mp hj).2
    · intro j₁ _ j₂ _ heq
      exact (eSa a).symm.injective heq
    · intro i hi
      refine ⟨eSa a i, ?_, by simp⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact (Finset.mem_filter.mp hi).2
  -- θ a : per-row subtype ≃ typeClassByCount (Ta a, fun b => c (a, b)).
  let θ : ∀ a, {ga : Sa a → β // ∀ b, (Finset.univ.filter (fun i : Sa a => ga i = b)).card = c (a, b)}
      ≃ typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b)) := fun a =>
    { toFun := fun ga =>
        ⟨fun j => ga.val ((eSa a).symm j), by
          intro b
          show typeCount _ b = c (a, b)
          unfold typeCount
          rw [h_filter_transport a ga.val b]
          exact ga.property b⟩
      invFun := fun g =>
        ⟨fun i => g.val ((eSa a) i), by
          intro b
          have h : (Finset.univ.filter (fun j : Fin (Ta a) => g.val j = b)).card = c (a, b) :=
            g.property b
          -- want: (Finset.univ.filter (fun i : Sa a => g.val (eSa a i) = b)).card = c (a, b)
          rw [← h]
          apply Finset.card_bij
            (fun (i : Sa a)
              (_ : i ∈ Finset.univ.filter (fun i : Sa a => g.val (eSa a i) = b)) =>
              eSa a i)
          · intro i hi
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            exact (Finset.mem_filter.mp hi).2
          · intro i₁ _ i₂ _ heq
            exact (eSa a).injective heq
          · intro j hj
            refine ⟨(eSa a).symm j, ?_, by simp⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [Equiv.apply_symm_apply]
            exact (Finset.mem_filter.mp hj).2⟩
      left_inv := fun ga => by
        ext i
        show ga.val ((eSa a).symm (eSa a i)) = ga.val i
        rw [Equiv.symm_apply_apply]
      right_inv := fun g => by
        ext j
        show g.val ((eSa a) ((eSa a).symm j)) = g.val j
        rw [Equiv.apply_symm_apply] }
  -- Combine.
  let final : {y // P y} ≃
      ∀ a, typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b)) :=
    ψ.trans (χ.trans (Equiv.piCongrRight θ))
  -- Wrap as Fintype.card equalities. Attach Fintype instances for each per-row set.
  haveI hFinRow : ∀ a, Fintype
      (typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b))) :=
    fun a => (typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b))).toFinite.fintype
  -- ∀-Fintype is from the per-row instances.
  haveI : Fintype (∀ a, typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b))) :=
    Pi.instFintype
  -- per-row toFinset.card ↔ Fintype.card
  have h_per_card_eq : ∀ a,
      (typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b))).toFinite.toFinset.card
        = Fintype.card (typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b))) := by
    intro a; rw [(typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b))).toFinite.card_toFinset]
  -- LHS: ∏ a, toFinset.card  =  ∏ a, Fintype.card = Fintype.card (∀ a, ...).
  have h_LHS_eq : (∏ a : α, (typeClassByCount (α := β) (n := Ta a)
        (fun b => c (a, b))).toFinite.toFinset.card)
      = Fintype.card (∀ a, typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b))) := by
    rw [show (∏ a : α, (typeClassByCount (α := β) (n := Ta a)
          (fun b => c (a, b))).toFinite.toFinset.card)
        = ∏ a : α, Fintype.card (typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b)))
        from Finset.prod_congr rfl (fun a _ => h_per_card_eq a)]
    -- Fintype.card_pi: card (∀ a, X a) = ∏ a, card (X a)
    convert (Fintype.card_pi (ι := α)
      (α := fun a => typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b)))).symm using 2
  rw [h_LHS_eq]
  -- Fintype.card (∀ a, T_row a) = Fintype.card {y // P y} via final.
  have h_card_eq : Fintype.card (∀ a, typeClassByCount (α := β) (n := Ta a) (fun b => c (a, b)))
      = Fintype.card {y // P y} :=
    (Fintype.card_congr final).symm
  rw [h_card_eq]
  -- Fintype.card {y // P y} = card (conditionalTypeClass x c) via toFinset.card.
  rw [(conditionalTypeClass (β := β) x c).toFinite.card_toFinset]
  -- Both subtype cards on {y // P y}, but Fintype instances differ — use Fintype.card_subtype_eq.
  exact Fintype.card_congr (Equiv.refl _)

/-- **Cardinality lower bound for conditional type class** (product of per-row
multinomial bounds):
`|conditionalTypeClass x c| ≥ ∏_a (typeCount x a)! / ∏_{a,b} (c (a,b))!`
up to the standard `(n+1)^{-|α×β|}` factor. -/
lemma conditionalTypeClass_card_ge
    {n : ℕ} (x : Fin n → α) (c : α × β → ℕ)
    (h_row : ∀ a, (∑ b : β, c (a, b)) = typeCount x a) :
    ∏ a : α, (((typeCount x a : ℝ) + 1) ^ (Fintype.card β : ℕ))⁻¹
        * ((typeCount x a : ℝ) ^ (typeCount x a)
            / ∏ b : β, ((c (a, b) : ℝ) ^ (c (a, b))))
      ≤ ((conditionalTypeClass (β := β) x c).toFinite.toFinset.card : ℝ) := by
  classical
  set Ta : α → ℕ := fun a => typeCount x a with hTa_def
  set crow : α → β → ℕ := fun a b => c (a, b) with hcrow_def
  have hcrow_sum : ∀ a, (∑ b : β, crow a b) = Ta a := fun a => h_row a
  have h_per_row : ∀ a : α,
      (((Ta a : ℝ) + 1) ^ (Fintype.card β : ℕ))⁻¹ *
          ((Ta a : ℝ) ^ Ta a / ∏ b : β, ((crow a b : ℝ) ^ (crow a b)))
        ≤ ((typeClassByCount (α := β) (n := Ta a) (crow a)).toFinite.toFinset.card : ℝ) :=
    fun a => typeClassByCount_card_ge (n := Ta a) (crow a) (hcrow_sum a)
  have h_prod_le :
      ∏ a : α, ((((Ta a : ℝ) + 1) ^ (Fintype.card β : ℕ))⁻¹ *
          ((Ta a : ℝ) ^ Ta a / ∏ b : β, ((crow a b : ℝ) ^ (crow a b))))
        ≤ ∏ a : α,
            ((typeClassByCount (α := β) (n := Ta a) (crow a)).toFinite.toFinset.card : ℝ) := by
    refine Finset.prod_le_prod (fun a _ => ?_) (fun a _ => h_per_row a)
    refine mul_nonneg (inv_nonneg.mpr ?_) ?_
    · positivity
    · refine div_nonneg ?_ ?_
      · positivity
      · refine Finset.prod_nonneg fun b _ => ?_
        positivity
  refine le_trans h_prod_le ?_
  -- Bijection gives: ∏_a card (T_{crow a}) = card (conditionalTypeClass x c).
  have h_bij := conditionalTypeClass_card_eq_prod_typeClass (β := β) x c
  rw [show ((conditionalTypeClass (β := β) x c).toFinite.toFinset.card : ℝ)
        = ((∏ a : α, ((typeClassByCount (α := β) (n := Ta a) (crow a)).toFinite.toFinset.card)) : ℝ)
      from by exact_mod_cast h_bij.symm]

/-! ### Phase E.3 — Per-y Y-product mass identity -/

/-- For `y ∈ conditionalTypeClass x c`, the Y-product mass at `y` equals
`∏_b qY(b)^{col_b}` where `col_b = ∑_a c (a, b)`. -/
lemma productMass_eq_columnProd
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Ys : ℕ → Ω → β)
    {n : ℕ} (x : Fin n → α) (c : α × β → ℕ)
    {y : Fin n → β} (hy : y ∈ conditionalTypeClass x c) :
    (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y}
      = ∏ b : β, (μ.map (Ys 0)).real {b} ^ (∑ a : α, c (a, b)) := by
  classical
  set qY : β → ℝ := fun b => (μ.map (Ys 0)).real {b} with hqY_def
  -- Step 1: pi-product singleton mass identity.
  have h_pi : (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y}
      = ∏ i : Fin n, qY (y i) := by
    show ((Measure.pi (fun _ : Fin n => μ.map (Ys 0))) {y}).toReal = ∏ i : Fin n, qY (y i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  rw [h_pi]
  -- Step 2: aggregate ∏ i, qY (y i) = ∏ b, qY(b) ^ typeCount y b via fiberwise.
  have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      y i ∈ (Finset.univ : Finset β) := fun _ _ => Finset.mem_univ _
  have h_fib := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset β)) h_maps (fun b : β => qY b)
  rw [← h_fib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Finset.prod_const]
  -- ((Finset.univ.filter fun i => y i = b).card) = typeCount y b = ∑ a, c (a, b)
  have h_count_y : (Finset.univ.filter fun i : Fin n => y i = b).card
      = ∑ a : α, c (a, b) := by
    -- ∑ a, c (a, b) = typeCount y b by partitioning {i : y i = b} by x i.
    have h_part : (Finset.univ.filter fun i : Fin n => y i = b)
        = (Finset.univ : Finset α).biUnion (fun a =>
            Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      refine ⟨fun h_yi => ⟨x i, rfl, h_yi⟩, ?_⟩
      rintro ⟨a, _, h_yi⟩
      exact h_yi
    have h_disjoint :
        ((Finset.univ : Finset α) : Set α).PairwiseDisjoint (fun a =>
          Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)) := by
      intro a₁ _ a₂ _ ha
      refine Finset.disjoint_filter.mpr ?_
      intro i _ ⟨ha₁, _⟩ ⟨ha₂, _⟩
      apply ha
      rw [← ha₁, ha₂]
    rw [h_part, Finset.card_biUnion h_disjoint]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact hy a b
  rw [h_count_y]

/-! ### Phase E.4 — Main assembly

The main theorem combines the four pieces:
1. **`floorMatrix` construction** (Phase E.1, proven): pick a single c_floor with
   row sums = typeCount x, total = n, and entries close to `n · qZ`.
2. **`floorMatrix_dist_le`** (statement only, Phase E.1): the rounding stays within
   `ε_X + |β|/n` of `qZ`. For n large or ε > ε_X, c_floor ∈ `sliceTypeIndices`.
3. **`conditionalTypeClass_card_ge`** (statement only, Phase E.2): the slice
   contains `conditionalTypeClass x c_floor` which has cardinality
   `≥ poly(n)⁻¹ · ∏_a (T_a^{T_a} / ∏_b c(a,b)^{c(a,b)})` (per-row multinomial).
4. **`productMass_eq_columnProd`** (Phase E.3, proven): for each `y` in this
   class, Y-product mass equals `∏_b qY(b)^{col_b}`.

Final algebra (the assembly): combining the cardinality bound, the per-y mass,
and the entropy chain rule `H(X) + H(Y) - H(Z) = I(X;Y)` yields the desired
exponential bound. Additionally requires marginal-compatibility hypotheses
(`hmarg_X`, `hmarg_Y`) which are typically supplied by the caller's construction
(e.g. `rdAmbient qStar` provides both marginals from a single joint pmf). -/

/-- **Marginal-Y identification** (helper): the Y-marginal of `qZ` equals `qY`,
i.e., `qY(b) = ∑_a qZ(a, b)`. -/
private lemma qY_eq_sum_qZ
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    (b : β) :
    (μ.map (Ys 0)).real {b} = ∑ a : α, (μ.map (jointSequence Xs Ys 0)).real {(a, b)} := by
  classical
  set qZ : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
  have h_pre : (Prod.snd ⁻¹' ({b} : Set β) : Set (α × β))
      = ⋃ a ∈ (Finset.univ : Finset α), ({(a, b)} : Set (α × β)) := by
    ext ⟨x', y'⟩
    constructor
    · intro hb'
      have : y' = b := hb'
      subst this
      refine Set.mem_iUnion.mpr ⟨x', Set.mem_iUnion.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · intro hb'
      rcases Set.mem_iUnion.mp hb' with ⟨a, ha⟩
      rcases Set.mem_iUnion.mp ha with ⟨_, hb''⟩
      simp only [Set.mem_singleton_iff] at hb''
      simp [Set.mem_preimage, hb'']
  have h_map : ((μ.map (jointSequence Xs Ys 0)).map Prod.snd).real {b}
      = (μ.map (jointSequence Xs Ys 0)).real (Prod.snd ⁻¹' {b}) :=
    map_measureReal_apply measurable_snd (MeasurableSet.singleton b)
  have h_qY_eq : ((μ.map (jointSequence Xs Ys 0)).map Prod.snd).real {b}
      = (μ.map (Ys 0)).real {b} := by rw [hmarg_Y]
  have h_disj : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint
      (fun a => ({(a, b)} : Set (α × β))) := by
    intro a₁ _ a₂ _ ha s hs1 hs2 p hp
    have hp1 := hs1 hp
    have hp2 := hs2 hp
    simp only [Set.mem_singleton_iff] at hp1 hp2
    have heq : (a₁, b) = (a₂, b) := hp1.symm.trans hp2
    exact (ha (Prod.mk.injEq _ _ _ _ |>.mp heq).1).elim
  have h_meas : ∀ a ∈ (Finset.univ : Finset α),
      MeasurableSet ({(a, b)} : Set (α × β)) := fun _ _ => measurableSet_singleton _
  have h_sum : (μ.map (jointSequence Xs Ys 0)).real (Prod.snd ⁻¹' {b})
      = ∑ a : α, qZ (a, b) := by
    rw [h_pre]
    rw [measureReal_biUnion_finset h_disj h_meas]
  rw [← h_qY_eq, h_map, h_sum]

/-- **Per-y Y-product mass lower bound** for `y ∈ conditionalTypeClass x c_floor`.
Combines `productMass_eq_columnProd` (exact mass identity) with the empirical
column-sum bound `|col_b/n - qY(b)| ≤ |α|·(ε_X + |β|/n)`. -/
private lemma productMass_columnProd_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hposY : ∀ b : β, 0 < (μ.map (Ys 0)).real {b})
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {n : ℕ} (hn : 0 < n)
    {ε_amp : ℝ} (hε_amp : 0 ≤ ε_amp)
    (c : α × β → ℕ)
    (h_close : ∀ p, |((c p : ℕ) : ℝ) / n - (μ.map (jointSequence Xs Ys 0)).real {p}|
                      ≤ ε_amp / (Fintype.card α : ℝ))
    (x : Fin n → α)
    {y : Fin n → β} (hy : y ∈ conditionalTypeClass x c) :
    Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys))
      ≤ (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y} := by
  classical
  set qY : β → ℝ := fun b => (μ.map (Ys 0)).real {b} with hqY_def
  set qZ : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set LY : ℝ := logSumAbs μ Ys with hLY_def
  have hLY_nn : 0 ≤ LY := logSumAbs_nonneg μ Ys
  have hα_pos : (0 : ℝ) < Fintype.card α := by
    have : (0 : ℕ) < Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Step 1: per-y mass = ∏_b qY(b)^col_b via productMass_eq_columnProd.
  rw [productMass_eq_columnProd (μ := μ) (Ys := Ys) x c hy]
  -- Step 2: take logs and apply the column-sum bound.
  set col : β → ℕ := fun b => ∑ a : α, c (a, b) with hcol_def
  -- Each col_b/n is close to qY(b) within ε_amp.
  have h_col_close : ∀ b : β, |(col b : ℝ) / n - qY b| ≤ ε_amp := by
    intro b
    -- col_b/n - qY(b) = ∑_a (c(a,b)/n - qZ(a,b)) since qY(b) = ∑_a qZ(a,b).
    have h_qY_marg : qY b = ∑ a : α, qZ (a, b) := by
      exact qY_eq_sum_qZ μ Xs Ys hmarg_Y b
    have h_decomp : (col b : ℝ) / n - qY b
        = ∑ a : α, ((c (a, b) : ℝ) / n - qZ (a, b)) := by
      rw [h_qY_marg, hcol_def]
      push_cast
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    rw [h_decomp]
    calc |∑ a : α, ((c (a, b) : ℝ) / n - qZ (a, b))|
        ≤ ∑ a : α, |((c (a, b) : ℝ) / n - qZ (a, b))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : α, ε_amp / (Fintype.card α : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact h_close (a, b)
      _ = (Fintype.card α : ℝ) * (ε_amp / (Fintype.card α : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ε_amp := by field_simp
  -- Step 3: bound ∏_b qY(b)^col_b ≥ exp(-n · (HY + ε_amp · LY)).
  -- Take log: ∑_b col_b · log qY(b) ≥ -n · (HY + ε_amp · LY).
  -- Decomposition: col_b · log qY(b) = n · qY(b) · log qY(b) + (col_b - n · qY(b)) · log qY(b).
  -- Sum: ∑_b col_b · log qY(b) = -n·HY + ∑_b (col_b - n·qY(b)) · log qY(b).
  -- |∑_b (col_b - n·qY(b)) · log qY(b)| ≤ n · ε_amp · LY.
  have h_qY_pos : ∀ b, 0 < qY b := fun b => hposY b
  -- Lower bound `∏ qY^col_b ≥ exp(-n(HY + ε_amp·LY))`.
  have h_prod_pos : 0 < ∏ b : β, qY b ^ col b := by
    refine Finset.prod_pos fun b _ => ?_
    exact pow_pos (h_qY_pos b) _
  rw [← Real.exp_log h_prod_pos]
  refine Real.exp_le_exp.mpr ?_
  have h_log_prod_eq : Real.log (∏ b : β, qY b ^ col b) = ∑ b : β, Real.log (qY b ^ col b) := by
    exact Real.log_prod (fun b _ => (pow_pos (h_qY_pos b) _).ne')
  rw [h_log_prod_eq]
  -- log(∏ qY^col) = ∑_b col_b · log qY(b)
  have h_log_each : ∀ b, Real.log (qY b ^ col b) = (col b : ℝ) * Real.log (qY b) :=
    fun b => Real.log_pow _ _
  rw [Finset.sum_congr rfl (fun b _ => h_log_each b)]
  -- Goal: -(n : ℝ) * (HY + ε_amp · LY) ≤ ∑ b, (col b) · log qY(b)
  -- Bridge: HY = -∑ qY · log qY. So -n·HY = n · ∑ qY · log qY = ∑_b n·qY(b)·log qY(b).
  have h_HY_eq : -(n : ℝ) * HY = ∑ b : β, (n : ℝ) * qY b * Real.log (qY b) := by
    have h_HY_unfold : HY = ∑ b : β, Real.negMulLog (qY b) := by
      show entropy μ (Ys 0) = ∑ b : β, Real.negMulLog (qY b)
      unfold entropy
      rfl
    rw [h_HY_unfold]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.negMulLog]
    ring
  -- Decomposition: (col b) · log qY(b) = n·qY(b)·log qY(b) + (col b - n·qY(b)) · log qY(b).
  have h_decomp_sum :
      (∑ b : β, ((col b : ℝ) * Real.log (qY b)))
        = ∑ b : β, (n : ℝ) * qY b * Real.log (qY b)
          + ∑ b : β, ((col b : ℝ) - (n : ℝ) * qY b) * Real.log (qY b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h_decomp_sum]
  rw [show -(n : ℝ) * (HY + ε_amp * LY)
        = -(n : ℝ) * HY + (-(n : ℝ) * ε_amp * LY) from by ring]
  rw [h_HY_eq]
  -- Now: need -(n · ε_amp · LY) ≤ ∑_b (col_b - n·qY(b)) · log qY(b).
  suffices h : -((n : ℝ) * ε_amp * LY) ≤ ∑ b : β, ((col b : ℝ) - (n : ℝ) * qY b) * Real.log (qY b) by
    have hgoal : -(n : ℝ) * ε_amp * LY = -((n : ℝ) * ε_amp * LY) := by ring
    rw [hgoal]
    linarith
  -- |∑_b (col_b - n·qY(b)) · log qY(b)| ≤ n · ε_amp · LY.
  have h_each : ∀ b ∈ (Finset.univ : Finset β),
      |((col b : ℝ) - (n : ℝ) * qY b)| ≤ (n : ℝ) * ε_amp := by
    intro b _
    have h := h_col_close b
    have h_re : (col b : ℝ) - (n : ℝ) * qY b = (n : ℝ) * ((col b : ℝ) / n - qY b) := by
      field_simp
    rw [h_re, abs_mul, abs_of_pos hn_pos]
    exact mul_le_mul_of_nonneg_left h hn_pos.le
  have h_abs_bound :
      |∑ b : β, ((col b : ℝ) - (n : ℝ) * qY b) * Real.log (qY b)|
        ≤ (n : ℝ) * ε_amp * LY := by
    calc |∑ b : β, ((col b : ℝ) - (n : ℝ) * qY b) * Real.log (qY b)|
        ≤ ∑ b : β, |((col b : ℝ) - (n : ℝ) * qY b) * Real.log (qY b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b : β, |((col b : ℝ) - (n : ℝ) * qY b)| * |Real.log (qY b)| := by
          refine Finset.sum_congr rfl fun b _ => abs_mul _ _
      _ ≤ ∑ b : β, ((n : ℝ) * ε_amp) * |Real.log (qY b)| := by
          refine Finset.sum_le_sum fun b hb => ?_
          exact mul_le_mul_of_nonneg_right (h_each b hb) (abs_nonneg _)
      _ = (n : ℝ) * ε_amp * ∑ b : β, |Real.log (qY b)| := by
          rw [← Finset.mul_sum]
      _ = (n : ℝ) * ε_amp * LY := by
          rfl
  have h_lb := neg_le_of_abs_le h_abs_bound
  linarith
/-! ### Phase E.4 — Entropy concentration helper (`conditional_KL_concentration_ge`)

Combines the per-row multinomial cardinality lower bound
(`conditionalTypeClass_card_ge`) with the per-y Y-product mass shape to yield the
joint exponential lower bound.

**Proof strategy**:
1. From `conditionalTypeClass_card_ge`, take logs:
   `log card ≥ -|β|·∑_a log(T_a+1) + ∑_a (T_a · log T_a - ∑_b c(a,b) · log c(a,b))`.
2. Combine with `n·log n` to express as
   `n·(entropyByCount c n - entropyByCount T n) - |β|·∑_a log(T_a+1)`.
3. Gibbs:
   * `entropyByCount c n ≥ HZ - (ε_X + |β|/n)·LZ - KL(c/n‖qZ)`
   * `entropyByCount T n ≤ HX + ε_X·LX`
4. KL bound (χ²): `KL(c/n‖qZ) ≤ |α||β|·(ε_X + |β|/n)² / qZ_min`. The
   `ε_X²` piece is controlled by the `hδ_dominates_kl` hypothesis; the
   `O(ε_X·|β|/n)` and `O(|β|²/n²)` pieces are dominated by `n·hδ` for `n` large.
5. Combine + exponentiate.

### Sub-lemmas

We factor out three local helpers used in the main proof:

* `KL_le_chi_square_finset` — Gibbs upper bound `∑ p·log(p/q) ≤ ∑ (p-q)²/q`
  (relies on `Real.log_le_sub_one_of_pos`, and the conservation `∑ p = ∑ q`).
* `sum_diff_log_abs_le_typicality` — for `|p - q| ≤ δ`,
  `|∑ (p - q)·log q| ≤ δ · ∑ |log q|`. -/

/-- **KL upper bound via χ²** (Gibbs/Pinsker): on a finite alphabet with
`∑ p = ∑ q`, `KL(p‖q) := ∑ p · log(p/q) ≤ ∑ (p-q)² / q`. -/
private lemma KL_le_chi_square_finset
    {γ : Type*} (s : Finset γ)
    (p q : γ → ℝ) (hp_nn : ∀ a ∈ s, 0 ≤ p a) (hq_pos : ∀ a ∈ s, 0 < q a)
    (h_sum_eq : (∑ a ∈ s, p a) = ∑ a ∈ s, q a) :
    (∑ a ∈ s, p a * Real.log (p a / q a))
      ≤ ∑ a ∈ s, (p a - q a) ^ 2 / q a := by
  -- Pointwise: p · log(p/q) ≤ p · (p/q - 1)  (from log x ≤ x - 1, x = p/q ≥ 0).
  -- Sum: ∑ p · (p/q - 1) = ∑ (p²/q - p) = ∑ p · (p - q)/q.
  --   = ∑ (p - q + q) · (p - q) / q
  --   = ∑ (p - q)²/q + ∑ (p - q).
  -- Since ∑ p = ∑ q, the latter ∑(p - q) = 0.
  -- Therefore ∑ p · log(p/q) ≤ ∑ (p - q)²/q + 0 = χ².
  have h_pointwise : ∀ a ∈ s,
      p a * Real.log (p a / q a) ≤ p a * (p a / q a - 1) := by
    intro a ha
    rcases lt_or_eq_of_le (hp_nn a ha) with hpa_pos | hpa_zero
    · have h_ratio_pos : 0 < p a / q a := div_pos hpa_pos (hq_pos a ha)
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos h_ratio_pos) (hp_nn a ha)
    · -- p a = 0: both sides equal 0.
      rw [← hpa_zero]; simp
  -- Sum the pointwise bound.
  have h_sum1 :
      (∑ a ∈ s, p a * Real.log (p a / q a))
        ≤ ∑ a ∈ s, p a * (p a / q a - 1) :=
    Finset.sum_le_sum h_pointwise
  refine le_trans h_sum1 ?_
  -- Rewrite ∑ p · (p/q - 1) = ∑ (p - q)²/q + (∑ p - ∑ q) = ∑ (p - q)²/q.
  have h_rewrite : ∀ a ∈ s,
      p a * (p a / q a - 1)
        = (p a - q a) ^ 2 / q a + (p a - q a) := by
    intro a ha
    have hq_ne : q a ≠ 0 := (hq_pos a ha).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl h_rewrite, Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  rw [h_sum_eq, sub_self, add_zero]

/-- For an empirical pmf within `δ` of a reference pmf,
`|∑ (p - q) · log q| ≤ δ · ∑ |log q|`. -/
private lemma sum_diff_log_abs_le_typicality
    {γ : Type*} [Fintype γ] (p q : γ → ℝ) (δ : ℝ)
    (h_close : ∀ a, |p a - q a| ≤ δ) :
    |∑ a : γ, (p a - q a) * Real.log (q a)|
      ≤ δ * ∑ a : γ, |Real.log (q a)| := by
  calc |∑ a : γ, (p a - q a) * Real.log (q a)|
      ≤ ∑ a : γ, |(p a - q a) * Real.log (q a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : γ, |p a - q a| * |Real.log (q a)| := by
        refine Finset.sum_congr rfl fun a _ => abs_mul _ _
    _ ≤ ∑ a : γ, δ * |Real.log (q a)| := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_right (h_close a) (abs_nonneg _)
    _ = δ * ∑ a : γ, |Real.log (q a)| := by
        rw [← Finset.mul_sum]

set_option maxHeartbeats 4000000 in
/-- **Conditional KL concentration helper** — combines `conditionalTypeClass_card_ge`
with `weak_displacement_eq_strong_sum` (joint) and a χ²-style KL bound to produce
the joint exponential lower bound used by `conditionalStronglyTypicalSlice_mass_ge`.

The auxiliary hypotheses `qZ_min > 0`, `qZ_min ≤ qZ p`, and `8·|α|·|β|·ε_X² ≤ hδ·qZ_min`
encode the small-`ε_X` / `qZ_min`-dependent slack required for the χ² bound
`KL(c/n‖qZ) ≤ |α|·|β|·(ε_X + |β|/n)²/qZ_min` to be dominated by `hδ`. -/
private lemma conditional_KL_concentration_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {ε ε_X : ℝ} (hε : 0 < ε) (hε_X : 0 ≤ ε_X) (hδ : ℝ) (hδ_pos : 0 < hδ)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β, qZ_min ≤ (μ.map (jointSequence Xs Ys 0)).real {p})
    (hδ_dominates_kl :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ hδ * qZ_min) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (x : Fin n → α),
      x ∈ stronglyTypicalSet μ Xs n ε_X →
      Real.exp (-(n : ℝ) *
            (entropy μ (Xs 0) + entropy μ (Ys 0)
              - entropy μ (jointSequence Xs Ys 0)
              + ((Fintype.card α : ℝ) * ε_X * logSumAbs μ Ys
                + ε_X * logSumAbs μ Xs
                + ε_X * logSumAbs μ (jointSequence Xs Ys)
                + hδ)))
        ≤ ((Set.Finite.toFinset (conditionalTypeClass_finite (β := β) x
              (fun p => floorMatrix
                (fun p' => (μ.map (jointSequence Xs Ys 0)).real {p'}) x p.1 p.2))).card : ℝ)
          * Real.exp (-(n : ℝ) *
                (entropy μ (Ys 0)
                  + ((Fintype.card α : ℝ) * ε_X
                      + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / n)
                    * logSumAbs μ Ys)) := by
  classical
  -- ── Abbreviations and bookkeeping. ──
  set qZ : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
  set qX : α → ℝ := fun a => (μ.map (Xs 0)).real {a} with hqX_def
  set HX : ℝ := entropy μ (Xs 0) with hHX_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set HZ : ℝ := entropy μ (jointSequence Xs Ys 0) with hHZ_def
  set LX : ℝ := logSumAbs μ Xs with hLX_def
  set LY : ℝ := logSumAbs μ Ys with hLY_def
  set LZ : ℝ := logSumAbs μ (jointSequence Xs Ys) with hLZ_def
  have hLX_nn : 0 ≤ LX := logSumAbs_nonneg μ Xs
  have hLY_nn : 0 ≤ LY := logSumAbs_nonneg μ Ys
  have hLZ_nn : 0 ≤ LZ := logSumAbs_nonneg μ (jointSequence Xs Ys)
  have hα_pos_nat : (0 : ℕ) < Fintype.card α := Fintype.card_pos
  have hβ_pos_nat : (0 : ℕ) < Fintype.card β := Fintype.card_pos
  have hα_pos : (0 : ℝ) < Fintype.card α := by exact_mod_cast hα_pos_nat
  have hβ_pos : (0 : ℝ) < Fintype.card β := by exact_mod_cast hβ_pos_nat
  have hα_nn : (0 : ℝ) ≤ Fintype.card α := hα_pos.le
  have hβ_nn : (0 : ℝ) ≤ Fintype.card β := hβ_pos.le
  have hαβ_pos : 0 < (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := mul_pos hα_pos hβ_pos
  have hαβ_nn : 0 ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := hαβ_pos.le
  -- Measurability of the joint sequence (used for probability-measure inheritance).
  have hZ_meas : Measurable (jointSequence Xs Ys 0) := measurable_jointSequence Xs Ys hXs hYs 0
  -- Inherit probability measures on the pushforwards.
  have hZ_prob : IsProbabilityMeasure (μ.map (jointSequence Xs Ys 0)) :=
    Measure.isProbabilityMeasure_map hZ_meas.aemeasurable
  have hX_prob : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  -- qZ positivity and sub-probability bounds.
  have hqZ_pos : ∀ p, 0 < qZ p := hposZ
  have hqZ_nn : ∀ p, 0 ≤ qZ p := fun p => (hqZ_pos p).le
  have hqZ_le_one : ∀ p, qZ p ≤ 1 := fun p => by
    show (μ.map (jointSequence Xs Ys 0)).real {p} ≤ 1
    exact measureReal_le_one
  -- qZ marginalizes to a probability measure on α (resp. β).
  -- ∑ p, qZ p = 1.
  have h_qZ_sum_one : (∑ p : α × β, qZ p) = 1 := by
    have h_univ_eq : (Set.univ : Set (α × β))
        = ⋃ p ∈ (Finset.univ : Finset (α × β)), ({p} : Set (α × β)) := by ext p; simp
    have h_disj : (↑(Finset.univ : Finset (α × β)) : Set (α × β)).PairwiseDisjoint
        (fun p => ({p} : Set (α × β))) := by
      intro p₁ _ p₂ _ hp s hs1 hs2 q hq
      have hq1 := hs1 hq; have hq2 := hs2 hq
      simp only [Set.mem_singleton_iff] at hq1 hq2
      exact (hp (hq1.symm.trans hq2)).elim
    have h_meas : ∀ p ∈ (Finset.univ : Finset (α × β)),
        MeasurableSet ({p} : Set (α × β)) := fun _ _ => measurableSet_singleton _
    have h_sum : (μ.map (jointSequence Xs Ys 0)).real (Set.univ : Set (α × β))
        = ∑ p : α × β, qZ p := by
      rw [h_univ_eq, measureReal_biUnion_finset h_disj h_meas]
    have h_univ : (μ.map (jointSequence Xs Ys 0)).real (Set.univ) = 1 :=
      probReal_univ (μ := μ.map (jointSequence Xs Ys 0))
    rw [← h_sum, h_univ]
  -- ∑ a, qX a = 1.
  have h_qX_sum_one : (∑ a : α, qX a) = 1 := by
    have h_univ_eq : (Set.univ : Set α)
        = ⋃ a ∈ (Finset.univ : Finset α), ({a} : Set α) := by ext a; simp
    have h_disj : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint
        (fun a => ({a} : Set α)) := by
      intro a₁ _ a₂ _ ha s hs1 hs2 q hq
      have hq1 := hs1 hq; have hq2 := hs2 hq
      simp only [Set.mem_singleton_iff] at hq1 hq2
      exact (ha (hq1.symm.trans hq2)).elim
    have h_meas : ∀ a ∈ (Finset.univ : Finset α),
        MeasurableSet ({a} : Set α) := fun _ _ => measurableSet_singleton _
    have h_sum : (μ.map (Xs 0)).real (Set.univ : Set α) = ∑ a : α, qX a := by
      rw [h_univ_eq, measureReal_biUnion_finset h_disj h_meas]
    have h_univ : (μ.map (Xs 0)).real (Set.univ) = 1 :=
      probReal_univ (μ := μ.map (Xs 0))
    rw [← h_sum, h_univ]
  -- qX a > 0 from qZ-marginal: qX a = ∑_b qZ(a, b), each term > 0.
  have hqX_pos : ∀ a : α, 0 < qX a := by
    intro a
    have h_pre : (Prod.fst ⁻¹' ({a} : Set α) : Set (α × β))
        = ⋃ b ∈ (Finset.univ : Finset β), ({(a, b)} : Set (α × β)) := by
      ext ⟨x', y'⟩
      refine ⟨fun hx' => ?_, fun hx' => ?_⟩
      · have : x' = a := hx'; subst this
        refine Set.mem_iUnion.mpr ⟨y', Set.mem_iUnion.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      · rcases Set.mem_iUnion.mp hx' with ⟨b', hb'⟩
        rcases Set.mem_iUnion.mp hb' with ⟨_, hb''⟩
        simp only [Set.mem_singleton_iff] at hb''
        simp [Set.mem_preimage, hb'']
    have h_map : ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a}
        = (μ.map (jointSequence Xs Ys 0)).real (Prod.fst ⁻¹' {a}) :=
      map_measureReal_apply measurable_fst (MeasurableSet.singleton a)
    have h_qX_eq : ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a} = qX a := by
      rw [hmarg_X]
    have h_disj : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint
        (fun b => ({(a, b)} : Set (α × β))) := by
      intro b₁ _ b₂ _ hb s hs1 hs2 p hp
      have hp1 := hs1 hp; have hp2 := hs2 hp
      simp only [Set.mem_singleton_iff] at hp1 hp2
      have heq : (a, b₁) = (a, b₂) := hp1.symm.trans hp2
      exact (hb (Prod.mk.injEq _ _ _ _ |>.mp heq).2).elim
    have h_meas : ∀ b ∈ (Finset.univ : Finset β),
        MeasurableSet ({(a, b)} : Set (α × β)) := fun _ _ => measurableSet_singleton _
    have h_sum : (μ.map (jointSequence Xs Ys 0)).real (Prod.fst ⁻¹' {a})
        = ∑ b : β, qZ (a, b) := by
      rw [h_pre, measureReal_biUnion_finset h_disj h_meas]
    have h_qXa_eq : qX a = ∑ b : β, qZ (a, b) := by
      rw [← h_qX_eq, h_map, h_sum]
    rw [h_qXa_eq]
    exact Finset.sum_pos (fun b _ => hqZ_pos (a, b)) Finset.univ_nonempty
  have hqX_nn : ∀ a, 0 ≤ qX a := fun a => (hqX_pos a).le
  -- ── Archimedean choice of N. ──
  -- (B) log(n+1)/n ≤ hδ / (4·|α|·|β|).
  obtain ⟨N_log, hN_log⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.log ((n : ℝ) + 1) / n
        ≤ hδ / (4 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
    have h_target_pos : 0 < hδ / (4 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
      apply div_pos hδ_pos
      have : (0 : ℝ) < 4 * (Fintype.card α : ℝ) := by linarith
      exact mul_pos this hβ_pos
    have h_lim : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
      have h_log_id : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      have h_shift : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
      have h_nat : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
          atTop (𝓝 0) := h_log_id.comp h_shift
      have h_ratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / n) atTop (𝓝 (1 + 0)) := by
          refine tendsto_const_nhds.add ?_
          exact tendsto_one_div_atTop_nhds_zero_nat
        rw [add_zero] at h1
        refine h1.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
        field_simp
      have h_prod : Tendsto
          (fun n : ℕ => (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
                          * (((n : ℝ) + 1) / n)) atTop (𝓝 (0 * 1)) := h_nat.mul h_ratio
      rw [zero_mul] at h_prod
      refine h_prod.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1_R : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      field_simp
    rw [Metric.tendsto_atTop] at h_lim
    obtain ⟨N, hN⟩ := h_lim _ h_target_pos
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    have h_nn : 0 ≤ Real.log ((n : ℝ) + 1) / n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · have hn_R : (0 : ℝ) < n := by exact_mod_cast hpos
        exact div_nonneg (Real.log_nonneg (by linarith)) hn_R.le
    rw [abs_of_nonneg h_nn] at h
    exact h.le
  -- (C) (|β|·LZ + |α|·|β|·LY) / n ≤ hδ/4.
  obtain ⟨N_const, hN_const⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((Fintype.card β : ℝ) * LZ
        + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY) / n ≤ hδ / 4 := by
    set C := (Fintype.card β : ℝ) * LZ + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY
      with hC_def
    have hC_nn : 0 ≤ C := by
      have h1 : 0 ≤ (Fintype.card β : ℝ) * LZ := mul_nonneg hβ_nn hLZ_nn
      have h2 : 0 ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY :=
        mul_nonneg hαβ_nn hLY_nn
      linarith
    have h_target_pos : 0 < hδ / 4 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (C / (hδ / 4))
    refine ⟨max N 1, fun n hn => ?_⟩
    have hN_le : N ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn1
    have hN_lt : C / (hδ / 4) < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hN_le)
    rw [div_lt_iff₀ h_target_pos] at hN_lt
    rw [div_le_iff₀ hn_R]
    linarith
  -- (D-cross) 2·|α|·|β|²·ε_X / qZ_min ≤ n · (hδ/8).
  obtain ⟨N_KL_cross, hN_KL_cross⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^2 * ε_X / qZ_min
        ≤ (n : ℝ) * (hδ / 8) := by
    set K := 2 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^2 * ε_X / qZ_min with hK_def
    have hK_nn : 0 ≤ K := by
      apply div_nonneg _ hqZ_min_pos.le
      apply mul_nonneg _ hε_X
      apply mul_nonneg _ (by positivity)
      linarith
    have h_target_pos : 0 < hδ / 8 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (K / (hδ / 8))
    refine ⟨max N 1, fun n hn => ?_⟩
    have hN_le : N ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn1
    have hN_lt : K / (hδ / 8) < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hN_le)
    rw [div_lt_iff₀ h_target_pos] at hN_lt
    linarith
  -- (D-inv) |α|·|β|³ / (n · qZ_min) ≤ hδ/8.
  obtain ⟨N_KL_inv, hN_KL_inv⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^3 / (n * qZ_min) ≤ hδ / 8 := by
    set K := (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^3 / qZ_min with hK_def
    have hK_nn : 0 ≤ K := by
      apply div_nonneg _ hqZ_min_pos.le
      apply mul_nonneg hα_nn (by positivity)
    have h_target_pos : 0 < hδ / 8 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (K / (hδ / 8))
    refine ⟨max N 1, fun n hn => ?_⟩
    have hN_le : N ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn1
    have hN_lt : K / (hδ / 8) < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hN_le)
    rw [div_lt_iff₀ h_target_pos] at hN_lt
    have hK_div : K / n ≤ hδ / 8 := by
      rw [div_le_iff₀ hn_R]; linarith
    -- Rewrite (|α|·|β|^3) / (n · qZ_min) = K / n.
    have h_eq : (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^3 / (n * qZ_min) = K / n := by
      rw [hK_def, div_div, mul_comm (n : ℝ) qZ_min]
    rw [h_eq]; exact hK_div
  -- Take the max of all four (and 1 to keep n ≥ 1).
  refine ⟨max (max (max N_log N_const) (max N_KL_cross N_KL_inv)) 1,
    fun n hn_ge x hx => ?_⟩
  have hn_pos_nat : 0 < n := by
    have : 1 ≤ n := le_of_max_le_right hn_ge; omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hn_main : max (max N_log N_const) (max N_KL_cross N_KL_inv) ≤ n :=
    le_of_max_le_left hn_ge
  have hn_pair1 : max N_log N_const ≤ n := le_of_max_le_left hn_main
  have hn_pair2 : max N_KL_cross N_KL_inv ≤ n := le_of_max_le_right hn_main
  have hn_N_log : N_log ≤ n := le_of_max_le_left hn_pair1
  have hn_N_const : N_const ≤ n := le_of_max_le_right hn_pair1
  have hn_N_KL_cross : N_KL_cross ≤ n := le_of_max_le_left hn_pair2
  have hn_N_KL_inv : N_KL_inv ≤ n := le_of_max_le_right hn_pair2
  -- ε_X-strong typicality of x.
  have hx_typ : ∀ a, |(typeCount x a : ℝ) / n - qX a| ≤ ε_X := hx
  -- Set c := floorMatrix qZ x · (joint count vector).
  set c : α × β → ℕ := fun p => floorMatrix qZ x p.1 p.2 with hc_def
  set T : α → ℕ := fun a => typeCount x a with hT_def
  have hc_row : ∀ a, (∑ b : β, c (a, b)) = T a :=
    fun a => floorMatrix_row_sum qZ hqZ_nn x a
  have hc_total : (∑ p : α × β, c p) = n := floorMatrix_total qZ hqZ_nn x
  have hT_le_n : ∀ a, T a ≤ n := by
    intro a
    have h1 : (Finset.univ.filter (fun i : Fin n => x i = a)).card ≤
        (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  have hT_sum : (∑ a : α, T a) = n := by
    show (∑ a : α, typeCount x a) = n
    unfold typeCount
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        x i ∈ (Finset.univ : Finset α) := fun _ _ => Finset.mem_univ _
    have h_fiber := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps (fun _ : Fin n => (1 : ℕ))
    have h_card : ∀ a : α,
        ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card
          = ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i => x i = a), (1 : ℕ) := by
      intro a; rw [Finset.sum_const, Nat.smul_one_eq_cast]; rfl
    rw [show (∑ a : α, ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card)
          = ∑ a : α, ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i => x i = a),
              (1 : ℕ)
        from Finset.sum_congr rfl fun a _ => h_card a]
    rw [h_fiber]; simp
  -- c-distance bound.
  have hc_close : ∀ p, |((c p : ℕ) : ℝ) / n - qZ p| ≤ ε_X + (Fintype.card β : ℝ) / n := by
    intro p
    obtain ⟨a, b⟩ := p
    exact floorMatrix_dist_le μ Xs Ys hXs hYs hposZ hmarg_X hn_pos_nat hε_X x hx a b
  -- ε_Z := ε_X + |β|/n.
  set ε_Z : ℝ := ε_X + (Fintype.card β : ℝ) / n with hε_Z_def
  have hβ_over_n_nn : 0 ≤ (Fintype.card β : ℝ) / n := div_nonneg hβ_nn hn_pos.le
  have hε_Z_nn : 0 ≤ ε_Z := by rw [hε_Z_def]; linarith
  -- ε_Z² = ε_X² + 2·ε_X·|β|/n + |β|²/n².
  have hε_Z_sq_expand : ε_Z^2 = ε_X^2 + 2 * ε_X * ((Fintype.card β : ℝ) / n)
      + ((Fintype.card β : ℝ) / n)^2 := by rw [hε_Z_def]; ring
  -- ── Step (I): Take logs of the cardinality lower bound. ──
  -- conditionalTypeClass_card_ge gives
  --   ∏_a [((T a + 1)^|β|)⁻¹ * (T_a^{T_a} / ∏_b c(a,b)^{c(a,b)})] ≤ card.
  set card_real : ℝ := ((Set.Finite.toFinset
    (conditionalTypeClass_finite (β := β) x c)).card : ℝ) with hcard_real_def
  -- Positivity gymnastics for the LHS product.
  have hT_plus_one_pos : ∀ a, (0 : ℝ) < (T a : ℝ) + 1 := by
    intro a; have : (0 : ℝ) ≤ (T a : ℝ) := Nat.cast_nonneg _; linarith
  have hT_plus_one_pow_pos : ∀ a, (0 : ℝ) < ((T a : ℝ) + 1) ^ (Fintype.card β : ℕ) :=
    fun a => pow_pos (hT_plus_one_pos a) _
  have hT_pow_pos_or_one : ∀ a,
      (0 : ℝ) < ((T a : ℝ)) ^ (T a) ∨ ((T a : ℝ)) ^ (T a) = 1 := by
    intro a
    rcases Nat.eq_zero_or_pos (T a) with h | h
    · right; rw [h, pow_zero]
    · left; exact pow_pos (by exact_mod_cast h) _
  have hT_pow_pos : ∀ a, (0 : ℝ) < ((T a : ℝ)) ^ (T a) := by
    intro a
    rcases hT_pow_pos_or_one a with h | h
    · exact h
    · rw [h]; exact one_pos
  have hT_pow_ne : ∀ a, ((T a : ℝ)) ^ (T a) ≠ 0 := fun a => (hT_pow_pos a).ne'
  have hc_pow_pos_or_one : ∀ a b,
      (0 : ℝ) < (c (a, b) : ℝ) ^ (c (a, b)) ∨ ((c (a, b) : ℝ)) ^ (c (a, b)) = 1 := by
    intro a b
    rcases Nat.eq_zero_or_pos (c (a, b)) with h | h
    · right; rw [h, pow_zero]
    · left; exact pow_pos (by exact_mod_cast h) _
  have hc_pow_pos : ∀ a b, (0 : ℝ) < (c (a, b) : ℝ) ^ (c (a, b)) := by
    intro a b
    rcases hc_pow_pos_or_one a b with h | h
    · exact h
    · rw [h]; exact one_pos
  have hc_pow_prod_pos : ∀ a, (0 : ℝ) < ∏ b : β, (c (a, b) : ℝ) ^ (c (a, b)) :=
    fun a => Finset.prod_pos fun b _ => hc_pow_pos a b
  have hc_pow_prod_ne : ∀ a, (∏ b : β, (c (a, b) : ℝ) ^ (c (a, b))) ≠ 0 :=
    fun a => (hc_pow_prod_pos a).ne'
  -- Per-row factor.
  set rowFactor : α → ℝ := fun a =>
    (((T a : ℝ) + 1) ^ (Fintype.card β : ℕ))⁻¹
      * ((T a : ℝ) ^ T a / ∏ b : β, (c (a, b) : ℝ) ^ (c (a, b))) with hrowFactor_def
  have hrowFactor_pos : ∀ a, 0 < rowFactor a := fun a =>
    mul_pos (inv_pos.mpr (hT_plus_one_pow_pos a))
      (div_pos (hT_pow_pos a) (hc_pow_prod_pos a))
  have hrowProd_pos : 0 < ∏ a : α, rowFactor a := Finset.prod_pos fun a _ => hrowFactor_pos a
  have h_card_ge_prod : ∏ a : α, rowFactor a ≤ card_real := by
    have h := conditionalTypeClass_card_ge (β := β) x c hc_row
    exact h
  -- Per-row log expansion.
  have h_log_each : ∀ a, Real.log (rowFactor a)
      = -(Fintype.card β : ℝ) * Real.log ((T a : ℝ) + 1)
        + (T a : ℝ) * Real.log (T a : ℝ)
        - ∑ b : β, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ) := by
    intro a
    rw [hrowFactor_def,
      Real.log_mul (inv_ne_zero (hT_plus_one_pow_pos a).ne')
        (div_ne_zero (hT_pow_ne a) (hc_pow_prod_ne a)),
      Real.log_inv, Real.log_pow,
      Real.log_div (hT_pow_ne a) (hc_pow_prod_ne a),
      Real.log_pow]
    have h_prod_log : Real.log (∏ b : β, (c (a, b) : ℝ) ^ (c (a, b)))
        = ∑ b : β, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ) := by
      rw [Real.log_prod (fun b _ => (hc_pow_pos a b).ne')]
      exact Finset.sum_congr rfl fun b _ => Real.log_pow _ _
    rw [h_prod_log]
    ring
  -- Sum log of the product.
  have h_log_prod : Real.log (∏ a : α, rowFactor a) = ∑ a : α, Real.log (rowFactor a) :=
    Real.log_prod (fun a _ => (hrowFactor_pos a).ne')
  -- ── Step (II): Chain-rule shape S := ∑_a T_a log T_a - ∑_{ab} c log c
  --     = n · (HZemp - HXemp). ──
  set HXemp : ℝ := -∑ a : α, ((T a : ℝ) / n) * Real.log ((T a : ℝ) / n) with hHXemp_def
  set HZemp : ℝ := -∑ p : α × β, ((c p : ℕ) : ℝ) / n * Real.log (((c p : ℕ) : ℝ) / n)
    with hHZemp_def
  have h_chain :
      (∑ a : α, (T a : ℝ) * Real.log (T a : ℝ))
        - ∑ a : α, ∑ b : β, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ)
        = (n : ℝ) * HZemp - (n : ℝ) * HXemp := by
    -- ∑_a T_a log T_a = n·log n - n·HXemp.
    have h_X : (∑ a : α, (T a : ℝ) * Real.log (T a : ℝ))
        = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) * HXemp := by
      have h_each : ∀ a, (T a : ℝ) * Real.log ((T a : ℝ) / n)
          = (T a : ℝ) * Real.log (T a : ℝ) - (T a : ℝ) * Real.log (n : ℝ) := by
        intro a
        rcases Nat.eq_zero_or_pos (T a) with h | h
        · rw [h]; push_cast; simp
        · have hpos : (0 : ℝ) < (T a : ℝ) := by exact_mod_cast h
          rw [Real.log_div hpos.ne' hn_ne]; ring
      have h_sum_each :
          (∑ a : α, (T a : ℝ) * Real.log ((T a : ℝ) / n))
            = (∑ a : α, (T a : ℝ) * Real.log (T a : ℝ))
              - (∑ a : α, (T a : ℝ)) * Real.log (n : ℝ) := by
        rw [Finset.sum_congr rfl (fun a _ => h_each a), Finset.sum_sub_distrib]
        congr 1; rw [← Finset.sum_mul]
      have hT_R_sum : (∑ a : α, (T a : ℝ)) = (n : ℝ) := by exact_mod_cast hT_sum
      have hnHX : (n : ℝ) * HXemp = -∑ a : α, (T a : ℝ) * Real.log ((T a : ℝ) / n) := by
        rw [hHXemp_def, mul_neg, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        field_simp
      -- Substitute ∑ T = n into h_sum_each.
      rw [hT_R_sum] at h_sum_each
      linarith
    -- ∑_{ab} c log c = n·log n - n·HZemp.
    have h_Z : (∑ a : α, ∑ b : β, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ))
        = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) * HZemp := by
      have h_swap : (∑ a : α, ∑ b : β, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ))
          = ∑ p : α × β, ((c p : ℕ) : ℝ) * Real.log ((c p : ℕ) : ℝ) := by
        rw [← Finset.sum_product']; rfl
      rw [h_swap]
      have h_each : ∀ p : α × β, ((c p : ℕ) : ℝ) * Real.log (((c p : ℕ) : ℝ) / n)
          = ((c p : ℕ) : ℝ) * Real.log ((c p : ℕ) : ℝ)
            - ((c p : ℕ) : ℝ) * Real.log (n : ℝ) := by
        intro p
        rcases Nat.eq_zero_or_pos (c p) with h | h
        · rw [show ((c p : ℕ) : ℝ) = 0 from by exact_mod_cast h]; simp
        · have hpos : (0 : ℝ) < ((c p : ℕ) : ℝ) := by exact_mod_cast h
          rw [Real.log_div hpos.ne' hn_ne]; ring
      have h_sum_each :
          (∑ p : α × β, ((c p : ℕ) : ℝ) * Real.log (((c p : ℕ) : ℝ) / n))
            = (∑ p : α × β, ((c p : ℕ) : ℝ) * Real.log ((c p : ℕ) : ℝ))
              - (∑ p : α × β, ((c p : ℕ) : ℝ)) * Real.log (n : ℝ) := by
        rw [Finset.sum_congr rfl (fun p _ => h_each p), Finset.sum_sub_distrib]
        congr 1; rw [← Finset.sum_mul]
      have hc_R_sum : (∑ p : α × β, ((c p : ℕ) : ℝ)) = (n : ℝ) := by exact_mod_cast hc_total
      have hnHZ : (n : ℝ) * HZemp =
          -∑ p : α × β, ((c p : ℕ) : ℝ) * Real.log (((c p : ℕ) : ℝ) / n) := by
        rw [hHZemp_def, mul_neg, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        field_simp
      rw [hc_R_sum] at h_sum_each
      linarith
    linarith
  -- Assemble log card lower bound.
  have h_log_card_lb : (n : ℝ) * HZemp - (n : ℝ) * HXemp
        - (Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1)
      ≤ Real.log card_real := by
    have h1 : Real.log (∏ a : α, rowFactor a) ≤ Real.log card_real := by
      apply Real.log_le_log hrowProd_pos h_card_ge_prod
    refine le_trans ?_ h1
    rw [h_log_prod, Finset.sum_congr rfl (fun a _ => h_log_each a)]
    -- Split the sum.
    have h_split :
        (∑ a : α,
          (-(Fintype.card β : ℝ) * Real.log ((T a : ℝ) + 1)
            + (T a : ℝ) * Real.log (T a : ℝ)
            - ∑ b : β, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ)))
        = -(Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1)
          + ((∑ a : α, (T a : ℝ) * Real.log (T a : ℝ))
              - ∑ a : α, ∑ b : β, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [show (∑ a : α, -(Fintype.card β : ℝ) * Real.log ((T a : ℝ) + 1))
            = -(Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1) from by
        rw [← Finset.mul_sum]]
      ring
    rw [h_split, h_chain]; linarith
  -- ── Step (II'): bound ∑_a log(T_a + 1) ≤ |α| · log(n + 1). ──
  have h_logT_sum_le : (∑ a : α, Real.log ((T a : ℝ) + 1))
      ≤ (Fintype.card α : ℝ) * Real.log ((n : ℝ) + 1) := by
    have h_each : ∀ a, Real.log ((T a : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := by
      intro a
      have hT_le_R : (T a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hT_le_n a
      apply Real.log_le_log (by linarith : (0 : ℝ) < (T a : ℝ) + 1)
      linarith
    have h_sum_le : (∑ a : α, Real.log ((T a : ℝ) + 1))
        ≤ ∑ a : α, Real.log ((n : ℝ) + 1) :=
      Finset.sum_le_sum fun a _ => h_each a
    have : (∑ a : α, Real.log ((n : ℝ) + 1)) = (Fintype.card α : ℝ) * Real.log ((n : ℝ) + 1) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  -- ── Step (III): Gibbs+typicality on X: HXemp ≤ HX + ε_X · LX. ──
  -- crossX := -∑_a (T_a/n) · log qX(a) = (∑_i pmfLog (x_i))/n.
  set crossX : ℝ := -∑ a : α, ((T a : ℝ) / n) * Real.log (qX a) with hcrossX_def
  -- HXemp ≤ crossX via Gibbs.
  have h_gibbs_X : HXemp ≤ crossX := by
    -- Use log y ≤ y - 1 with y = qX/(T/n):
    -- (T/n) · log(qX/(T/n)) ≤ qX - T/n. Sum: ≤ ∑ qX - ∑ T/n = 1 - 1 = 0.
    have h_pointwise : ∀ a ∈ (Finset.univ : Finset α),
        ((T a : ℝ) / n) * Real.log (qX a / ((T a : ℝ) / n)) ≤
          qX a - ((T a : ℝ) / n) := by
      intro a _
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ (T a : ℝ) / n from
        div_nonneg (Nat.cast_nonneg _) hn_pos.le) with hpos | hzero
      · have h_ratio_pos : 0 < qX a / ((T a : ℝ) / n) := div_pos (hqX_pos a) hpos
        have hlog := Real.log_le_sub_one_of_pos h_ratio_pos
        have hmul : ((T a : ℝ) / n) * Real.log (qX a / ((T a : ℝ) / n))
            ≤ ((T a : ℝ) / n) * (qX a / ((T a : ℝ) / n) - 1) :=
          mul_le_mul_of_nonneg_left hlog hpos.le
        refine le_trans hmul ?_
        have h_ratio_ne : ((T a : ℝ) / n) ≠ 0 := hpos.ne'
        have h_simp : ((T a : ℝ) / n) * (qX a / ((T a : ℝ) / n) - 1)
            = qX a - (T a : ℝ) / n := by
          rw [mul_sub, mul_one, mul_div_assoc', mul_comm ((T a : ℝ) / n) (qX a),
              mul_div_assoc, div_self h_ratio_ne, mul_one]
        linarith
      · rw [← hzero, zero_mul]; linarith [hqX_nn a]
    have h_sum1 :
        (∑ a : α, ((T a : ℝ) / n) * Real.log (qX a / ((T a : ℝ) / n)))
          ≤ ∑ a : α, (qX a - ((T a : ℝ) / n)) :=
      Finset.sum_le_sum h_pointwise
    have h_sum_zero : (∑ a : α, (qX a - ((T a : ℝ) / n))) = 0 := by
      rw [Finset.sum_sub_distrib,
        show (∑ a : α, ((T a : ℝ) / n)) = (∑ a : α, (T a : ℝ)) / n from by
          rw [Finset.sum_div],
        show (∑ a : α, (T a : ℝ)) = (n : ℝ) from by exact_mod_cast hT_sum,
        div_self hn_ne, h_qX_sum_one, sub_self]
    have h_HX_minus_cross :
        HXemp - crossX
          = ∑ a : α, ((T a : ℝ) / n) * Real.log (qX a / ((T a : ℝ) / n)) := by
      rw [hHXemp_def, hcrossX_def]
      rw [show -∑ a : α, ((T a : ℝ) / n) * Real.log ((T a : ℝ) / n)
            - (-∑ a : α, ((T a : ℝ) / n) * Real.log (qX a))
            = ∑ a : α, ((T a : ℝ) / n) * Real.log (qX a)
              - ∑ a : α, ((T a : ℝ) / n) * Real.log ((T a : ℝ) / n) from by ring]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ (T a : ℝ) / n from
        div_nonneg (Nat.cast_nonneg _) hn_pos.le) with hpos | hzero
      · rw [Real.log_div (hqX_pos a).ne' hpos.ne']; ring
      · rw [← hzero]; simp
    linarith
  -- crossX − HX  ≤ ε_X·LX (typicality on X via weak_displacement_eq_strong_sum).
  have h_cross_X_typ : |crossX - HX| ≤ ε_X * LX := by
    have h_cross_eq : (∑ i : Fin n, pmfLog μ Xs (x i)) / n = crossX := by
      have h_pmfLog_eq : ∀ a, pmfLog μ Xs a = -Real.log (qX a) := fun a => rfl
      set f : α → ℝ := fun a => -Real.log (qX a) with hf_def
      have h_pmf_eq_f : ∀ i, pmfLog μ Xs (x i) = f (x i) := fun i => h_pmfLog_eq (x i)
      have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          x i ∈ (Finset.univ : Finset α) := fun _ _ => Finset.mem_univ _
      have h_fib := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset α)) h_maps f
      have h_agg : (∑ i : Fin n, pmfLog μ Xs (x i)) = ∑ a : α, (T a : ℝ) * f a := by
        rw [Finset.sum_congr rfl fun i _ => h_pmf_eq_f i, ← h_fib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
      rw [h_agg, Finset.sum_div, hcrossX_def]
      -- Goal: ∑ a, (T a : ℝ) * f a / n = -∑ a, ((T a : ℝ) / n) * Real.log (qX a)
      rw [show (∑ a : α, (T a : ℝ) * f a / n)
            = -∑ a : α, ((T a : ℝ) / n) * Real.log (qX a) from ?_]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hf_def]
      have : (T a : ℝ) * (-Real.log (qX a)) / n = -((T a : ℝ) / n * Real.log (qX a)) := by
        ring
      exact this
    have hwk := stronglyTypical_implies_weakly_typical_bound μ Xs hXs hn_pos_nat x hx
    rw [h_cross_eq] at hwk
    exact hwk
  have h_HXemp_le : HXemp ≤ HX + ε_X * LX := by
    have h_cross_le : crossX ≤ HX + ε_X * LX := by
      have h := abs_sub_le_iff.mp h_cross_X_typ
      linarith [h.1]
    linarith
  -- ── Step (IV): typicality+KL on Z: HZemp ≥ HZ - ε_Z·LZ - KL(c/n‖qZ). ──
  set crossZ : ℝ := -∑ p : α × β, ((c p : ℕ) : ℝ) / n * Real.log (qZ p) with hcrossZ_def
  have h_cross_Z_typ : |crossZ - HZ| ≤ ε_Z * LZ := by
    have h_HZ_unfold : HZ = ∑ p : α × β, Real.negMulLog (qZ p) := by
      show entropy μ (jointSequence Xs Ys 0) = ∑ p : α × β, Real.negMulLog (qZ p)
      unfold entropy; rfl
    have h_eq : crossZ - HZ
        = ∑ p : α × β, (qZ p - ((c p : ℕ) : ℝ) / n) * Real.log (qZ p) := by
      rw [h_HZ_unfold, hcrossZ_def]
      -- Use sum_sub_distrib / Real.negMulLog at the elemen level.
      have h_each : ∀ p : α × β,
          (qZ p - ((c p : ℕ) : ℝ) / n) * Real.log (qZ p)
            = -(((c p : ℕ) : ℝ) / n * Real.log (qZ p)) - Real.negMulLog (qZ p) := by
        intro p; rw [Real.negMulLog]; ring
      rw [Finset.sum_congr rfl (fun p _ => h_each p)]
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have h_neg : ∑ p : α × β, (qZ p - ((c p : ℕ) : ℝ) / n) * Real.log (qZ p)
        = -∑ p : α × β, (((c p : ℕ) : ℝ) / n - qZ p) * Real.log (qZ p) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_; ring
    rw [h_eq, h_neg, abs_neg]
    have hLZ_eq : LZ = ∑ p : α × β, |Real.log (qZ p)| := by
      show logSumAbs μ (jointSequence Xs Ys) = ∑ p : α × β, |Real.log (qZ p)|
      rfl
    rw [hLZ_eq]
    exact sum_diff_log_abs_le_typicality
      (fun p => ((c p : ℕ) : ℝ) / n) qZ ε_Z hc_close
  -- KL upper bound (χ²-style).
  set KL_val : ℝ :=
    ∑ p : α × β, ((c p : ℕ) : ℝ) / n * Real.log ((((c p : ℕ) : ℝ) / n) / qZ p)
    with hKL_val_def
  have h_KL_chi : KL_val ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_Z^2 / qZ_min := by
    have h_p_nn : ∀ p ∈ (Finset.univ : Finset (α × β)), 0 ≤ ((c p : ℕ) : ℝ) / n :=
      fun p _ => div_nonneg (Nat.cast_nonneg _) hn_pos.le
    have h_q_pos : ∀ p ∈ (Finset.univ : Finset (α × β)), 0 < qZ p := fun p _ => hqZ_pos p
    have h_p_sum_eq : (∑ p : α × β, ((c p : ℕ) : ℝ) / n) = ∑ p : α × β, qZ p := by
      rw [← Finset.sum_div,
        show (∑ p : α × β, ((c p : ℕ) : ℝ)) = (n : ℝ) from by exact_mod_cast hc_total,
        div_self hn_ne, h_qZ_sum_one]
    have h_chi := KL_le_chi_square_finset (Finset.univ : Finset (α × β))
      (fun p => ((c p : ℕ) : ℝ) / n) qZ h_p_nn h_q_pos h_p_sum_eq
    refine le_trans h_chi ?_
    -- bound each summand by ε_Z²/qZ_min.
    have h_each : ∀ p ∈ (Finset.univ : Finset (α × β)),
        (((c p : ℕ) : ℝ) / n - qZ p)^2 / qZ p ≤ ε_Z^2 / qZ_min := by
      intro p _
      have h1 : |((c p : ℕ) : ℝ) / n - qZ p| ≤ ε_Z := hc_close p
      have h_sq : (((c p : ℕ) : ℝ) / n - qZ p)^2 ≤ ε_Z^2 := by
        rw [show (((c p : ℕ) : ℝ) / n - qZ p)^2
              = |((c p : ℕ) : ℝ) / n - qZ p|^2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      -- (diff)²/qZ p ≤ ε_Z²/qZ p ≤ ε_Z²/qZ_min.
      have h_num_le : (((c p : ℕ) : ℝ) / n - qZ p)^2 / qZ p ≤ ε_Z^2 / qZ p :=
        div_le_div_of_nonneg_right h_sq (hqZ_pos p).le
      have hε_Z_sq_nn : 0 ≤ ε_Z^2 := sq_nonneg _
      have h_denom_le : ε_Z^2 / qZ p ≤ ε_Z^2 / qZ_min := by
        apply div_le_div_of_nonneg_left hε_Z_sq_nn hqZ_min_pos (hqZ_min_le p)
      linarith
    calc ∑ p : α × β, (((c p : ℕ) : ℝ) / n - qZ p)^2 / qZ p
        ≤ ∑ p : α × β, ε_Z^2 / qZ_min := Finset.sum_le_sum h_each
      _ = ((Fintype.card (α × β) : ℕ) : ℝ) * (ε_Z^2 / qZ_min) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_Z^2 / qZ_min := by
          rw [Fintype.card_prod]; push_cast; ring
  -- HZemp = crossZ - KL_val.
  -- Pointwise: (c/n) · log(c/n) = (c/n) · log(qZ) + (c/n) · log((c/n)/qZ) (for c/n > 0).
  -- For c = 0, both sides are 0.
  have h_HZemp_eq : HZemp = crossZ - KL_val := by
    rw [hHZemp_def, hcrossZ_def, hKL_val_def]
    have h_each : ∀ p : α × β,
        ((c p : ℕ) : ℝ) / n * Real.log (((c p : ℕ) : ℝ) / n)
          = ((c p : ℕ) : ℝ) / n * Real.log (qZ p)
            + ((c p : ℕ) : ℝ) / n * Real.log ((((c p : ℕ) : ℝ) / n) / qZ p) := by
      intro p
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ ((c p : ℕ) : ℝ) / n from
        div_nonneg (Nat.cast_nonneg _) hn_pos.le) with hpos | hzero
      · rw [show ((c p : ℕ) : ℝ) / n * Real.log (qZ p)
              + ((c p : ℕ) : ℝ) / n * Real.log ((((c p : ℕ) : ℝ) / n) / qZ p)
            = ((c p : ℕ) : ℝ) / n
              * (Real.log (qZ p) + Real.log ((((c p : ℕ) : ℝ) / n) / qZ p))
            from by ring]
        rw [show Real.log (qZ p) + Real.log ((((c p : ℕ) : ℝ) / n) / qZ p)
              = Real.log (((c p : ℕ) : ℝ) / n) from by
          rw [Real.log_div hpos.ne' (hqZ_pos p).ne']; ring]
      · rw [← hzero]; ring
    rw [Finset.sum_congr rfl (fun p _ => h_each p)]
    rw [Finset.sum_add_distrib, neg_add]
    ring
  have h_HZemp_ge : HZemp ≥ HZ - ε_Z * LZ - KL_val := by
    have h_cross_ge : crossZ ≥ HZ - ε_Z * LZ := by
      have h := abs_sub_le_iff.mp h_cross_Z_typ
      linarith [h.2]
    linarith [h_HZemp_eq]
  -- ── Step (V): N domination of slack. ──
  -- Want: log card_real ≥ n·(HZ - HX) + |α|·|β|·LY - n·ε_X·LX - n·ε_X·LZ - n·hδ.
  -- Equivalent (via exp_le_exp + log_le_log) target after dividing by exp(-n·(HY + ε_amp·LY)):
  --   exp(-n·(HX + HY - HZ + slack)) ≤ card_real · exp(-n·(HY + ε_amp·LY)).
  -- Rearranged: card_real ≥ exp(n·(HZ - HX + slack' )) for slack' some expression.
  -- We'll work in log space.
  set ε_amp : ℝ := (Fintype.card α : ℝ) * ε_X
    + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / n with hε_amp_def
  -- slack_total (matches the target's exponent on the LHS):
  set slack : ℝ := (Fintype.card α : ℝ) * ε_X * LY + ε_X * LX + ε_X * LZ + hδ with hslack_def
  -- Algebraic identity: ε_amp - |α|·ε_X = |α|·|β|/n.
  have h_ε_amp_diff : ε_amp - (Fintype.card α : ℝ) * ε_X
      = (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / n := by
    rw [hε_amp_def]; ring
  -- Goal (after taking log + multiplying through):
  -- log card_real ≥ n·HZ - n·HX - n·(|α|·ε_X·LY + ε_X·LX + ε_X·LZ + hδ) + n·(HY + ε_amp·LY) - n·HY
  --              = n·HZ - n·HX - n·(ε_X·LX + ε_X·LZ + hδ) + n·(ε_amp - |α|·ε_X)·LY
  --              = n·HZ - n·HX - n·(ε_X·LX + ε_X·LZ + hδ) + |α|·|β|·LY.
  set target_lb : ℝ :=
    (n : ℝ) * HZ - (n : ℝ) * HX
      - (n : ℝ) * (ε_X * LX + ε_X * LZ + hδ)
      + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY with htarget_lb_def
  -- The main analytic content: log card_real ≥ target_lb.
  have h_log_card_target : target_lb ≤ Real.log card_real := by
    -- Combine h_log_card_lb with chain bounds.
    -- LHS of h_log_card_lb: n·(HZemp - HXemp) - |β|·∑_a log(T_a + 1).
    -- Chain bounds:
    --   HXemp ≤ HX + ε_X · LX  ⟹ -HXemp ≥ -HX - ε_X·LX
    --   HZemp ≥ HZ - ε_Z · LZ - KL  ⟹ HZemp - HXemp ≥ HZ - HX - ε_Z·LZ - KL - ε_X·LX
    --   KL ≤ |α|·|β|·ε_Z²/qZ_min
    --   ε_Z = ε_X + |β|/n ⟹ ε_Z·LZ = ε_X·LZ + (|β|/n)·LZ
    -- So:
    --   n·(HZemp - HXemp) ≥ n·HZ - n·HX - n·ε_X·LZ - |β|·LZ - n·KL - n·ε_X·LX
    -- And bound:
    --   n·KL ≤ n·|α|·|β|·ε_Z²/qZ_min
    --        ≤ n·|α|·|β|·ε_X²/qZ_min + 2·|α|·|β|²·ε_X/qZ_min + |α|·|β|³/(n·qZ_min)
    -- The first piece is ≤ n·hδ/8 by hδ_dominates_kl; the second and third by our Archimedean.
    -- And:
    --   |β|·∑_a log(T_a + 1) ≤ |α|·|β|·log(n+1)  ≤ n·hδ/4 by hN_log.
    --   |β|·LZ + |α|·|β|·LY ≤ n·hδ/4 by hN_const.
    -- All combined: log card ≥ target_lb.
    have h_HZ_HX_lb : (n : ℝ) * (HZemp - HXemp)
        ≥ (n : ℝ) * (HZ - HX) - (n : ℝ) * ε_X * LZ
          - (Fintype.card β : ℝ) * LZ - (n : ℝ) * KL_val
          - (n : ℝ) * ε_X * LX := by
      -- HZemp ≥ HZ - ε_Z · LZ - KL_val
      -- HXemp ≤ HX + ε_X · LX
      have h_diff : HZemp - HXemp ≥ (HZ - HX) - ε_Z * LZ - KL_val - ε_X * LX := by
        linarith
      have h_eZ : ε_Z * LZ = ε_X * LZ + (Fintype.card β : ℝ) / n * LZ := by
        show (ε_X + (Fintype.card β : ℝ) / n) * LZ = _
        ring
      have h_nε_Z_LZ : (n : ℝ) * (ε_Z * LZ) = (n : ℝ) * ε_X * LZ + (Fintype.card β : ℝ) * LZ := by
        rw [h_eZ]
        rw [show (n : ℝ) * (ε_X * LZ + (Fintype.card β : ℝ) / n * LZ)
              = (n : ℝ) * ε_X * LZ + (n : ℝ) * ((Fintype.card β : ℝ) / n * LZ)
            from by ring]
        congr 1
        rw [show (n : ℝ) * ((Fintype.card β : ℝ) / n * LZ)
              = ((n : ℝ) / n) * ((Fintype.card β : ℝ) * LZ) from by ring]
        rw [div_self hn_ne, one_mul]
      have h_lin : (n : ℝ) * (HZemp - HXemp)
          ≥ (n : ℝ) * ((HZ - HX) - ε_Z * LZ - KL_val - ε_X * LX) := by
        exact mul_le_mul_of_nonneg_left h_diff hn_pos.le
      have h_expand : (n : ℝ) * ((HZ - HX) - ε_Z * LZ - KL_val - ε_X * LX)
          = (n : ℝ) * (HZ - HX) - (n : ℝ) * (ε_Z * LZ) - (n : ℝ) * KL_val
            - (n : ℝ) * ε_X * LX := by ring
      linarith [h_nε_Z_LZ]
    -- Bound n · KL_val.
    have h_nKL_lb : (n : ℝ) * KL_val
        ≤ (n : ℝ) * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_Z^2 / qZ_min) :=
      mul_le_mul_of_nonneg_left h_KL_chi hn_pos.le
    -- Expand (n · ε_Z² / qZ_min · |α||β|):
    -- n · |α||β|(ε_X + |β|/n)² / qZ_min
    --   = n · |α||β| · ε_X²/qZ_min + 2·|α||β|² · ε_X/qZ_min + |α||β|³/(n·qZ_min).
    have h_nKL_expand : (n : ℝ) * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_Z^2 / qZ_min)
        = (n : ℝ) * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X^2 / qZ_min
          + 2 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^2 * ε_X / qZ_min
          + (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^3 / (n * qZ_min) := by
      rw [hε_Z_sq_expand]
      -- The LHS and RHS differ by powers of n that need n ≠ 0.
      have hqZ_ne : qZ_min ≠ 0 := hqZ_min_pos.ne'
      field_simp
    -- (D-main) n · |α||β| · ε_X² / qZ_min ≤ n · hδ/8.
    have h_KL_main : (n : ℝ) * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X^2 / qZ_min
        ≤ (n : ℝ) * (hδ / 8) := by
      -- From hδ_dominates_kl: 8|α||β|ε_X² ≤ hδ·qZ_min.
      -- So |α||β|ε_X²/qZ_min ≤ hδ/8 (when qZ_min > 0).
      have h0 : 8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ hδ * qZ_min := hδ_dominates_kl
      have h_div : (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2 / qZ_min ≤ hδ / 8 := by
        rw [div_le_div_iff₀ hqZ_min_pos (by linarith : (0 : ℝ) < 8)]
        linarith
      calc (n : ℝ) * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X^2 / qZ_min
          = (n : ℝ) * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X^2 / qZ_min) := by
            ring
        _ ≤ (n : ℝ) * (hδ / 8) := mul_le_mul_of_nonneg_left h_div hn_pos.le
    have h_KL_cross_le := hN_KL_cross n hn_N_KL_cross
    have h_KL_inv_le := hN_KL_inv n hn_N_KL_inv
    have h_nKL_total : (n : ℝ) * KL_val ≤ (n : ℝ) * (hδ / 8 + hδ / 8 + hδ / 8) := by
      calc (n : ℝ) * KL_val ≤ _ := h_nKL_lb
        _ = _ := h_nKL_expand
        _ ≤ (n : ℝ) * (hδ / 8) + (n : ℝ) * (hδ / 8)
              + (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^3 / (n * qZ_min) := by
            have := h_KL_main; have := h_KL_cross_le; linarith
        _ ≤ (n : ℝ) * (hδ / 8) + (n : ℝ) * (hδ / 8) + (n : ℝ) * (hδ / 8) := by
            have h_inv_lt : (Fintype.card α : ℝ) * (Fintype.card β : ℝ)^3 / (n * qZ_min)
                ≤ (n : ℝ) * (hδ / 8) := by
              have h := h_KL_inv_le
              have : 1 * (hδ / 8) ≤ (n : ℝ) * (hδ / 8) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hn_pos_nat) (by linarith)
              linarith
            linarith
        _ = (n : ℝ) * (hδ / 8 + hδ / 8 + hδ / 8) := by ring
    -- |β| · ∑_a log(T_a+1) ≤ |α|·|β|·log(n+1) ≤ n·hδ/4 (using hN_log).
    have h_logT_bound : (Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1)
        ≤ (n : ℝ) * (hδ / 4) := by
      have h_sum_le := h_logT_sum_le
      have h_mul : (Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1)
          ≤ (Fintype.card β : ℝ) * ((Fintype.card α : ℝ) * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h_sum_le hβ_nn
      -- |α||β| log(n+1) ≤ n · hδ/4.
      have h_log := hN_log n hn_N_log
      -- log(n+1)/n ≤ hδ / (4|α||β|).
      -- So log(n+1) ≤ n · hδ / (4|α||β|), i.e. |α||β| · log(n+1) ≤ n · hδ/4.
      -- h_log says log(n+1)/n ≤ hδ/(4|α||β|).
      -- Multiply both sides by 4·|α|·|β|·n (positive) to get:
      --   log(n+1) · 4|α||β| ≤ hδ · n   (and then divide by 4 to get our target).
      have h4αβ_pos : (0 : ℝ) < 4 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := by
        have : (0 : ℝ) < 4 * (Fintype.card α : ℝ) := by linarith
        nlinarith [hβ_pos]
      have h_log_nn : 0 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_nonneg (by linarith)
      -- From log(n+1)/n ≤ hδ/(4|α||β|), multiply by n: log(n+1) ≤ n · hδ/(4|α||β|).
      have h_log_mul_n : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) * (hδ / (4 * (Fintype.card α : ℝ)
            * (Fintype.card β : ℝ))) := by
        have := hN_log n hn_N_log
        rw [div_le_iff₀ hn_pos] at this
        linarith
      -- Now |α||β| · log(n+1) ≤ |α||β| · n · hδ/(4|α||β|) = n · hδ/4.
      have h_target_eq : (Fintype.card α : ℝ) * (Fintype.card β : ℝ)
            * ((n : ℝ) * (hδ / (4 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ))))
          = (n : ℝ) * (hδ / 4) := by
        have hα_ne : (Fintype.card α : ℝ) ≠ 0 := hα_pos.ne'
        have hβ_ne : (Fintype.card β : ℝ) ≠ 0 := hβ_pos.ne'
        field_simp
      have hKey : (Fintype.card β : ℝ) * ((Fintype.card α : ℝ) * Real.log ((n : ℝ) + 1))
          ≤ (n : ℝ) * (hδ / 4) := by
        have h1 : (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * Real.log ((n : ℝ) + 1)
            ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ)
                * ((n : ℝ) * (hδ / (4 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ)))) :=
          mul_le_mul_of_nonneg_left h_log_mul_n (by positivity)
        rw [h_target_eq] at h1
        linarith
      linarith
    -- Combine: log card_real ≥ n·HZ - n·HX - n·ε_X·LZ - |β|·LZ - n·KL - n·ε_X·LX - |β|·∑log(T+1).
    -- ≥ n·HZ - n·HX - n·ε_X·LZ - |β|·LZ - n·(3hδ/8) - n·ε_X·LX - n·hδ/4
    -- Target: n·HZ - n·HX - n·ε_X·LX - n·ε_X·LZ - n·hδ + |α|·|β|·LY.
    -- Need: -|β|·LZ - n·(3hδ/8) - n·hδ/4 ≥ -n·hδ + |α|·|β|·LY
    --   ⟺ n·hδ - n·(3hδ/8) - n·hδ/4 ≥ |β|·LZ + |α|·|β|·LY
    --   ⟺ n·(hδ - 3hδ/8 - hδ/4) = n·(3hδ/8) ≥ |β|·LZ + |α|·|β|·LY.
    -- And we have hN_const: (|β|·LZ + |α|·|β|·LY)/n ≤ hδ/4. So we get:
    --   |β|·LZ + |α|·|β|·LY ≤ n·hδ/4 ≤ n·(3hδ/8) ✓.
    have h_const_bound : (Fintype.card β : ℝ) * LZ
          + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY ≤ (n : ℝ) * (hδ / 4) := by
      have h := hN_const n hn_N_const
      rw [div_le_iff₀ hn_pos] at h
      linarith
    -- Now combine all.
    have hgoal : target_lb ≤ (n : ℝ) * HZemp - (n : ℝ) * HXemp
        - (Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1) := by
      -- target_lb = n·HZ - n·HX - n·(ε_X·LX + ε_X·LZ + hδ) + |α|·|β|·LY
      have h_target_expand : target_lb
          = (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LX
            - (n : ℝ) * ε_X * LZ - (n : ℝ) * hδ
            + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY := by
        rw [htarget_lb_def]; ring
      have h_split : (n : ℝ) * (HZemp - HXemp) = (n : ℝ) * HZemp - (n : ℝ) * HXemp := by ring
      rw [h_target_expand]
      have hHZHX := h_HZ_HX_lb
      have key : (n : ℝ) * HZemp - (n : ℝ) * HXemp
          ≥ (n : ℝ) * (HZ - HX) - (n : ℝ) * ε_X * LZ
            - (Fintype.card β : ℝ) * LZ - (n : ℝ) * KL_val
            - (n : ℝ) * ε_X * LX := by linarith
      have h_nHZ_HX : (n : ℝ) * (HZ - HX) = (n : ℝ) * HZ - (n : ℝ) * HX := by ring
      -- We want: target_expand ≤ n·HZemp - n·HXemp - |β| · ∑ log(T+1).
      -- From key and the bounds:
      -- n·HZemp - n·HXemp ≥ n·HZ - n·HX - n·ε_X·LZ - |β|·LZ - n·KL - n·ε_X·LX
      -- |β|·∑log(T+1) ≤ n·hδ/4 (from h_logT_bound)
      -- n·KL ≤ n·(3hδ/8)
      -- |β|·LZ + |α|·|β|·LY ≤ n·hδ/4 (from h_const_bound)
      have h_alt : (n : ℝ) * HZemp - (n : ℝ) * HXemp
            - (Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1)
          ≥ (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LZ
            - (Fintype.card β : ℝ) * LZ - (n : ℝ) * KL_val
            - (n : ℝ) * ε_X * LX
            - (n : ℝ) * (hδ / 4) := by linarith
      -- Now show RHS of h_alt ≥ target_expand:
      -- RHS = n·HZ - n·HX - n·ε_X·LZ - |β|·LZ - n·KL - n·ε_X·LX - n·hδ/4
      -- Target = n·HZ - n·HX - n·ε_X·LX - n·ε_X·LZ - n·hδ + |α|·|β|·LY
      -- Diff: RHS - Target = -|β|·LZ - n·KL - n·hδ/4 + n·hδ - |α|·|β|·LY
      --     = n·(3hδ/4) - n·KL - |β|·LZ - |α|·|β|·LY
      -- From h_const_bound: |β|·LZ + |α|·|β|·LY ≤ n·hδ/4.
      -- From n·KL ≤ n·(3hδ/8).
      -- So diff ≥ n·(3hδ/4) - n·(3hδ/8) - n·hδ/4 = n·(3hδ/4 - 3hδ/8 - hδ/4) = n·hδ/8 ≥ 0.
      -- Normalize h_nKL_total: n * (hδ/8 + hδ/8 + hδ/8) = 3 * n * hδ / 8.
      have h_nKL_3_8 : (n : ℝ) * KL_val ≤ 3 * (n : ℝ) * hδ / 8 := by
        have h := h_nKL_total
        have heq : (n : ℝ) * (hδ / 8 + hδ / 8 + hδ / 8) = 3 * (n : ℝ) * hδ / 8 := by ring
        linarith [heq]
      have h_n_hδ_pos : 0 ≤ (n : ℝ) * (hδ / 8) := by
        have : 0 < (n : ℝ) * (hδ / 8) := mul_pos hn_pos (by linarith)
        exact this.le
      have h_diff_pos : (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LZ
            - (Fintype.card β : ℝ) * LZ - (n : ℝ) * KL_val
            - (n : ℝ) * ε_X * LX - (n : ℝ) * (hδ / 4)
          ≥ ((n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LX
              - (n : ℝ) * ε_X * LZ - (n : ℝ) * hδ
              + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY) := by
        -- After cancellation: -|β|·LZ - n·KL - n·hδ/4 + n·hδ - |α|·|β|·LY ≥ 0.
        -- ⟺ 3·n·hδ/4 ≥ |β|·LZ + n·KL + |α|·|β|·LY (from h_const_bound, h_nKL_3_8).
        nlinarith [h_const_bound, h_nKL_3_8, h_n_hδ_pos, hn_pos, hδ_pos]
      linarith [h_alt, h_diff_pos]
    exact le_trans hgoal h_log_card_lb
  -- ── Step (VI): exponentiate and finish. ──
  -- card_real ≥ exp(target_lb) (via Real.exp_log + Real.log_le_log).
  have hcard_pos : 0 < card_real := lt_of_lt_of_le hrowProd_pos h_card_ge_prod
  have hcard_exp_ge : Real.exp target_lb ≤ card_real := by
    rw [← Real.exp_log hcard_pos]
    exact Real.exp_le_exp.mpr h_log_card_target
  -- Final arithmetic: target_lb + (-n·(HY + ε_amp·LY)) = -n·(HX + HY - HZ + slack).
  have h_exp_match : target_lb + (-(n : ℝ) * (HY + ε_amp * LY))
      = -(n : ℝ) * (HX + HY - HZ + slack) := by
    rw [htarget_lb_def, hε_amp_def, hslack_def]
    field_simp
    ring
  -- Final: LHS = exp(-n·(HX+HY-HZ+slack)) ≤ card · exp(-n·(HY + ε_amp·LY)).
  have h_exp_factor : Real.exp (-(n : ℝ) * (HX + HY - HZ + slack))
      = Real.exp target_lb * Real.exp (-(n : ℝ) * (HY + ε_amp * LY)) := by
    rw [← Real.exp_add, h_exp_match]
  -- Goal: exp(-n·(HX + HY - HZ + (|α|·ε_X·LY + ε_X·LX + ε_X·LZ + hδ)))
  --       ≤ card_real · exp(-n·(HY + ε_amp·LY)).
  -- (Local `set` abbreviations should have already rewritten the goal to use
  --  HX, HY, HZ, LX, LY, LZ, ε_amp; only `slack` shape needs aligning.)
  show Real.exp (-(n : ℝ) * (HX + HY - HZ + slack))
        ≤ card_real * Real.exp (-(n : ℝ) * (HY + ε_amp * LY))
  rw [h_exp_factor]
  exact mul_le_mul_of_nonneg_right hcard_exp_ge (Real.exp_nonneg _)

/-- **Conditional slice mass lower bound (Cover-Thomas 10.6.1, strong form,
mutual-information form).** For `x` X-strongly-typical and `Y ∼ μ.map (Ys 0)^n`
i.i.d., the Y-product mass of the joint strongly-typical slice at `x` is bounded
below by `exp(-n · (I(X;Y) + slack)) = exp(-n · (H(X) + H(Y) - H(Z) + slack))`,
eventually in `n` (the slack absorbs the polynomial floor error and the
`(n+1)^{|α||β|}` cardinality factor).

The eventual quantification (`∃ N, ∀ n ≥ N`) parallels
`jointStronglyTypicalSet_indep_prob_ge`. The auxiliary slack is the same shape:
each of `ε`-times-`logSumAbs` terms (Lipschitz amplification through
strong⇒weak), and an extra free `δ > 0` to absorb polynomial corrections. -/
@[entry_point]
theorem conditionalStronglyTypicalSlice_mass_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep_Z_pair : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hident_Z : ∀ i, IdentDistrib (jointSequence Xs Ys i)
                                  (jointSequence Xs Ys 0) μ μ)
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (hposX : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    (hposY : ∀ b : β, 0 < (μ.map (Ys 0)).real {b})
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {ε ε_X δ : ℝ}
    (hε : 0 < ε) (hε_X : 0 ≤ ε_X) (hε_X_lt_ε : ε_X < ε) (hδ : 0 < δ)
    -- Caller-supplied `qZ_min > 0` bound + smallness of `ε_X` relative to the
    -- slack `δ` and `qZ_min`. See `conditional_KL_concentration_ge` for the
    -- rationale (chi-square KL upper bound is `O(ε_X²/qZ_min)`).
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β, qZ_min ≤ (μ.map (jointSequence Xs Ys 0)).real {p})
    (hδ_dominates_kl :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ * qZ_min) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (x : Fin n → α),
      x ∈ stronglyTypicalSet μ Xs n ε_X →
      Real.exp (-(n : ℝ) *
          (entropy μ (Xs 0) + entropy μ (Ys 0)
            - entropy μ (jointSequence Xs Ys 0)
            + ((Fintype.card α : ℝ) * ε_X * logSumAbs μ Ys
               + ε_X * logSumAbs μ Xs
               + ε_X * logSumAbs μ (jointSequence Xs Ys)
               + δ)))
        ≤ (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real
              (conditionalStronglyTypicalSlice μ Xs Ys n ε x) := by
  classical
  set qZ : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
  -- Choose N large enough that `|β|/n ≤ ε - ε_X` (so c_floor stays in sliceTypeIndices).
  have h_diff_pos : 0 < ε - ε_X := by linarith
  obtain ⟨N_KL, hN_KL⟩ := conditional_KL_concentration_ge μ Xs Ys hXs hYs hposZ
    hmarg_X hmarg_Y hε hε_X δ hδ qZ_min hqZ_min_pos hqZ_min_le hδ_dominates_kl
  obtain ⟨N_slice, hN_slice⟩ :
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Fintype.card β : ℝ) / n ≤ ε - ε_X := by
    -- (|β| / n) ≤ ε - ε_X eventually.
    have h_card_nn : (0 : ℝ) ≤ Fintype.card β := Nat.cast_nonneg _
    have h_archimedean : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Fintype.card β : ℝ) ≤ n * (ε - ε_X) := by
      obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card β : ℝ) / (ε - ε_X))
      refine ⟨max N 1, fun n hn => ?_⟩
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have hN_le : N ≤ n := le_of_max_le_left hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hN_lt : (Fintype.card β : ℝ) / (ε - ε_X) < (n : ℝ) :=
        lt_of_lt_of_le hN (by exact_mod_cast hN_le)
      rw [div_lt_iff₀ h_diff_pos] at hN_lt
      linarith
    obtain ⟨N, hN⟩ := h_archimedean
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hN_le : N ≤ n := le_of_max_le_left hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_le_iff₀ hn_pos]
    have := hN n hN_le
    linarith
  refine ⟨max (max N_KL N_slice) 1, fun n hn_ge x hx => ?_⟩
  have hn_pos : 0 < n := by
    have : 1 ≤ n := le_of_max_le_right hn_ge
    omega
  have hn_N_KL : N_KL ≤ n := le_of_max_le_left (le_of_max_le_left hn_ge)
  have hn_N_slice : N_slice ≤ n := le_of_max_le_right (le_of_max_le_left hn_ge)
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  -- Set c_floor := floorMatrix qZ x.
  set c_floor : α × β → ℕ := fun p => floorMatrix qZ x p.1 p.2 with hc_floor_def
  -- Step 1: c_floor ∈ sliceTypeIndices.
  have h_floor_close : ∀ p : α × β,
      |((c_floor p : ℕ) : ℝ) / n - qZ p| ≤ ε_X + (Fintype.card β : ℝ) / n := by
    intro p
    obtain ⟨a, b⟩ := p
    exact floorMatrix_dist_le μ Xs Ys hXs hYs hposZ hmarg_X hn_pos hε_X x hx a b
  have h_c_le : ∀ p : α × β, c_floor p ≤ n := by
    intro p
    rcases p with ⟨a, b⟩
    have h_row_sum : (∑ b' : β, floorMatrix qZ x a b') = typeCount x a :=
      floorMatrix_row_sum qZ (fun p' => (hposZ p').le) x a
    have h_single : floorMatrix qZ x a b ≤ ∑ b' : β, floorMatrix qZ x a b' :=
      Finset.single_le_sum (f := fun b' => floorMatrix qZ x a b')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have h_T_le : typeCount x a ≤ n := by
      unfold typeCount
      have h1 : (Finset.univ.filter (fun i : Fin n => x i = a)).card ≤
          (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      rw [Finset.card_univ, Fintype.card_fin] at h1
      exact h1
    calc c_floor (a, b) = floorMatrix qZ x a b := rfl
      _ ≤ ∑ b' : β, floorMatrix qZ x a b' := h_single
      _ = typeCount x a := h_row_sum
      _ ≤ n := h_T_le
  -- Lift c_floor to TypeCountIndex (= α × β → Fin (n+1)).
  let c_idx : TypeCountIndex (α × β) n := fun p => ⟨c_floor p, by
    have := h_c_le p; omega⟩
  have h_c_idx_eq : ∀ p, (c_idx p : ℕ) = c_floor p := fun _ => rfl
  have h_floor_in_slice : c_idx ∈ sliceTypeIndices μ Xs Ys n ε := by
    unfold sliceTypeIndices
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro p
    -- |c_floor p / n - qZ p| ≤ ε_X + |β|/n ≤ ε_X + (ε - ε_X) = ε.
    have h1 := h_floor_close p
    have h2 : (Fintype.card β : ℝ) / n ≤ ε - ε_X := hN_slice n hn_N_slice
    have h_cast : ((c_idx p : ℕ) : ℝ) = ((c_floor p : ℕ) : ℝ) := by
      rw [h_c_idx_eq]
    rw [h_cast]
    linarith
  -- Step 2: slice mass ≥ mass(conditionalTypeClass x c_floor).
  set Cset : Set (Fin n → β) := conditionalTypeClass (β := β) x c_floor with hCset_def
  have h_subset : Cset ⊆ conditionalStronglyTypicalSlice μ Xs Ys n ε x := by
    rw [conditionalStronglyTypicalSlice_eq_biUnion]
    intro y hy
    -- y ∈ Cset = conditionalTypeClass x c_floor; want ∈ ⋃ c ∈ slice, conditionalTypeClass x (c : ℕ).
    -- Note: c_idx : TypeCountIndex (α × β) n; (fun p => (c_idx p : ℕ)) = c_floor by defeq.
    have h_idx_unfold : (fun p => ((c_idx p : Fin (n + 1)) : ℕ)) = c_floor := by
      funext p; rfl
    refine Set.mem_iUnion.mpr ⟨c_idx, Set.mem_iUnion.mpr ⟨h_floor_in_slice, ?_⟩⟩
    rw [h_idx_unfold]
    exact hy
  have h_mass_mono :
      (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real Cset
        ≤ (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real
            (conditionalStronglyTypicalSlice μ Xs Ys n ε x) :=
    measureReal_mono (μ := Measure.pi (fun _ : Fin n => μ.map (Ys 0))) h_subset
  -- Step 3: Cset is finite, mass(Cset) = ∑_{y ∈ Cset.toFinset} (μ_Y^n).real {y}.
  have h_Cset_fin : Cset.Finite := conditionalTypeClass_finite x c_floor
  set Cfin : Finset (Fin n → β) := h_Cset_fin.toFinset with hCfin_def
  have h_mass_sum :
      (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real Cset
        = ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y} := by
    have h_coe : (Cfin : Set (Fin n → β)) = Cset := h_Cset_fin.coe_toFinset
    rw [← h_coe, ← sum_measureReal_singleton
      (μ := Measure.pi (fun _ : Fin n => μ.map (Ys 0))) Cfin]
  -- Step 4: per-y mass lower bound — use productMass_columnProd_ge.
  -- Set ε_amp := |α|·ε_X + |α|·|β|/n.
  set ε_amp : ℝ :=
    (Fintype.card α : ℝ) * ε_X
    + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / n with hε_amp_def
  have hε_amp_nn : 0 ≤ ε_amp := by
    have h1 : 0 ≤ (Fintype.card α : ℝ) * ε_X :=
      mul_nonneg (Nat.cast_nonneg _) hε_X
    have h2 : 0 ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / n := by
      refine div_nonneg ?_ hn_R_pos.le
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have h_floor_close_for_perY : ∀ p : α × β,
      |((c_floor p : ℕ) : ℝ) / n - qZ p| ≤ ε_amp / (Fintype.card α : ℝ) := by
    intro p
    have h := h_floor_close p
    have hα_pos : (0 : ℝ) < Fintype.card α := by
      have : (0 : ℕ) < Fintype.card α := Fintype.card_pos
      exact_mod_cast this
    -- ε_amp / |α| = ε_X + |β|/n
    have h_eq : ε_amp / (Fintype.card α : ℝ) = ε_X + (Fintype.card β : ℝ) / n := by
      rw [hε_amp_def]
      field_simp
    rw [h_eq]
    exact h
  have h_per_y : ∀ y ∈ Cfin,
      Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys))
        ≤ (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y} := by
    intro y hy
    have hy_set : y ∈ Cset := h_Cset_fin.mem_toFinset.mp hy
    exact productMass_columnProd_ge μ Xs Ys hposY hmarg_Y hn_pos hε_amp_nn
      c_floor h_floor_close_for_perY x hy_set
  -- Step 5: Sum the per-y bounds, get card × exp(-n(HY + ε_amp · LY)) ≤ ∑ y ∈ Cfin, mass {y}.
  have h_card_mass :
      (Cfin.card : ℝ) *
          Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys))
        ≤ ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y} := by
    calc (Cfin.card : ℝ) *
            Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys))
        = ∑ _y ∈ Cfin,
            Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y} :=
          Finset.sum_le_sum h_per_y
  -- Step 6: combine with the entropy-concentration lemma to get the target bound.
  have h_KL :=
    hN_KL n hn_N_KL x hx
  -- h_KL says: card · exp(-n(HY + ε_amp · LY)) ≥ exp(-n(HX + HY - HZ + slack)).
  -- The card in h_KL is given via Set.Finite.toFinset (the finiteness witness from
  -- `conditionalTypeClass_finite`); the card we have via `Cfin` uses the same set,
  -- so the cards are propositionally equal.
  have h_card_eq_KL : ((Set.Finite.toFinset
            (conditionalTypeClass_finite (β := β) x c_floor)).card : ℝ)
        = (Cfin.card : ℝ) := by
    rfl
  rw [h_card_eq_KL] at h_KL
  -- Now combine: target ≤ card · exp(-n(HY + ε_amp · LY)) ≤ ∑ y ∈ Cfin, ... = mass(Cset) ≤ mass(slice).
  calc Real.exp (-(n : ℝ) *
        (entropy μ (Xs 0) + entropy μ (Ys 0)
          - entropy μ (jointSequence Xs Ys 0)
          + ((Fintype.card α : ℝ) * ε_X * logSumAbs μ Ys
            + ε_X * logSumAbs μ Xs
            + ε_X * logSumAbs μ (jointSequence Xs Ys)
            + δ)))
      ≤ (Cfin.card : ℝ)
            * Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys)) :=
        h_KL
    _ ≤ ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real {y} :=
        h_card_mass
    _ = (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real Cset := h_mass_sum.symm
    _ ≤ (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real
            (conditionalStronglyTypicalSlice μ Xs Ys n ε x) := h_mass_mono

end InformationTheory.Shannon
