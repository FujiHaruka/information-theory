import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.StrongTypicality
import InformationTheory.Shannon.Sanov.LDPEquality
import InformationTheory.Shannon.TypeClassLowerBound
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseEStrong

/-!
# Conditional method of types — Core

Definitions and structural lemmas for the conditional method of types:
conditional type classes, marginal sums, the slice partition, the floor-matrix
construction, per-row multinomial cardinality, and the per-`y` Y-product mass
identity. Downstream assembly lives in
`InformationTheory.Shannon.ConditionalMethodOfTypes.Mass`.

This file is part of the `ConditionalMethodOfTypes` umbrella; see that module
for the headline theorem `conditionalStronglyTypicalSlice_mass_ge`.
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
/-! ## Conditional type-class basics + joint type bridge -/

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

/-! ## Marginal sums of joint type -/

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

/-! ## Slice partition by joint type -/

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

/-! ## Slice cardinality (polynomial number of joint types) -/

/-! ## Per-fiber slice mass lower bound (main theorem)

The entropy-concentration helper `conditional_KL_concentration_ge` is discharged
via the χ²-style KL upper bound and an Archimedean N-choice for the three
vanishing slack terms (`log(n+1)/n → 0`, `1/n → 0`, and the constant Lipschitz
amplification).

The pieces assembled here (`floorMatrix` + `floorMatrix_row_sum` +
`floorMatrix_total` + `productMass_eq_columnProd` + `conditionalTypeClass_card_ge`
+ `conditionalStronglyTypicalSlice_mass_ge`) yield the Cover–Thomas 10.6.1 form
for downstream consumers.

### Note on the entropy form

The bound is sometimes paraphrased as
`exp(-n · (H(Z) - H(X) + slack)) = exp(-n · (H(Y|X) + slack))`.
That paraphrase is **incorrect**: when `X = Y` deterministically (a degenerate
but legal case), `H(Y|X) = 0` so the paraphrased bound demands `mass ≥ exp(-n·slack)
≈ 1`, but the actual mass is `≈ exp(-n · H(X))`. The correct form (used here)
is `exp(-n · I(X;Y))`, which yields `mass ≥ exp(-n·H(X)) · poly(n)⁻¹` in that
case (consistent with the truth). -/

/-! ### Floor matrix construction

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

lemma sum_real_prod_singleton_of_map_fst_eq
    (ν : Measure (α × β)) [IsFiniteMeasure ν] (νX : Measure α)
    (hmarg : ν.map Prod.fst = νX) (a : α) :
    (∑ b' : β, ν.real {(a, b')}) = νX.real {a} := by
  classical
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
  have h_map : (ν.map Prod.fst).real {a} = ν.real (Prod.fst ⁻¹' {a}) :=
    map_measureReal_apply measurable_fst (MeasurableSet.singleton a)
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
  have h_sum : ν.real (Prod.fst ⁻¹' {a}) = ∑ b' : β, ν.real {(a, b')} := by
    rw [h_pre]
    rw [measureReal_biUnion_finset h_disj h_meas]
  rw [← hmarg, h_map, h_sum]

lemma abs_floor_mul_div_sub_mul_le_of_abs_div_sub_le
    (Ta : ℕ) (q s ε : ℝ) {n : ℕ} (hn_pos : (0 : ℝ) < n)
    (hs_nn : 0 ≤ s) (hs_le : s ≤ 1) (hε : 0 ≤ ε)
    (h_slack : |(Ta : ℝ) / n - q| ≤ ε) :
    |((Nat.floor ((Ta : ℝ) * s) : ℕ) : ℝ) / n - q * s|
      ≤ ε + 1 / n := by
  have h_floor_le : (Nat.floor ((Ta : ℝ) * s) : ℝ) ≤ (Ta : ℝ) * s :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hs_nn)
  have h_floor_lt_succ : (Ta : ℝ) * s < (Nat.floor ((Ta : ℝ) * s) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h_slack_mul : |((Ta : ℝ) / n - q) * s| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hs_nn]
    calc |(Ta : ℝ) / n - q| * s
        ≤ ε * s := mul_le_mul_of_nonneg_right h_slack hs_nn
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hs_le hε
      _ = ε := by ring
  have h_decomp : ((Nat.floor ((Ta : ℝ) * s) : ℕ) : ℝ) / n - q * s
      = ((Nat.floor ((Ta : ℝ) * s) : ℝ) - (Ta : ℝ) * s) / n
        + ((Ta : ℝ) / n - q) * s := by
    field_simp
    ring
  rw [h_decomp]
  refine (abs_add_le _ _).trans ?_
  have h1 : |((Nat.floor ((Ta : ℝ) * s) : ℝ) - (Ta : ℝ) * s) / n| ≤ 1 / n := by
    rw [abs_div, abs_of_pos hn_pos]
    apply div_le_div_of_nonneg_right _ hn_pos.le
    rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
  linarith

lemma abs_cast_sub_floor_sum_div_sub_mul_le_of_sum_eq_one
    (Ta : ℕ) (q ε : ℝ) (r : β → ℝ) (b₀ : β) {n : ℕ} (hn_pos : (0 : ℝ) < n)
    (hr_nn : ∀ b', 0 ≤ r b') (hr_le_one : ∀ b', r b' ≤ 1) (hsum_r : (∑ b' : β, r b') = 1)
    (hε : 0 ≤ ε) (h_slack : |(Ta : ℝ) / n - q| ≤ ε) :
    |((Ta : ℝ) - ((∑ b' ∈ Finset.univ.erase b₀,
          Nat.floor ((Ta : ℝ) * r b') : ℕ) : ℝ)) / n - q * r b₀|
      ≤ ε + (Fintype.card β : ℝ) / n := by
  classical
  have h_floor_le : ∀ b', (Nat.floor ((Ta : ℝ) * r b') : ℝ) ≤ (Ta : ℝ) * r b' :=
    fun b' => Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hr_nn b'))
  have h_floor_lt_succ : ∀ b',
      (Ta : ℝ) * r b' < (Nat.floor ((Ta : ℝ) * r b') : ℝ) + 1 :=
    fun b' => Nat.lt_floor_add_one _
  have h_decomp :
      ((Ta : ℝ) - ((∑ b' ∈ Finset.univ.erase b₀,
            Nat.floor ((Ta : ℝ) * r b') : ℕ) : ℝ)) / n - q * r b₀
        = ((Ta : ℝ) / n - q) * r b₀
            + (∑ b' ∈ Finset.univ.erase b₀,
                ((Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ))) / n := by
    have h_S_real : ((∑ b' ∈ Finset.univ.erase b₀,
          Nat.floor ((Ta : ℝ) * r b') : ℕ) : ℝ)
        = ∑ b' ∈ Finset.univ.erase b₀, (Nat.floor ((Ta : ℝ) * r b') : ℝ) := by
      push_cast; rfl
    rw [h_S_real]
    have h_Ta_r_sum : (Ta : ℝ) * r b₀ + ∑ b' ∈ Finset.univ.erase b₀, (Ta : ℝ) * r b'
        = (Ta : ℝ) := by
      have h_pull : ∑ b' ∈ Finset.univ.erase b₀, (Ta : ℝ) * r b'
          = (Ta : ℝ) * ∑ b' ∈ Finset.univ.erase b₀, r b' := by
        rw [Finset.mul_sum]
      rw [h_pull, ← mul_add]
      rw [Finset.add_sum_erase _ (fun b' => r b') (Finset.mem_univ b₀)]
      rw [hsum_r, mul_one]
    rw [Finset.sum_sub_distrib]
    field_simp
    linarith [h_Ta_r_sum]
  rw [h_decomp]
  refine (abs_add_le _ _).trans ?_
  have h_first : |((Ta : ℝ) / n - q) * r b₀| ≤ ε := by
    rw [abs_mul, abs_of_nonneg (hr_nn b₀)]
    calc |(Ta : ℝ) / n - q| * r b₀
        ≤ ε * r b₀ := mul_le_mul_of_nonneg_right h_slack (hr_nn b₀)
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (hr_le_one b₀) hε
      _ = ε := by ring
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
  have h_card_le : (((Finset.univ : Finset β).erase b₀).card : ℝ)
      ≤ (Fintype.card β : ℝ) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    exact_mod_cast Nat.sub_le _ _
  have h_second : |(∑ b' ∈ Finset.univ.erase b₀,
          ((Ta : ℝ) * r b' - (Nat.floor ((Ta : ℝ) * r b') : ℝ))) / n|
      ≤ (Fintype.card β : ℝ) / n := by
    rw [abs_div, abs_of_pos hn_pos]
    apply div_le_div_of_nonneg_right _ hn_pos.le
    rw [abs_of_nonneg h_sum_nn]
    exact h_sum_le_card.trans h_card_le
  linarith

/-- **Joint type close to qZ**: For `x` X-strongly-typical at slack `ε_X` with
matching X-marginals, each entry of `floorMatrix qZ x` satisfies
`|floorMatrix x a b / n - qZ(a, b)| ≤ ε_X + |β| / n`. -/
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
  have h_qXa_eq : qXa = qX a :=
    sum_real_prod_singleton_of_map_fst_eq (μ.map (jointSequence Xs Ys 0)) (μ.map (Xs 0))
      hmarg_X a
  -- typeCount x a / n - qX a slack bound from X-strong typicality.
  have hx_slack : |(typeCount x a : ℝ) / n - qX a| ≤ ε_X := hx a
  set Ta : ℕ := typeCount x a with hTa_def
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
  -- Helper bound: |c/n - qZ(a,b)| ≤ ε_X + 1/n when c = floor(T_a · r(b)) and b ≠ b₀.
  have h_off_bound : ∀ b' : β,
      |((Nat.floor ((Ta : ℝ) * r b') : ℕ) : ℝ) / n - qZ (a, b')|
        ≤ ε_X + 1 / n := by
    intro b'
    have h_qZ_eq : qZ (a, b') = qXa * r b' := by
      rw [hr_def]; field_simp
    rw [h_qZ_eq]
    exact abs_floor_mul_div_sub_mul_le_of_abs_div_sub_le Ta qXa (r b') ε_X hn_pos
      (hr_nn b') (hr_le_one b') hε_X (by rw [h_qXa_eq]; exact hx_slack)
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
    have h_sum_r : (∑ b' : β, r b') = 1 := by
      rw [hr_def]
      rw [← Finset.sum_div]
      rw [show (∑ b' : β, qZ (a, b')) = qXa from rfl]
      field_simp
    rw [hS_def]
    exact abs_cast_sub_floor_sum_div_sub_mul_le_of_sum_eq_one Ta qXa ε_X r b₀ hn_pos
      hr_nn hr_le_one h_sum_r hε_X (by rw [h_qXa_eq]; exact hx_slack)
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

/-! ### Per-row multinomial cardinality

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

/-! ### Per-y Y-product mass identity -/

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

end InformationTheory.Shannon
