import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Sanov.LDP
import InformationTheory.Shannon.KLDivContinuous
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Fin

/-!
# Rounded type sequence (achievable type index)

The achievable type sequence `roundedTypeIndex P n` for Sanov's theorem
(Cover-Thomas Theorem 11.4.1), built by floor rounding with a single absorber
letter to satisfy the sum constraint exactly.

## Implementation notes

* The achievable type sequence `roundedTypeIndex P n` is built by floor rounding
  with a single absorber letter to satisfy the sum constraint exactly.
* `roundedTypeIndex_dist_le` / `roundedTypeIndex_tendsto` show the rounded type
  index converges to `P` pointwise (and in the `α → ℝ` Pi-topology).
* `klDivIndex_rounded_tendsto` lifts this to KL-divergence convergence via
  `klDivSumForm_ofVec` continuity.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Rounded type sequence (achievable type index) -/

/-- Default "absorber" letter for the rounded type index: any element of the
nonempty Fintype `α`. -/
private noncomputable def absorberLetter (α : Type*) [Nonempty α] : α :=
  Classical.choice (inferInstance : Nonempty α)

/-- Floor-rounding of `n · P a`. -/
private noncomputable def roundedFloor (P : α → ℝ) (n : ℕ) (a : α) : ℕ :=
  Nat.floor ((n : ℝ) * P a)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
private lemma roundedFloor_le_real (P : α → ℝ) (n : ℕ) (a : α)
    (hP_nn : 0 ≤ P a) :
    (roundedFloor P n a : ℝ) ≤ (n : ℝ) * P a := by
  unfold roundedFloor
  exact Nat.floor_le (by positivity)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
private lemma roundedFloor_lt_succ (P : α → ℝ) (n : ℕ) (a : α) :
    (n : ℝ) * P a < (roundedFloor P n a : ℝ) + 1 :=
  Nat.lt_floor_add_one _

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
private lemma roundedFloor_le (P : α → ℝ) (n : ℕ) (a : α)
    (hP_nn : 0 ≤ P a) (hP_le_one : P a ≤ 1) :
    roundedFloor P n a ≤ n := by
  have h1 : (roundedFloor P n a : ℝ) ≤ (n : ℝ) * P a :=
    roundedFloor_le_real P n a hP_nn
  have h2 : (n : ℝ) * P a ≤ n := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h3 : (roundedFloor P n a : ℝ) ≤ (n : ℝ) := le_trans h1 h2
  exact_mod_cast h3

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- `∑ a, roundedFloor P n a ≤ n` when `∑ P a = 1` and `P ≥ 0`. -/
private lemma sum_roundedFloor_le (P : α → ℝ) (hP : (∑ a, P a) = 1)
    (hP_nn : ∀ a, 0 ≤ P a) (n : ℕ) :
    (∑ a, roundedFloor P n a) ≤ n := by
  have h_real : (∑ a, (roundedFloor P n a : ℝ)) ≤ (n : ℝ) := by
    calc (∑ a, (roundedFloor P n a : ℝ))
        ≤ ∑ a, (n : ℝ) * P a := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact roundedFloor_le_real P n a (hP_nn a)
      _ = (n : ℝ) * ∑ a, P a := by rw [Finset.mul_sum]
      _ = (n : ℝ) := by rw [hP, mul_one]
  exact_mod_cast h_real

/-- ℕ-valued form of the rounded type index (clean to reason about).
`c a := ⌊n · P a⌋` for `a ≠ a₀`, and `c a₀ := n - ∑_{a ≠ a₀} ⌊n · P a⌋`. -/
noncomputable def roundedTypeIndexNat (P : α → ℝ) (n : ℕ) (a : α) : ℕ :=
  let a₀ := absorberLetter α
  if a = a₀ then
    n - ∑ b ∈ Finset.univ.erase a₀, roundedFloor P n b
  else
    min (roundedFloor P n a) n

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
private lemma roundedTypeIndexNat_le (P : α → ℝ) (n : ℕ) (a : α) :
    roundedTypeIndexNat P n a ≤ n := by
  unfold roundedTypeIndexNat
  dsimp only
  split_ifs
  · exact Nat.sub_le _ _
  · exact min_le_right _ _

/-- **Rounded type index** (achievable type sequence).
`c a := ⌊n · P a⌋` for `a ≠ a₀`, and `c a₀ := n - ∑_{a ≠ a₀} ⌊n · P a⌋`
where `a₀ := absorberLetter α`. The single "absorber" letter takes all the
deficit, simplifying the `Fin (n+1)` range proof. -/
noncomputable def roundedTypeIndex (P : α → ℝ) (n : ℕ) :
    TypeCountIndex α n := fun a =>
  ⟨roundedTypeIndexNat P n a, Nat.lt_succ_of_le (roundedTypeIndexNat_le P n a)⟩


omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Sum constraint**: `∑ a, roundedTypeIndex P n a = n`. -/
lemma roundedTypeIndex_sum
    (P : α → ℝ) (hP : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a)
    (n : ℕ) (_hn : 0 < n) :
    (∑ a, (roundedTypeIndex P n a : ℕ)) = n := by
  classical
  set a₀ : α := absorberLetter α with ha₀_def
  set f : α → ℕ := roundedFloor P n with hf_def
  -- For a ≠ a₀: c a = min (f a) n = f a since f a ≤ n.
  have h_non_abs : ∀ a, a ≠ a₀ → (roundedTypeIndex P n a : ℕ) = f a := by
    intro a ha
    show roundedTypeIndexNat P n a = f a
    unfold roundedTypeIndexNat
    dsimp only
    rw [if_neg ha]
    exact min_eq_left (roundedFloor_le P n a (hP_nn a) (by
      have : P a ≤ ∑ b, P b := by
        refine Finset.single_le_sum (f := P) (fun b _ => hP_nn b) (Finset.mem_univ _)
      rw [hP] at this; exact this))
  have h_abs : (roundedTypeIndex P n a₀ : ℕ) = n - ∑ b ∈ Finset.univ.erase a₀, f b := by
    show roundedTypeIndexNat P n a₀ = n - ∑ b ∈ Finset.univ.erase a₀, f b
    unfold roundedTypeIndexNat
    dsimp only
    rw [if_pos rfl]
  -- Sum splits as a₀ + sum over erase a₀.
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a₀)]
  rw [h_abs]
  rw [Finset.sum_congr rfl (fun a ha => h_non_abs a (Finset.ne_of_mem_erase ha))]
  -- ∑_{a ≠ a₀} f a + (n - ∑_{a ≠ a₀} f a) = n
  have h_sum_le : (∑ a ∈ Finset.univ.erase a₀, f a) ≤ n := by
    have h_total : (∑ a, f a) ≤ n := sum_roundedFloor_le P hP hP_nn n
    have h_split : (∑ a ∈ Finset.univ.erase a₀, f a) + f a₀ = ∑ a, f a :=
      Finset.sum_erase_add _ _ (Finset.mem_univ a₀)
    omega
  -- Goal: ∑_{erase} f + (n - ∑_{erase} f) = n. Notation: `(s.sum f)` vs `∑ a ∈ s, f a`.
  show (∑ a ∈ Finset.univ.erase a₀, f a) + (n - ∑ b ∈ Finset.univ.erase a₀, f b) = n
  omega

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Rounding distance bound**: `|(c a : ℝ)/n - P a| ≤ |α|/n` per letter.
The absorber letter takes up to `|α|-1` deficit; non-absorber letters
differ from `n · P a` by `< 1`. Sufficient for Tendsto (sandwich with `→ 0`). -/
lemma roundedTypeIndex_dist_le
    (P : α → ℝ) (hP : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a)
    (n : ℕ) (hn : 0 < n) (a : α) :
    |((roundedTypeIndex P n a : ℕ) : ℝ) / n - P a| ≤ (Fintype.card α : ℝ) / n := by
  classical
  set a₀ : α := absorberLetter α with ha₀_def
  set f : α → ℕ := roundedFloor P n with hf_def
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hP_le_one : ∀ b, P b ≤ 1 := by
    intro b
    have : P b ≤ ∑ c, P c :=
      Finset.single_le_sum (f := P) (fun c _ => hP_nn c) (Finset.mem_univ _)
    rw [hP] at this; exact this
  -- Reformulate: |c a / n - P a| ≤ |α|/n  ↔  |c a - n · P a| ≤ |α|.
  show |((roundedTypeIndexNat P n a : ℝ)) / n - P a| ≤ (Fintype.card α : ℝ) / n
  have h_rw : (roundedTypeIndexNat P n a : ℝ) / (n : ℝ) - P a
      = ((roundedTypeIndexNat P n a : ℝ) - (n : ℝ) * P a) / (n : ℝ) := by
    field_simp
  rw [h_rw, abs_div, abs_of_pos hn_pos,
    div_le_div_iff_of_pos_right hn_pos]
  -- Now goal: |c a - n · P a| ≤ |α|.
  by_cases h : a = a₀
  · -- a₀ case: c a = n - ∑_{b ≠ a₀} f b.
    subst h
    have h_sum_le_n : (∑ b ∈ Finset.univ.erase a₀, f b) ≤ n := by
      have h_total : (∑ b, f b) ≤ n := sum_roundedFloor_le P hP hP_nn n
      have h_split : (∑ b ∈ Finset.univ.erase a₀, f b) + f a₀ = ∑ b, f b :=
        Finset.sum_erase_add _ _ (Finset.mem_univ a₀)
      omega
    have h_val : (roundedTypeIndexNat P n a₀ : ℝ)
        = (n : ℝ) - ∑ b ∈ Finset.univ.erase a₀, (f b : ℝ) := by
      show ((roundedTypeIndexNat P n a₀ : ℕ) : ℝ) = _
      have hRTNat_eq : roundedTypeIndexNat P n a₀
          = n - ∑ b ∈ Finset.univ.erase a₀, f b := by
        unfold roundedTypeIndexNat
        dsimp only
        rw [if_pos rfl]
      rw [hRTNat_eq, Nat.cast_sub h_sum_le_n]
      push_cast
      rfl
    rw [h_val]
    -- ∑_b P b = 1 so n = ∑ n P b. Therefore
    -- n - ∑_{erase} f - n P a₀ = ∑_{b ≠ a₀} (n P b - f b).
    have h_sum_n : (n : ℝ) = ∑ b, (n : ℝ) * P b := by
      rw [← Finset.mul_sum, hP, mul_one]
    have h_split : (n : ℝ) - n * P a₀ = ∑ b ∈ Finset.univ.erase a₀, (n : ℝ) * P b := by
      have h_decomp : ∑ b, (n : ℝ) * P b
          = (n : ℝ) * P a₀ + ∑ b ∈ Finset.univ.erase a₀, (n : ℝ) * P b :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ a₀)).symm
      linarith [h_sum_n, h_decomp]
    have h_diff : ((n : ℝ) - ∑ b ∈ Finset.univ.erase a₀, (f b : ℝ)) - (n : ℝ) * P a₀
        = ∑ b ∈ Finset.univ.erase a₀, ((n : ℝ) * P b - f b) := by
      rw [show ((n : ℝ) - ∑ b ∈ Finset.univ.erase a₀, (f b : ℝ)) - (n : ℝ) * P a₀
            = ((n : ℝ) - (n : ℝ) * P a₀) - ∑ b ∈ Finset.univ.erase a₀, (f b : ℝ) from by ring]
      rw [h_split, ← Finset.sum_sub_distrib]
    rw [h_diff]
    -- Each summand: 0 ≤ n · P b - f b < 1.
    have h_each : ∀ b ∈ (Finset.univ.erase a₀ : Finset α),
        0 ≤ (n : ℝ) * P b - f b ∧ (n : ℝ) * P b - f b < 1 := by
      intro b _
      refine ⟨?_, ?_⟩
      · linarith [roundedFloor_le_real P n b (hP_nn b)]
      · linarith [roundedFloor_lt_succ P n b]
    -- |sum| ≤ |α-1| ≤ |α|.
    have h_card : (Finset.univ.erase a₀).card = Fintype.card α - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl
    have h_sum_nn : 0 ≤ ∑ b ∈ Finset.univ.erase a₀, ((n : ℝ) * P b - f b) :=
      Finset.sum_nonneg fun b hb => (h_each b hb).1
    have h_sum_lt : (∑ b ∈ Finset.univ.erase a₀, ((n : ℝ) * P b - f b))
        ≤ (Finset.univ.erase a₀).card := by
      have h := Finset.sum_le_sum (s := (Finset.univ.erase a₀ : Finset α))
        (f := fun b => (n : ℝ) * P b - f b) (g := fun _ => (1 : ℝ))
        (fun b hb => (h_each b hb).2.le)
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    rw [abs_of_nonneg h_sum_nn]
    refine h_sum_lt.trans ?_
    rw [h_card]
    exact_mod_cast Nat.sub_le _ _
  · -- a ≠ a₀ case: c a = min (f a) n = f a.
    have h_val : (roundedTypeIndexNat P n a : ℝ) = (f a : ℝ) := by
      show (roundedTypeIndexNat P n a : ℝ) = (f a : ℝ)
      unfold roundedTypeIndexNat
      dsimp only
      rw [if_neg h]
      have : min (f a) n = f a := min_eq_left (roundedFloor_le P n a (hP_nn a) (hP_le_one a))
      rw [this]
    rw [h_val]
    have h1 : (f a : ℝ) ≤ (n : ℝ) * P a := roundedFloor_le_real P n a (hP_nn a)
    have h2 : (n : ℝ) * P a < (f a : ℝ) + 1 := roundedFloor_lt_succ P n a
    have h_lb : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
    have h_card_pos : (1 : ℝ) ≤ Fintype.card α := by
      have : (1 : ℕ) ≤ Fintype.card α := Fintype.card_pos
      exact_mod_cast this
    rw [abs_le]
    refine ⟨?_, ?_⟩ <;> linarith

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Pointwise Tendsto**: `(roundedTypeIndex P n a : ℝ) / n → P a`. -/
lemma roundedTypeIndex_tendsto
    (P : α → ℝ) (hP : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a)
    (a : α) :
    Tendsto (fun n : ℕ => ((roundedTypeIndex P n a : ℕ) : ℝ) / n) atTop (𝓝 (P a)) := by
  -- Sandwich: |c_n / n - P a| ≤ |α| / n → 0.
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  -- Pick N so |α|/N < ε.
  have h_card_pos : (0 : ℝ) < Fintype.card α := by
    have : (0 : ℕ) < Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (Fintype.card α : ℝ) / N < ε ∧ 0 < N := by
    -- |α|/N < ε ↔ N > |α|/ε.
    obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card α : ℝ) / ε)
    refine ⟨N + 1, ?_, by omega⟩
    have hN_pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    rw [div_lt_iff₀ hN_pos]
    have h_N_real : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; rfl
    rw [h_N_real]
    rw [div_lt_iff₀ hε] at hN
    linarith
  refine ⟨N, fun n hn => ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le hN.2 hn
  have h_dist := roundedTypeIndex_dist_le P hP hP_nn n hn_pos a
  -- d(x,y) = |x - y|, so the goal is `|... - P a| < ε`.
  rw [Real.dist_eq]
  have h_n_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_card_div_decr : (Fintype.card α : ℝ) / n ≤ (Fintype.card α : ℝ) / N := by
    refine div_le_div_of_nonneg_left h_card_pos.le ?_ ?_
    · exact_mod_cast hN.2
    · exact_mod_cast hn
  calc |((roundedTypeIndex P n a : ℕ) : ℝ) / n - P a|
      ≤ (Fintype.card α : ℝ) / n := h_dist
    _ ≤ (Fintype.card α : ℝ) / N := h_card_div_decr
    _ < ε := hN.1

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Vector Tendsto** (`α → ℝ` Pi-topology). -/
lemma roundedTypeIndex_tendsto_vec
    (P : α → ℝ) (hP : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a) :
    Tendsto (fun n : ℕ => (fun a => ((roundedTypeIndex P n a : ℕ) : ℝ) / n))
      atTop (𝓝 P) := by
  rw [tendsto_pi_nhds]
  intro a
  exact roundedTypeIndex_tendsto P hP hP_nn a

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **General witness lemma**: for any count `c : α → ℕ` with `∑ a, c a = n`,
the type class `typeClassByCount c` is nonempty.
Construction: define `g : Fin n → α` by packing `Σ a, Fin (c a)` into `Fin n`
via cardinality equivalence, then projecting via `Sigma.fst`. -/
lemma typeClassByCount_nonempty_of_sum
    {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (typeClassByCount (α := α) (n := n) c).Nonempty := by
  classical
  -- We use an equivalence `Σ a : α, Fin (c a) ≃ Fin n`.
  have h_card_sigma : Fintype.card (Σ a : α, Fin (c a)) = n := by
    rw [Fintype.card_sigma]
    simp [hc_sum]
  have h_card_eq : Fintype.card (Σ a : α, Fin (c a)) = Fintype.card (Fin n) := by
    rw [h_card_sigma, Fintype.card_fin]
  -- noncomputable equivalence
  let e : (Σ a : α, Fin (c a)) ≃ Fin n := Fintype.equivOfCardEq h_card_eq
  -- g j := first component of e⁻¹ j.
  let g : Fin n → α := fun j => (e.symm j).fst
  refine ⟨g, ?_⟩
  intro a
  show (Finset.univ.filter (fun i : Fin n => g i = a)).card = c a
  -- count via image of an embedding from Fin (c a):  k ↦ e ⟨a, k⟩.
  let φ : Fin (c a) ↪ Fin n :=
    ⟨fun k => e ⟨a, k⟩, fun k₁ k₂ h => by
      have := e.injective h
      simpa using this⟩
  have h_filter_eq :
      Finset.univ.filter (fun i : Fin n => g i = a)
        = (Finset.univ : Finset (Fin (c a))).map φ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hj
      -- (e.symm j).fst = a, so we can extract (e.symm j).snd via heq.
      have hfst : (e.symm j).fst = a := hj
      refine ⟨Fin.cast (by rw [hfst]) (e.symm j).snd, ?_⟩
      show e ⟨a, Fin.cast (by rw [hfst]) (e.symm j).snd⟩ = j
      have h_pair_eq : (⟨a, Fin.cast (by rw [hfst]) (e.symm j).snd⟩ : Σ b : α, Fin (c b))
          = e.symm j := by
        apply Sigma.ext hfst.symm
        -- snd HEq.
        have : HEq (Fin.cast (by rw [hfst]) (e.symm j).snd) (e.symm j).snd :=
          (Fin.heq_ext_iff (by rw [hfst])).mpr rfl
        exact this
      rw [h_pair_eq, Equiv.apply_symm_apply]
    · rintro ⟨k, rfl⟩
      show (e.symm (e ⟨a, k⟩)).fst = a
      rw [Equiv.symm_apply_apply]
  rw [h_filter_eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]


omit [MeasurableSingletonClass α] in
/-- **KL convergence via `klDivSumForm_ofVec` continuity**:
`klDivIndex (roundedTypeIndex P n) n Q → klDivSumForm_ofVec P (Q.real ∘ singleton)`. -/
theorem klDivIndex_rounded_tendsto
    (Q : Measure α) (hQpos : ∀ a, 0 < Q.real {a})
    (P : α → ℝ) (hP : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a) :
    Tendsto (fun n : ℕ =>
        klDivIndex (fun a => (roundedTypeIndex P n a : ℕ)) n Q)
      atTop (𝓝 (klDivSumForm_ofVec P (fun a => Q.real {a}))) := by
  -- rewrite klDivIndex via the `klDivSumForm_ofVec` connection
  have h_rewrite : ∀ n,
      klDivIndex (fun a => (roundedTypeIndex P n a : ℕ)) n Q
        = klDivSumForm_ofVec
            (fun a => ((roundedTypeIndex P n a : ℕ) : ℝ) / n)
            (fun a => Q.real {a}) := fun n =>
    klDivIndex_eq_ofVec (fun a => (roundedTypeIndex P n a : ℕ)) n Q
  simp_rw [h_rewrite]
  -- Now: continuity of klDivSumForm_ofVec composed with tendsto of c_n/n.
  have h_cont : Continuous
      (fun p : α → ℝ => klDivSumForm_ofVec p (fun a => Q.real {a})) :=
    klDivSumForm_ofVec_continuous (fun a => Q.real {a}) hQpos
  have h_tendsto_vec :
      Tendsto (fun n : ℕ => (fun a => ((roundedTypeIndex P n a : ℕ) : ℝ) / n))
        atTop (𝓝 P) :=
    roundedTypeIndex_tendsto_vec P hP hP_nn
  exact h_cont.tendsto P |>.comp h_tendsto_vec

end InformationTheory.Shannon
