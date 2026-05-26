import Common2026.Meta.EntryPoint
import Common2026.Shannon.SanovLDP
import Common2026.Shannon.KLDivContinuous
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Sanov LDP equality form (B-1'')

Cover-Thomas Theorem 11.4.1 LDP equality, **簡略 open set 形**.

```
(1/n) log Q^n(⋃ c ∈ E n, T_c)  →  -klDivSumForm_ofVec P Q  (n → ∞)
```

入力: ユーザが渡す `P ∈ Δ`, `D = klDivSumForm_ofVec P (Q.real ∘ singleton)`,
`E n` が `roundedTypeIndex P n` を eventually 含む + `∀ c ∈ E n, D ≤ klDivIndex c n Q`。

構成 (4 phase):
* **Phase B** — achievable type sequence `roundedTypeIndex P n` の構成 + Tendsto。
* **Phase C** — multinomial Stirling-free `Q^n(T_c) ≥ (n+1)^{-|α|} · exp(-n · klDivIndex)`.
* **Phase D** — liminf 形 lower bound `liminf (1/n) log Q^n(⋃) ≥ -D`.
* **Phase E** — sandwich `B-1' upper + Phase D lower` → Tendsto.

詳細: `docs/shannon/sanov-ldp-equality-plan.md` Phase B-E.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Phase B — Rounded type sequence -/

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
/-- **KL convergence via Phase A continuity**:
`klDivIndex (roundedTypeIndex P n) n Q → klDivSumForm_ofVec P (Q.real ∘ singleton)`. -/
theorem klDivIndex_rounded_tendsto
    (Q : Measure α) (hQpos : ∀ a, 0 < Q.real {a})
    (P : α → ℝ) (hP : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a) :
    Tendsto (fun n : ℕ =>
        klDivIndex (fun a => (roundedTypeIndex P n a : ℕ)) n Q)
      atTop (𝓝 (klDivSumForm_ofVec P (fun a => Q.real {a}))) := by
  -- rewrite klDivIndex via Phase A connection
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

/-! ### Phase C — Multinomial Stirling-free lower bound -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **Per-letter factorial-power inequality**:
`c! · c^k ≤ k! · c^c` for all c, k ∈ ℕ. -/
private lemma factorial_pow_swap_le (c k : ℕ) :
    Nat.factorial c * c ^ k ≤ Nat.factorial k * c ^ c := by
  rcases Nat.lt_or_ge k c with hk | hk
  · -- k < c, so k ≤ c.
    have hkc : k ≤ c := hk.le
    have h_desc : c.descFactorial (c - k) ≤ c ^ (c - k) :=
      Nat.descFactorial_le_pow c (c - k)
    have h_fact_eq : Nat.factorial c = Nat.factorial k * c.descFactorial (c - k) := by
      have h := Nat.factorial_mul_descFactorial (n := c) (k := c - k) (Nat.sub_le _ _)
      rw [Nat.sub_sub_self hkc] at h
      exact h.symm
    calc Nat.factorial c * c ^ k
        = Nat.factorial k * c.descFactorial (c - k) * c ^ k := by rw [h_fact_eq]
      _ ≤ Nat.factorial k * c ^ (c - k) * c ^ k :=
            Nat.mul_le_mul_right (c ^ k) (Nat.mul_le_mul_left _ h_desc)
      _ = Nat.factorial k * c ^ c := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkc]
  · -- c ≤ k: use Nat.factorial_mul_pow_sub_le_factorial.
    have h := Nat.factorial_mul_pow_sub_le_factorial hk
    have h_pow_split : Nat.factorial c * c ^ k
        = (Nat.factorial c * c ^ (k - c)) * c ^ c := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    rw [h_pow_split]
    exact Nat.mul_le_mul_right (c ^ c) h

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **Product over α of per-letter factorial-power inequality**.
`(∏ Nat.factorial (c a)) · (∏ (c a)^{k a}) ≤ (∏ (k a)!) · (∏ (c a)^{c a})`. -/
private lemma prod_factorial_pow_swap_le (c k : α → ℕ) :
    (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a)
      ≤ (∏ a, Nat.factorial (k a)) * (∏ a, c a ^ c a) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun a _ => factorial_pow_swap_le (c a) (k a))

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Max-likelihood for the multinomial coefficient**: for c, k both summing to n,
`multinomial univ k · ∏ c(a)^{k a} ≤ multinomial univ c · ∏ c(a)^{c a}`.

(In ratio form: `multinomial univ k / multinomial univ c ≤ ∏ c(a)^{c a - k a}` after div.) -/
private lemma multinomial_pow_le {n : ℕ} (c k : α → ℕ)
    (hc_sum : (∑ a, c a) = n) (hk_sum : (∑ a, k a) = n) :
    Nat.multinomial Finset.univ k * (∏ a, c a ^ k a)
      ≤ Nat.multinomial Finset.univ c * (∏ a, c a ^ c a) := by
  -- (∏ c!)·multinomial c = n! = (∏ k!)·multinomial k.
  have h_c : (∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c
        = Nat.factorial n := by
    rw [Nat.multinomial_spec, hc_sum]
  have h_k : (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ k
        = Nat.factorial n := by
    rw [Nat.multinomial_spec, hk_sum]
  have h_swap := prod_factorial_pow_swap_le (α := α) c k
  have h_pos : 0 < Nat.factorial n := Nat.factorial_pos _
  -- Multiply h_swap by `multinomial univ c`:
  have step :
      (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a) * Nat.multinomial Finset.univ c
        ≤ (∏ a, Nat.factorial (k a)) * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ c :=
    Nat.mul_le_mul_right _ h_swap
  have hL : (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a)
        * Nat.multinomial Finset.univ c
      = Nat.factorial n * (∏ a, c a ^ k a) := by
    rw [show (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a)
              * Nat.multinomial Finset.univ c
          = ((∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c)
              * (∏ a, c a ^ k a) by ring,
        h_c]
  have hR : (∏ a, Nat.factorial (k a)) * (∏ a, c a ^ c a)
        * Nat.multinomial Finset.univ c
      = (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
        * (∏ a, c a ^ c a) := by ring
  rw [hL, hR] at step
  -- step : n! · (∏ c^k) ≤ (∏ k!) · multinomial univ c · (∏ c^c)
  -- Multiply step by multinomial univ k:
  have step2 :
      Nat.factorial n * (∏ a, c a ^ k a) * Nat.multinomial Finset.univ k
        ≤ (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
            * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ k :=
    Nat.mul_le_mul_right _ step
  have hL2 : Nat.factorial n * (∏ a, c a ^ k a) * Nat.multinomial Finset.univ k
      = Nat.factorial n * (Nat.multinomial Finset.univ k * (∏ a, c a ^ k a)) := by ring
  have hR2 : (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
        * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ k
      = Nat.factorial n * (Nat.multinomial Finset.univ c * (∏ a, c a ^ c a)) := by
    rw [show (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
              * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ k
          = ((∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ k)
              * (Nat.multinomial Finset.univ c * (∏ a, c a ^ c a)) by ring,
        h_k]
  rw [hL2, hR2] at step2
  exact Nat.le_of_mul_le_mul_left step2 h_pos

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **`multinomial univ c ≤ |T_c|`** (the bridge to the multinomial coefficient).

We use a **surjection** `Φ : Fin n → α → T_c` defined via `x₀ ∈ T_c`:
`Φ σ := x₀ ∘ σ`. By surjectivity of `Φ` (any `x ∈ T_c` is hit because both x, x₀ have
type c so we can find a permutation taking one to the other), `n! = |Perm Fin n|`
counts each `x ∈ T_c` with multiplicity = fiber size ≤ `∏ a, Nat.factorial (c a)` (the permutations
preserving fiber structure on x₀). So `n! ≤ |T_c| · ∏ c(a)!`, giving the goal via
`Nat.multinomial_spec`.

Strategy: use `Fintype.card_le_of_surjective` with a chosen `Ψ : (T_c × Π a, Perm (Fin (c a))) → Perm (Fin n)`
that is injective. Then `n! = card (Perm Fin n) ≥ |T_c| · ∏ c(a)!`. -/
private lemma multinomial_le_typeClass_card {n : ℕ} (c : α → ℕ)
    (hc_sum : (∑ a, c a) = n) :
    Nat.multinomial Finset.univ c
      ≤ (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card := by
  classical
  -- Strategy: construct an injection Ψ : Perm (Fin n) → T_c × (Π a, Perm (Fin (c a))).
  -- Then n! = |Perm (Fin n)| ≤ |T_c| · ∏ Nat.factorial (c a). Combined with multinomial_spec
  -- (multinomial · ∏ Nat.factorial (c a) = n!), we get multinomial ≤ |T_c|.
  obtain ⟨x₀, hx₀⟩ := typeClassByCount_nonempty_of_sum c hc_sum
  -- Generic reference equiv  Fin (typeCount x a) ≃ {i // x i = a}.
  have hcard_typeCount : ∀ (x : Fin n → α) (a : α),
      Fintype.card (Fin (typeCount x a)) = Fintype.card {i : Fin n // x i = a} := by
    intro x a
    rw [Fintype.card_fin, Fintype.card_subtype]
    rfl
  let ePos : (x : Fin n → α) → (a : α) → Fin (typeCount x a) ≃ {i : Fin n // x i = a} :=
    fun x a => Fintype.equivOfCardEq (hcard_typeCount x a)
  -- For x ∈ T_c, derive  Fin (c a) ≃ {i // x i = a}.
  let eFibOf : (x : Fin n → α) → (∀ a, typeCount x a = c a) →
      (a : α) → Fin (c a) ≃ {i : Fin n // x i = a} :=
    fun x h a => (Equiv.cast (by rw [h a])).trans (ePos x a)
  let eFib₀ : (a : α) → Fin (c a) ≃ {i : Fin n // x₀ i = a} := eFibOf x₀ hx₀
  -- Given σ, derive x σ ∈ T_c.
  let xOf : Equiv.Perm (Fin n) → (Fin n → α) := fun σ i => x₀ (σ.symm i)
  have h_xOf_mem : ∀ σ : Equiv.Perm (Fin n), xOf σ ∈ typeClassByCount c := by
    intro σ a
    show (Finset.univ.filter (fun i => xOf σ i = a)).card = c a
    have h_eq : Finset.univ.filter (fun i : Fin n => xOf σ i = a)
        = (Finset.univ.filter (fun j : Fin n => x₀ j = a)).map σ.toEmbedding := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.coe_toEmbedding]
      refine ⟨fun h_xi => ⟨σ.symm i, h_xi, Equiv.apply_symm_apply σ i⟩, ?_⟩
      rintro ⟨j, hj, rfl⟩
      show x₀ (σ.symm (σ j)) = a
      rw [Equiv.symm_apply_apply]; exact hj
    rw [h_eq, Finset.card_map]; exact hx₀ a
  let xMem : Equiv.Perm (Fin n) → (typeClassByCount (α := α) (n := n) c) :=
    fun σ => ⟨xOf σ, h_xOf_mem σ⟩
  -- Restriction σ : {j // x₀ j = a} → {i // xOf σ i = a}.
  have h_restrict_mem : ∀ (σ : Equiv.Perm (Fin n)) (a : α) (j : Fin n) (hj : x₀ j = a),
      xOf σ (σ j) = a := fun σ a j hj => by
    show x₀ (σ.symm (σ j)) = a
    rw [Equiv.symm_apply_apply]; exact hj
  -- τOf σ a : Fin (c a) ≃ Fin (c a).
  let τOf : (σ : Equiv.Perm (Fin n)) → (∀ a, Equiv.Perm (Fin (c a))) := fun σ a =>
    let e1 : Fin (c a) ≃ {j : Fin n // x₀ j = a} := eFib₀ a
    let e2 : {j : Fin n // x₀ j = a} ≃ {i : Fin n // xOf σ i = a} :=
      { toFun := fun j => ⟨σ j.val, h_restrict_mem σ a j.val j.property⟩,
        invFun := fun i => ⟨σ.symm i.val, by
          show x₀ (σ.symm i.val) = a; exact i.property⟩,
        left_inv := fun j => Subtype.ext (Equiv.symm_apply_apply σ j.val),
        right_inv := fun i => Subtype.ext (Equiv.apply_symm_apply σ i.val) }
    let e3 : {i : Fin n // xOf σ i = a} ≃ Fin (c a) := (eFibOf (xOf σ) (h_xOf_mem σ) a).symm
    (e1.trans e2).trans e3
  let Ψ : Equiv.Perm (Fin n) →
      (typeClassByCount (α := α) (n := n) c) × (∀ a, Equiv.Perm (Fin (c a))) :=
    fun σ => (xMem σ, τOf σ)
  -- Recovery formula: σ j = (eFibOf (xOf σ) ... (x₀ j) (τOf σ (x₀ j) ((eFib₀ (x₀ j)).symm ⟨j, rfl⟩))).val
  have h_recovery : ∀ (σ : Equiv.Perm (Fin n)) (j : Fin n),
      σ j = ((eFibOf (xOf σ) (h_xOf_mem σ) (x₀ j))
              (τOf σ (x₀ j) ((eFib₀ (x₀ j)).symm ⟨j, rfl⟩))).val := by
    intro σ j
    set a := x₀ j
    set k : Fin (c a) := (eFib₀ a).symm ⟨j, (rfl : x₀ j = a)⟩
    -- Unfold τOf σ a applied to k.
    show σ j = ((eFibOf (xOf σ) (h_xOf_mem σ) a) (τOf σ a k)).val
    have hk_eq : (eFib₀ a) k = ⟨j, rfl⟩ := Equiv.apply_symm_apply _ _
    have hτ_unfold : τOf σ a k =
        (eFibOf (xOf σ) (h_xOf_mem σ) a).symm
          ⟨σ j, h_restrict_mem σ a j rfl⟩ := by
      show ((eFib₀ a).trans _).trans _ k = _
      simp only [Equiv.trans_apply]
      rw [hk_eq]
      rfl
    rw [hτ_unfold, Equiv.apply_symm_apply]
  -- Ψ injective.
  have hΨ_inj : Function.Injective Ψ := by
    intro σ σ' hσ
    have hxMem_eq : xMem σ = xMem σ' := (Prod.mk.injEq ..).mp hσ |>.1
    have hx_eq : xOf σ = xOf σ' := congrArg Subtype.val hxMem_eq
    have hτ_eq : τOf σ = τOf σ' := (Prod.mk.injEq ..).mp hσ |>.2
    refine Equiv.ext (fun j => ?_)
    rw [h_recovery σ j, h_recovery σ' j]
    -- Goal: ((eFibOf (xOf σ) (h_xOf_mem σ) (x₀ j)) (τOf σ ...)).val
    --     = ((eFibOf (xOf σ') (h_xOf_mem σ') (x₀ j)) (τOf σ' ...)).val.
    -- Use hxMem_eq and hτ_eq to align both sides as members of the same Subtype.
    -- The most robust way: show the result via `Subtype.ext` after using the membership-coercion.
    -- The Subtype-valued LHS RHS, after taking .val, only require equality at the value level.
    -- We use the fact that `eFibOf x hx a m` as a Subtype's `.val` is independent of `hx` (only x matters), and depends on x via Fintype.equivOfCardEq.
    -- The cleanest path: substitute xOf σ with xOf σ' (then membership proofs become equal by Subsingleton).
    set j₀ := (⟨j, (rfl : x₀ j = x₀ j)⟩ : {i : Fin n // x₀ i = x₀ j})
    set k := (eFib₀ (x₀ j)).symm j₀
    -- After unfolding the τ-applications, replace τOf σ with τOf σ' via hτ_eq.
    have h_tau_at : τOf σ (x₀ j) k = τOf σ' (x₀ j) k := by rw [hτ_eq]
    rw [h_tau_at]
    -- Now both sides: (eFibOf (xOf σ) (h_xOf_mem σ) a (τOf σ' a k)).val vs (eFibOf (xOf σ') ...).val.
    -- The pair `(xOf σ, h_xOf_mem σ)` equals `(xOf σ', h_xOf_mem σ')` via `hxMem_eq`.
    -- Use Sigma to consolidate the dependency.
    have h_pair_eq : (⟨xOf σ, h_xOf_mem σ⟩ : (typeClassByCount c)) = ⟨xOf σ', h_xOf_mem σ'⟩ :=
      hxMem_eq
    -- Apply this via `congr` of the auxiliary function.
    let g : (typeClassByCount (α := α) (n := n) c) → Fin n := fun y =>
      ((eFibOf y.val y.property (x₀ j)) (τOf σ' (x₀ j) k)).val
    have hg_eq : g ⟨xOf σ, h_xOf_mem σ⟩ = g ⟨xOf σ', h_xOf_mem σ'⟩ := by
      congr 1
    exact hg_eq
  -- Cardinality calculation.
  have h_card_le := Fintype.card_le_of_injective Ψ hΨ_inj
  have hL : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hR : Fintype.card ((typeClassByCount (α := α) (n := n) c)
        × (∀ a, Equiv.Perm (Fin (c a))))
      = (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card
          * ∏ a, Nat.factorial (c a) := by
    rw [Fintype.card_prod, Fintype.card_pi]
    congr 1
    · exact (Set.Finite.card_toFinset _).symm
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [Fintype.card_perm, Fintype.card_fin]
  rw [hL, hR] at h_card_le
  -- h_card_le : n! ≤ |T_c| · ∏ Nat.factorial (c a).
  have h_spec : (∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c = Nat.factorial n := by
    rw [Nat.multinomial_spec, hc_sum]
  have h_prod_pos : 0 < ∏ a, Nat.factorial (c a) :=
    Finset.prod_pos fun _ _ => Nat.factorial_pos _
  -- multinomial · ∏ Nat.factorial (c a) = n! ≤ |T_c| · ∏ Nat.factorial (c a).
  -- So multinomial ≤ |T_c|.
  have h_mul_le : (∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c
      ≤ (∏ a, Nat.factorial (c a)) *
        (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card := by
    rw [h_spec]
    -- |T_c| · ∏ Nat.factorial (c a) ≥ n! = ∏ Nat.factorial (c a) · multinomial.
    -- h_card_le : n! ≤ |T_c| · ∏ Nat.factorial (c a).
    calc Nat.factorial n ≤ (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card * ∏ a, Nat.factorial (c a) :=
          h_card_le
      _ = (∏ a, Nat.factorial (c a)) * (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card := by ring
  exact Nat.le_of_mul_le_mul_left h_mul_le h_prod_pos

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **ℝ form of `multinomial_pow_le`**. -/
private lemma multinomial_pow_le_real {n : ℕ} (c k : α → ℕ)
    (hc_sum : (∑ a, c a) = n) (hk_sum : (∑ a, k a) = n) :
    (Nat.multinomial Finset.univ k : ℝ) * (∏ a, (c a : ℝ) ^ k a)
      ≤ (Nat.multinomial Finset.univ c : ℝ) * (∏ a, (c a : ℝ) ^ c a) := by
  have h := multinomial_pow_le (α := α) c k hc_sum hk_sum
  have :
      ((Nat.multinomial Finset.univ k * (∏ a, c a ^ k a) : ℕ) : ℝ)
        ≤ ((Nat.multinomial Finset.univ c * (∏ a, c a ^ c a) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at this
  exact this

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Card of `piAntidiag univ n` is bounded by `(n+1)^{|α|}`**. -/
private lemma piAntidiag_card_le (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset α) n).card
      ≤ (n + 1) ^ Fintype.card α := by
  classical
  -- Build embedding piAntidiag univ n ↪ (α → Fin (n+1)).
  have h_bound : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
      ∀ a, k a ≤ n := by
    intros k hk_mem a
    have hk_sum := (Finset.mem_piAntidiag.mp hk_mem).1
    have hka : k a ≤ ∑ a', k a' := Finset.single_le_sum (f := k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    rw [hk_sum] at hka
    exact hka
  let φ : (α → ℕ) → (α → Fin (n+1)) :=
    fun k a => ⟨min (k a) n, by
      have hmin : min (k a) n ≤ n := Nat.min_le_right _ _
      omega⟩
  have h_inj_on : Set.InjOn φ (Finset.piAntidiag (Finset.univ : Finset α) n) := by
    intros k₁ hk₁ k₂ hk₂ heq
    funext a
    have heqa := congrFun heq a
    have h_min1 : k₁ a = min (k₁ a) n := by
      have := h_bound k₁ hk₁ a; omega
    have h_min2 : k₂ a = min (k₂ a) n := by
      have := h_bound k₂ hk₂ a; omega
    have : min (k₁ a) n = min (k₂ a) n := by
      have := Fin.mk.inj_iff.mp heqa
      exact this
    omega
  have h_card_pow : Fintype.card (α → Fin (n+1)) = (n+1) ^ Fintype.card α := by
    have h := @Fintype.card_fun α (Fin (n+1)) _ _ _
    rw [Fintype.card_fin] at h
    exact h
  calc (Finset.piAntidiag (Finset.univ : Finset α) n).card
      = ((Finset.piAntidiag (Finset.univ : Finset α) n).image φ).card :=
        (Finset.card_image_of_injOn h_inj_on).symm
    _ ≤ (Finset.univ : Finset (α → Fin (n+1))).card := Finset.card_le_card (by
        intros _ _; exact Finset.mem_univ _)
    _ = Fintype.card (α → Fin (n+1)) := by rw [Finset.card_univ]
    _ = (n+1) ^ Fintype.card α := h_card_pow

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Multinomial Stirling-free lower bound** (Cover-Thomas 11.1.3):
`(n+1)^{-|α|} · n^n / ∏ (c a)^(c a) ≤ |T_c|`.

戦略: `multinomial univ c · ∏ (c/n)^{c a} ≥ (n+1)^{-|α|}` を multinomial theorem
+ max-likelihood (per-letter factorial-power 不等式) で取り、最後に
`multinomial univ c ≤ |T_c|` を合わせる。 -/
theorem typeClassByCount_card_ge
    {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ *
        ((n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a)))
      ≤ ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) := by
  classical
  -- Goal: (n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ |T_c|.
  -- Chain: multinomial univ c ≤ |T_c| ; (n+1)^{-|α|} · n^n / ∏ c^c ≤ multinomial univ c.
  have h_main : ((Nat.multinomial Finset.univ c : ℝ))
        ≤ ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) := by
    have h := multinomial_le_typeClass_card (α := α) c hc_sum
    exact_mod_cast h
  refine le_trans ?_ h_main
  -- Now: (n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ multinomial univ c.
  -- This is equivalent to: n^n ≤ multinomial univ c · ∏ c(a)^{c(a)} · (n+1)^{|α|}.
  -- Equivalent (dividing by n^n on both sides): 1 ≤ (n+1)^{|α|} · multinomial univ c · ∏ (c/n)^c.
  -- This follows from 1 = ∑_k multinomial univ k · ∏ (c/n)^k ≤ (n+1)^{|α|} · max term.
  -- Edge case: n = 0. Then c = 0 everywhere, ∏ c(a)^{c(a)} = 1, n^n = 0^0 = 1.
  -- multinomial univ 0 = 1, LHS = 1, RHS = 1. OK.
  -- General path.
  by_cases hn : n = 0
  · -- n = 0: c a = 0 for all a, multinomial univ c = 1.
    subst hn
    have hc_zero : ∀ a, c a = 0 := fun a => by
      have : c a ≤ ∑ a', c a' := Finset.single_le_sum (f := c)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      omega
    have h_prod_one : ∏ a : α, ((c a : ℝ) ^ (c a)) = 1 := by
      refine Finset.prod_eq_one fun a _ => ?_
      rw [hc_zero a]; simp
    -- multinomial univ c = 1, so the goal `... ≤ multinomial univ c` is `1 ≤ 1`.
    have h_multinomial_one : Nat.multinomial Finset.univ c = 1 := by
      unfold Nat.multinomial
      have h_facts : ∀ a, Nat.factorial (c a) = 1 := fun a => by
        rw [hc_zero a]; rfl
      rw [Finset.prod_congr rfl (fun a _ => h_facts a), Finset.prod_const_one]
      rw [hc_sum]
      decide
    rw [h_prod_one]
    have h_mc : (Nat.multinomial Finset.univ c : ℝ) = 1 := by
      exact_mod_cast h_multinomial_one
    rw [h_mc]
    simp
  · -- n ≥ 1.
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
    have hn_real_succ_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- Step 1: ∑_a (c a / n) = 1 (in ℝ).
    have h_sum_one : (∑ a, (c a : ℝ) / n) = 1 := by
      rw [← Finset.sum_div]
      have h_cast : (∑ a, (c a : ℝ)) = (n : ℝ) := by exact_mod_cast hc_sum
      rw [h_cast]; field_simp
    -- Step 2: (∑_a (c a / n))^n = 1.
    have h_pow_one : (∑ a, (c a : ℝ) / n) ^ n = 1 := by rw [h_sum_one]; simp
    -- Step 3: Apply multinomial theorem.
    have h_mn := Finset.sum_pow_eq_sum_piAntidiag (R := ℝ)
      (Finset.univ : Finset α) (fun a => (c a : ℝ) / n) n
    -- h_mn: (∑ a, (c a)/n)^n = ∑ k ∈ piAntidiag univ n, multinomial univ k · ∏ (c/n)^{k a}
    rw [h_pow_one] at h_mn
    -- h_mn : 1 = ∑ k ∈ piAntidiag univ n, multinomial univ k * ∏ (c/n)^{k a}
    -- Step 4: c ∈ piAntidiag univ n.
    have hc_mem : c ∈ Finset.piAntidiag (Finset.univ : Finset α) n := by
      rw [Finset.mem_piAntidiag]
      refine ⟨hc_sum, fun a _ => Finset.mem_univ a⟩
    -- Step 5: each term ≤ multinomial univ c · ∏ (c/n)^{c a} (max-likelihood).
    have h_term_max : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
        (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a)
          ≤ (Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a) := by
      intros k hk_mem
      have hk_sum := (Finset.mem_piAntidiag.mp hk_mem).1
      -- Use multinomial_pow_le_real but with `(c a / n)` factor.
      -- multinomial k · ∏ (c/n)^k = multinomial k · ∏ (c)^k / n^n.
      -- multinomial c · ∏ (c/n)^c = multinomial c · ∏ (c)^c / n^n.
      have h_split_k : ∏ a, ((c a : ℝ) / n) ^ (k a)
          = (∏ a, (c a : ℝ) ^ (k a)) / (n : ℝ) ^ n := by
        rw [show ∏ a, ((c a : ℝ) / n) ^ (k a)
                = ∏ a, ((c a : ℝ) ^ (k a) / (n : ℝ) ^ (k a)) from
            Finset.prod_congr rfl (fun a _ => div_pow _ _ _)]
        rw [Finset.prod_div_distrib]
        congr 1
        rw [Finset.prod_pow_eq_pow_sum, hk_sum]
      have h_split_c : ∏ a, ((c a : ℝ) / n) ^ (c a)
          = (∏ a, (c a : ℝ) ^ (c a)) / (n : ℝ) ^ n := by
        rw [show ∏ a, ((c a : ℝ) / n) ^ (c a)
                = ∏ a, ((c a : ℝ) ^ (c a) / (n : ℝ) ^ (c a)) from
            Finset.prod_congr rfl (fun a _ => div_pow _ _ _)]
        rw [Finset.prod_div_distrib]
        congr 1
        rw [Finset.prod_pow_eq_pow_sum, hc_sum]
      rw [h_split_k, h_split_c]
      rw [show (Nat.multinomial Finset.univ k : ℝ)
              * ((∏ a, (c a : ℝ) ^ (k a)) / (n : ℝ) ^ n)
            = ((Nat.multinomial Finset.univ k : ℝ) * (∏ a, (c a : ℝ) ^ (k a)))
                / (n : ℝ) ^ n by ring]
      rw [show (Nat.multinomial Finset.univ c : ℝ)
              * ((∏ a, (c a : ℝ) ^ (c a)) / (n : ℝ) ^ n)
            = ((Nat.multinomial Finset.univ c : ℝ) * (∏ a, (c a : ℝ) ^ (c a)))
                / (n : ℝ) ^ n by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact multinomial_pow_le_real c k hc_sum hk_sum
    -- Step 6: all terms ≥ 0.
    have h_term_nn : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
        0 ≤ (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a) := by
      intros k _
      refine mul_nonneg (by positivity) (Finset.prod_nonneg fun a _ => by positivity)
    -- Step 7: sum ≤ card · max.
    have h_card_bound :
        (1 : ℝ) ≤ ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
          * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) := by
      rw [h_mn]
      calc (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
              (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a))
          ≤ ∑ _k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
              ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) :=
            Finset.sum_le_sum h_term_max
        _ = ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
              * ((Nat.multinomial Finset.univ c : ℝ)
                * ∏ a, ((c a : ℝ) / n) ^ (c a)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    -- Step 8: card ≤ (n+1)^|α|.
    have h_card_le : ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
        ≤ ((n : ℝ) + 1) ^ Fintype.card α := by
      have := piAntidiag_card_le (α := α) n
      have h_cast : (((n + 1) ^ Fintype.card α : ℕ) : ℝ)
          = ((n : ℝ) + 1) ^ Fintype.card α := by push_cast; ring
      have := (Nat.cast_le (α := ℝ)).mpr this
      rwa [h_cast] at this
    -- Step 9: combine.
    -- From h_card_bound: 1 ≤ K · M (where K = card piAntidiag, M = mult · ∏(c/n)^c).
    -- From h_card_le: K ≤ (n+1)^|α|.
    -- So 1 ≤ (n+1)^|α| · M, i.e., (n+1)^{-|α|} ≤ M = mult · ∏(c/n)^c.
    have h_M_nn : 0 ≤ (Nat.multinomial Finset.univ c : ℝ)
        * ∏ a, ((c a : ℝ) / n) ^ (c a) := h_term_nn c hc_mem
    have h_chain : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ Fintype.card α
        * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) := by
      calc (1 : ℝ) ≤ ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
              * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) :=
            h_card_bound
        _ ≤ ((n : ℝ) + 1) ^ Fintype.card α
              * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) :=
            mul_le_mul_of_nonneg_right h_card_le h_M_nn
    -- Step 10: turn into the goal.
    -- Goal: (n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ multinomial univ c.
    -- We have: 1 ≤ (n+1)^|α| · multinomial univ c · ∏ (c/n)^c
    --          = (n+1)^|α| · multinomial univ c · ∏ c^c / n^n.
    -- ⟹ n^n ≤ (n+1)^|α| · multinomial univ c · ∏ c^c.
    -- ⟹ n^n / (∏ c^c) ≤ (n+1)^|α| · multinomial univ c.
    -- ⟹ (n+1)^{-|α|} · n^n / ∏ c^c ≤ multinomial univ c.
    -- First rewrite ∏ (c/n)^c = ∏ c^c / n^n.
    have h_prod_split : ∏ a, ((c a : ℝ) / n) ^ (c a)
        = (∏ a, (c a : ℝ) ^ (c a)) / (n : ℝ) ^ n := by
      rw [show ∏ a, ((c a : ℝ) / n) ^ (c a)
              = ∏ a, ((c a : ℝ) ^ (c a) / (n : ℝ) ^ (c a)) from
          Finset.prod_congr rfl (fun a _ => div_pow _ _ _)]
      rw [Finset.prod_div_distrib]
      congr 1
      rw [Finset.prod_pow_eq_pow_sum, hc_sum]
    rw [h_prod_split] at h_chain
    -- h_chain : 1 ≤ (n+1)^|α| · multinomial · (∏ c^c / n^n).
    -- Multiply by n^n / ∏ c^c (positive).
    -- But first: need ∏ c^c > 0? Could be 0 if some c(a) = 0 — no, 0^0 = 1, so each factor ≥ 1
    -- when c(a) ≥ 1. When c(a) = 0, factor = 0^0 = 1. So all factors ≥ 1.
    -- Actually for c(a) = 0, (c a : ℝ)^(c a) = 0^0 = 1 in ℝ (Real convention).
    -- So ∏ ≥ 1 > 0.
    have h_prod_cc_pos : (0 : ℝ) < ∏ a, (c a : ℝ) ^ (c a) := by
      refine Finset.prod_pos fun a _ => ?_
      rcases Nat.eq_zero_or_pos (c a) with h0 | hp
      · rw [h0]; simp
      · exact pow_pos (by exact_mod_cast hp) _
    have h_n_pow_pos : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hn_real_pos _
    -- Manipulate h_chain.
    -- 1 ≤ (n+1)^|α| · M · (P / n^n) where P = ∏ c^c, M = mult.
    -- ⟹ n^n ≤ (n+1)^|α| · M · P.
    -- ⟹ n^n / P ≤ (n+1)^|α| · M.
    -- ⟹ (n+1)^{-|α|} · n^n / P ≤ M.
    have h_npow_le :
        (n : ℝ) ^ n ≤ ((n : ℝ) + 1) ^ Fintype.card α
          * (Nat.multinomial Finset.univ c : ℝ) * (∏ a, (c a : ℝ) ^ (c a)) := by
      have := mul_le_mul_of_nonneg_right h_chain h_n_pow_pos.le
      rw [one_mul] at this
      have h_rhs_eq : ((n : ℝ) + 1) ^ Fintype.card α
          * ((Nat.multinomial Finset.univ c : ℝ)
              * ((∏ a, (c a : ℝ) ^ (c a)) / (n : ℝ) ^ n)) * (n : ℝ) ^ n
          = ((n : ℝ) + 1) ^ Fintype.card α
              * (Nat.multinomial Finset.univ c : ℝ) * (∏ a, (c a : ℝ) ^ (c a)) := by
        field_simp
      rw [h_rhs_eq] at this
      exact this
    -- Divide by ∏ c^c (positive).
    have h_div :
        (n : ℝ) ^ n / (∏ a, (c a : ℝ) ^ (c a))
          ≤ ((n : ℝ) + 1) ^ Fintype.card α
              * (Nat.multinomial Finset.univ c : ℝ) := by
      rw [div_le_iff₀ h_prod_cc_pos]
      linarith [h_npow_le]
    -- Multiply by (n+1)^{-|α|} (positive).
    have h_succ_pow_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ Fintype.card α :=
      pow_pos hn_real_succ_pos _
    rw [← div_le_iff₀' h_succ_pow_pos] at h_div
    rw [show (((n : ℝ) + 1) ^ Fintype.card α)⁻¹
            * ((n : ℝ) ^ n / ∏ a, ((c a : ℝ) ^ (c a)))
          = ((n : ℝ) ^ n / (∏ a, ((c a : ℝ) ^ (c a))))
              / ((n : ℝ) + 1) ^ Fintype.card α by
      field_simp]
    exact h_div

omit [Nonempty α] in
/-- **Lower bound on `Q^n(T_c)`** (Phase C 主補題, from `typeClassByCount_card_ge`):
`Q^n(T_c) ≥ (n+1)^{-|α|} · exp(-n · klDivIndex c n Q)`.

Derivation: `Q^n(T_c) = |T_c| · ∏ Q(a)^c(a)` (per-x identity), and the
multinomial lower bound gives `|T_c| · ∏ Q(a)^c(a) ≥ (n+1)^{-|α|} · n^n / ∏ c(a)^c(a) · ∏ Q(a)^c(a)`,
which after algebra equals `(n+1)^{-|α|} · exp(-n · klDivIndex c n Q)`. -/
theorem typeClassByCount_Qn_ge
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ * Real.exp (-((n : ℝ) * klDivIndex c n Q))
      ≤ ((Measure.pi (fun _ : Fin n => Q)) (typeClassByCount (α := α) c)).toReal := by
  classical
  -- Setup.
  set T : Finset (Fin n → α) := (typeClassByCount (α := α) c).toFinite.toFinset with hT_def
  have hT_coe : (T : Set (Fin n → α)) = typeClassByCount c := by simp [hT_def]
  set qm : α → ℝ := fun a => Q.real {a} with hqm_def
  set N : ℝ := (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ with hN_def
  -- Step 1: Q^n(T_c) (set form) = sum over T of ∏ Q(x_i).
  have h_pi_singleton_Q : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n => Q)).real {x}) = ∏ i : Fin n, qm (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal = ∏ i : Fin n, qm (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have h_pi_eq_sum :
      ((Measure.pi (fun _ : Fin n => Q)) (typeClassByCount (α := α) c)).toReal
        = ∑ x ∈ T, ∏ i : Fin n, qm (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n => Q)) (T : Set (Fin n → α))).toReal
        = ∑ x ∈ T, ((Measure.pi (fun _ : Fin n => Q)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n => Q)) T]
    rw [← hT_coe, h_step]
    refine Finset.sum_congr rfl fun x _ => h_pi_singleton_Q x
  -- Step 2: For each x ∈ T, ∏ Q(x_i) = ∏ Q(a)^c(a).
  have h_per_point : ∀ x ∈ T,
      (∏ i : Fin n, qm (x i)) = ∏ a : α, qm a ^ (c a) := by
    intro x hx
    have hxT : x ∈ typeClassByCount c := (Set.Finite.mem_toFinset _).mp hx
    -- ∏_i qm (x_i) = ∏ a, qm(a)^c(a) via fiberwise.
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
      fun i _ => Finset.mem_univ _
    have h := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps (fun a : α => qm a)
    rw [← h]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_const]
    have : (Finset.univ.filter fun j : Fin n => x j = a).card = c a := hxT a
    rw [this]
  -- Step 3: ∑_{x ∈ T} ∏ Q(x_i) = |T| · ∏ Q(a)^c(a).
  have h_sum_eq : (∑ x ∈ T, ∏ i : Fin n, qm (x i))
      = (T.card : ℝ) * ∏ a : α, qm a ^ (c a) := by
    rw [Finset.sum_congr rfl h_per_point]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h_pi_eq_sum, h_sum_eq]
  -- Now need: N · exp(-n · klDivIndex) ≤ |T| · ∏ Q(a)^c(a).
  -- Use typeClassByCount_card_ge: |T| ≥ N · n^n / ∏ c(a)^c(a).
  have h_card_ge := typeClassByCount_card_ge c hc_sum
  -- Show: N · exp(-n klDivIndex c n Q) = N · n^n · ∏ Q(a)^c(a) / ∏ c(a)^c(a).
  -- This requires computing exp(-n klDivIndex) = ∏ (c(a)/n · Q(a) / (c(a)/n))^c(a) ...
  -- Easier: exp(-n klDivIndex) = exp(∑ c(a) · log Q(a) - ∑ c(a) log (c(a)/n)) (n × klDivIndex)
  --                          = (∏ Q(a)^c(a)) / (∏ (c(a)/n)^c(a))
  --                          = n^n · ∏ Q(a)^c(a) / ∏ c(a)^c(a) (when c(a) > 0; 0 terms cancel)
  -- For c(a) = 0: 0^0 = 1, so (c(a)/n)^0 = 1, contribution unchanged.
  have h_exp_eq : Real.exp (-((n : ℝ) * klDivIndex c n Q))
      = ((n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a))) * ∏ a : α, qm a ^ (c a) := by
    -- (n × klDivIndex) = ∑ a, c(a) · (log (c(a)/n) - log Q(a))
    have h_n_klDiv : (n : ℝ) * klDivIndex c n Q
        = ∑ a : α, (c a : ℝ) * (Real.log ((c a : ℝ) / n) - Real.log (qm a)) := by
      unfold klDivIndex
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rcases eq_or_ne (c a) 0 with h0 | h_pos
      · simp [h0]
      · have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
        have hc_real_pos : (0 : ℝ) < (c a : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h_pos)
        show (n : ℝ) * ((c a : ℝ) / (n : ℝ) *
              (Real.log ((c a : ℝ) / (n : ℝ)) - Real.log (Q.real {a})))
            = (c a : ℝ) * (Real.log ((c a : ℝ) / (n : ℝ)) - Real.log (qm a))
        rw [hqm_def]
        field_simp
    rw [h_n_klDiv]
    rw [show -∑ a : α, (c a : ℝ) * (Real.log ((c a : ℝ) / n) - Real.log (qm a))
        = ∑ a : α, (c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n)) by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring]
    rw [Real.exp_sum]
    -- ∏ a, exp(c(a) · (log Q(a) - log (c(a)/n))) = ∏ a, (Q(a) / (c(a)/n))^c(a)
    -- (when c(a) > 0; when c(a) = 0: exp(0) = 1 = 1).
    -- Also = ∏ a, Q(a)^c(a) / (c(a)/n)^c(a)
    -- = ∏ Q(a)^c(a) / ∏ (c(a)/n)^c(a)
    -- = ∏ Q(a)^c(a) · n^c(a) / c(a)^c(a) ... by individual letter.
    -- ∏ n^c(a) = n^(∑c) = n^n.
    -- So result = n^n · ∏ Q(a)^c(a) / ∏ c(a)^c(a).
    have h_per_letter : ∀ a : α,
        Real.exp ((c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n)))
          = qm a ^ (c a) * ((n : ℝ) ^ (c a) / (c a : ℝ) ^ (c a)) := by
      intro a
      rcases eq_or_ne (c a) 0 with h0 | h_pos
      · simp [h0]
      have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hc_real_pos : (0 : ℝ) < (c a : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h_pos)
      have hqm_a_pos : 0 < qm a := hQpos a
      have h_div_pos : 0 < (c a : ℝ) / n := div_pos hc_real_pos hn_real_pos
      -- Expand: c(a) · (log Q - log (c/n)) = c(a) log Q - c(a) log (c/n)
      --   = log Q^c(a) - log (c/n)^c(a)
      --   = log (Q^c(a) / (c/n)^c(a))
      rw [show (c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n))
            = Real.log (qm a ^ (c a)) - Real.log (((c a : ℝ) / n) ^ (c a)) by
            rw [Real.log_pow, Real.log_pow]; ring]
      rw [← Real.log_div (pow_pos hqm_a_pos _).ne' (pow_pos h_div_pos _).ne']
      rw [Real.exp_log (div_pos (pow_pos hqm_a_pos _) (pow_pos h_div_pos _))]
      rw [div_pow]
      -- qm a ^ c a / ((c a)^c a / n^c a) = qm a ^ c a · (n^c a / c a^c a)
      field_simp
    rw [show (∏ a : α, Real.exp ((c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n))))
          = ∏ a : α, qm a ^ (c a) * ((n : ℝ) ^ (c a) / (c a : ℝ) ^ (c a)) from
        Finset.prod_congr rfl fun a _ => h_per_letter a]
    -- Now: ∏ a, qm a ^ c a · n^c(a) / c(a)^c(a)
    -- = (∏ qm^c) · (∏ n^c / c^c)
    -- = (∏ qm^c) · (∏ n^c) / (∏ c^c)
    -- ∏ n^c(a) = n^(∑ c(a)) = n^n.
    rw [Finset.prod_mul_distrib]
    rw [show (∏ a : α, (n : ℝ) ^ (c a) / (c a : ℝ) ^ (c a))
          = (∏ a : α, (n : ℝ) ^ (c a)) / ∏ a : α, ((c a : ℝ) ^ (c a)) by
        rw [Finset.prod_div_distrib]]
    rw [show (∏ a : α, (n : ℝ) ^ (c a)) = (n : ℝ) ^ n by
      rw [Finset.prod_pow_eq_pow_sum, hc_sum]]
    ring
  rw [h_exp_eq]
  -- Now: N · n^n / ∏ c^c · ∏ qm^c ≤ |T| · ∏ qm^c.
  -- Equivalent to: (|T| - N · n^n / ∏ c^c) · ∏ qm^c ≥ 0, which holds if ∏ qm^c ≥ 0
  -- AND |T| ≥ N · n^n / ∏ c^c (the card lower bound).
  have h_qm_prod_nn : 0 ≤ ∏ a : α, qm a ^ (c a) :=
    Finset.prod_nonneg fun a _ => pow_nonneg (hQpos a).le _
  have h_T_card : (T.card : ℝ) = ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) := by
    rfl
  rw [h_T_card] at *
  -- Goal: N · ((n^n / ∏ c^c) · ∏ qm^c) ≤ |T| · ∏ qm^c.
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right h_card_ge h_qm_prod_nn

/-! ### Phase D — liminf 形 lower bound -/

/-- **Sanov LDP lower bound (single-rounding sequence)**:
`roundedTypeIndex P n ∈ E n` が eventually 成り立つとき
`liminf (1/n) log Q^n(⋃ c ∈ E n, T_c) ≥ -klDivSumForm_ofVec P (Q.real ∘ singleton)`.

証明 sketch:
1. `T_{c_n} ⊆ ⋃ c ∈ E n, T_c` (c_n ∈ E n から)。
2. Phase C: `Q^n(T_{c_n}) ≥ (n+1)^{-|α|} · exp(-n · klDivIndex c_n n Q)`.
3. `(1/n) log Q^n(⋃) ≥ -|α| · log(n+1)/n - klDivIndex c_n n Q`.
4. `log(n+1)/n → 0` (B-1' `log_succ_div_tendsto_zero`),
   `klDivIndex c_n n Q → klDivSumForm_ofVec P` (Phase B `klDivIndex_rounded_tendsto`).
5. liminf inequality. -/
theorem sanov_ldp_lower_bound_pointwise
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (P : α → ℝ) (hP_prob : (∑ a, P a) = 1)
    (hP_full : ∀ a, 0 < P a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n) :
    -klDivSumForm_ofVec P (fun a => Q.real {a})
      ≤ Filter.liminf (fun n : ℕ => (1 / (n : ℝ)) * Real.log
          (((Measure.pi (fun _ : Fin n => Q))
            (⋃ c ∈ E n, typeClassByCount (α := α)
              (fun a => (c a : ℕ)))).toReal)) atTop := by
  classical
  set D : ℝ := klDivSumForm_ofVec P (fun a => Q.real {a}) with hD_def
  set K : ℝ := (Fintype.card α : ℝ) with hK_def
  set f : ℕ → ℝ := fun n => (1 / (n : ℝ)) * Real.log
    (((Measure.pi (fun _ : Fin n => Q))
      (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) with hf_def
  have hP_nn : ∀ a, 0 ≤ P a := fun a => (hP_full a).le
  -- Lower bound `f n ≥ -K · log(n+1)/n - klDivIndex (c_n) n Q` eventually.
  -- Define `g n := -K · log(n+1)/n - klDivIndex (c_n) n Q`; show f ≥ g eventually, and g → -D.
  set c_seq : ∀ n, α → ℕ := fun n a => (roundedTypeIndex P n a : ℕ)
  set g : ℕ → ℝ := fun n => -K * (Real.log ((n : ℝ) + 1) / (n : ℝ))
    - klDivIndex (c_seq n) n Q with hg_def
  -- g → -D.
  have hg_tendsto : Tendsto g atTop (𝓝 (-D)) := by
    have h_log_zero : Tendsto (fun n : ℕ => -K * (Real.log ((n : ℝ) + 1) / (n : ℝ)))
        atTop (𝓝 (-K * 0)) := log_succ_div_tendsto_zero.const_mul (-K)
    rw [mul_zero] at h_log_zero
    have h_kl : Tendsto (fun n : ℕ => klDivIndex (c_seq n) n Q) atTop (𝓝 D) :=
      klDivIndex_rounded_tendsto Q hQpos P hP_prob hP_nn
    have h_sub := h_log_zero.sub h_kl
    rw [zero_sub] at h_sub
    exact h_sub
  -- f n ≥ g n eventually.
  have h_f_ge_g : ∀ᶠ n : ℕ in atTop, g n ≤ f n := by
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    filter_upwards [h_n_pos, h_in_E] with n hn_pos h_inE
    have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
    -- T_{c_n} ⊆ ⋃ c ∈ E n, T_c (because c_n ∈ E n).
    have h_subset :
        (typeClassByCount (α := α) (n := n) (c_seq n))
        ⊆ ⋃ c ∈ E n, typeClassByCount (α := α) (n := n) (fun a => (c a : ℕ)) := by
      intro x hx
      simp only [Set.mem_iUnion]
      exact ⟨roundedTypeIndex P n, h_inE, hx⟩
    -- Phase C: Q^n(T_{c_n}) ≥ (n+1)^{-|α|} exp(-n klDivIndex c_n n Q).
    have h_Qn_ge := typeClassByCount_Qn_ge Q hQpos hn_pos (c_seq n)
      (roundedTypeIndex_sum P hP_prob hP_nn n hn_pos)
    -- Q^n(⋃) ≥ Q^n(T_{c_n}).
    have h_union_ge : ((Measure.pi (fun _ : Fin n => Q))
          (typeClassByCount (α := α) (c_seq n))).toReal
        ≤ ((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
      apply ENNReal.toReal_mono
      · exact measure_ne_top _ _
      · exact measure_mono h_subset
    -- Combine: Q^n(⋃) ≥ (n+1)^{-|α|} exp(-n klDivIndex).
    have h_union_lb :
        (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
          * Real.exp (-((n : ℝ) * klDivIndex (c_seq n) n Q))
        ≤ ((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal :=
      h_Qn_ge.trans h_union_ge
    -- Take log: log Q^n(⋃) ≥ log((n+1)^{-|α|}) + log(exp(-n klDivIndex)) = -|α| log(n+1) - n klDivIndex.
    have h_lb_pos : (0 : ℝ) <
        (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
          * Real.exp (-((n : ℝ) * klDivIndex (c_seq n) n Q)) := by
      apply mul_pos
      · positivity
      · exact Real.exp_pos _
    have h_union_pos : 0 < ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal :=
      lt_of_lt_of_le h_lb_pos h_union_lb
    have h_log_mono : Real.log
        ((((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
          * Real.exp (-((n : ℝ) * klDivIndex (c_seq n) n Q)))
        ≤ Real.log (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) :=
      Real.log_le_log h_lb_pos h_union_lb
    -- Compute log of LHS.
    have h_log_lhs : Real.log
        ((((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
          * Real.exp (-((n : ℝ) * klDivIndex (c_seq n) n Q)))
        = -K * Real.log ((n : ℝ) + 1) - (n : ℝ) * klDivIndex (c_seq n) n Q := by
      have hpow_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ (Fintype.card α : ℕ) := by positivity
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne']
      rw [Real.log_inv, Real.log_pow, Real.log_exp]
      ring
    rw [h_log_lhs] at h_log_mono
    -- Now: -K log(n+1) - n klDivIndex ≤ log Q^n(⋃).
    -- Divide by n: -K log(n+1)/n - klDivIndex ≤ (1/n) log Q^n(⋃) = f n.
    have h_one_div_pos : 0 < 1 / (n : ℝ) := by positivity
    have h_mul := mul_le_mul_of_nonneg_left h_log_mono h_one_div_pos.le
    show g n ≤ f n
    rw [hg_def, hf_def]
    -- (1/n) · (-K log(n+1) - n klDivIndex) = -K log(n+1)/n - klDivIndex.
    have h_lhs_eq : (1 / (n : ℝ)) * (-K * Real.log ((n : ℝ) + 1)
          - (n : ℝ) * klDivIndex (c_seq n) n Q)
        = -K * (Real.log ((n : ℝ) + 1) / (n : ℝ)) - klDivIndex (c_seq n) n Q := by
      field_simp
    rw [h_lhs_eq] at h_mul
    exact h_mul
  -- Conclude: liminf f ≥ liminf g = -D (since g tendsto -D, liminf = -D).
  -- Need IsBoundedUnder (· ≥ ·) atTop g (bounded below): g tendsto -D, so eventually g ≥ -D - 1.
  have h_g_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop g := by
    refine ⟨-D - 1, ?_⟩
    rw [Filter.eventually_map]
    have : ∀ᶠ n : ℕ in atTop, g n ∈ Set.Ioo (-D - 1) (-D + 1) := by
      apply hg_tendsto.eventually
      exact isOpen_Ioo.mem_nhds (by constructor <;> linarith)
    filter_upwards [this] with n hn; exact hn.1.le
  -- Need IsCoboundedUnder (· ≥ ·) atTop f: dual of bounded above. We have f bounded below ≥ log m,
  -- but `IsCoboundedUnder (· ≥ ·)` needs: ∃ b, ∀ b' (s.t. eventually b' ≥ f), b' ≥ b.
  -- Equivalently: f's eventual lower bounds are bounded. Since f ≥ log m (some fixed value), this holds.
  -- Use that bounded below ⟹ cobounded for `≥`.
  -- Actually IsCoboundedUnder (· ≥ ·) f = IsCobounded (· ≥ ·) (map f atTop).
  -- For atTop in ℝ, this should follow from bounded above. Let me derive.
  -- Get bounded above for f: tricky. But IsCobounded follows from IsBounded.
  have h_f_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop f := by
    -- f n ≤ 0 since Q^n(⋃) ≤ 1 and log ≤ 0 of value ≤ 1; (1/n) · negative ≤ 0.
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    filter_upwards [h_n_pos] with n hn_pos
    -- f n = (1/n) log Q^n. Q^n ≤ 1, so log ≤ 0, so (1/n) log ≤ 0.
    show f n ≤ 0
    rw [hf_def]
    have h_Qn_le_one : ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal ≤ 1 := by
      have := MeasureTheory.measureReal_le_one (μ := Measure.pi (fun _ : Fin n => Q))
        (s := ⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))
      simpa [MeasureTheory.measureReal_def] using this
    have h_one_div_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    -- log of value ≤ 1: if value > 0, log ≤ 0. If value = 0, log = 0.
    rcases eq_or_lt_of_le (le_of_lt (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) h_one_div_nn))
      with h_div_eq | h_div_pos
    · -- 1/n = 0 (impossible since n > 0). Skip
      have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have : 1 / (n : ℝ) > 0 := by positivity
      linarith
    · have h_log_le : Real.log
          (((Measure.pi (fun _ : Fin n => Q))
            (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) ≤ 0 := by
        apply Real.log_nonpos
        · exact ENNReal.toReal_nonneg
        · exact h_Qn_le_one
      have h_mul_le := mul_nonpos_of_nonneg_of_nonpos h_one_div_nn h_log_le
      exact h_mul_le
  have h_f_cobdd : Filter.IsCoboundedUnder (· ≥ ·) atTop f :=
    h_f_bdd_above.isCoboundedUnder_flip
  have h_liminf_le : liminf g atTop ≤ liminf f atTop :=
    Filter.liminf_le_liminf h_f_ge_g h_g_bdd_below h_f_cobdd
  rw [hg_tendsto.liminf_eq] at h_liminf_le
  exact h_liminf_le


/-! ### Phase E — Tendsto sandwich (main theorem) -/

/-- **Sanov LDP equality form** (B-1'' 主定理, Cover-Thomas Theorem 11.4.1 簡略形):

```
(1/n) log Q^n(⋃ c ∈ E n, T_c)  →  -klDivSumForm_ofVec P (Q.real ∘ singleton)
```

入力: `P` (minimizer のユーザ指定形), `E n` が eventually `roundedTypeIndex P n` を含む,
`∀ c ∈ E n, klDivSumForm_ofVec P Q ≤ klDivIndex c n Q` (minimizer 性).

証明 sketch: B-1' upper bound (`sanov_ldp_upper_bound`) で `limsup ≤ -D + ε` (∀ ε > 0)
⇒ `limsup ≤ -D`. Phase D で `liminf ≥ -D`. `tendsto_of_le_liminf_of_limsup_le` で sandwich. -/
@[entry_point]
theorem sanov_ldp_equality
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (P : α → ℝ) (hP_prob : (∑ a, P a) = 1)
    (hP_full : ∀ a, 0 < P a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n)
    (h_minimizer : ∀ n, ∀ c ∈ E n,
      klDivSumForm_ofVec P (fun a => Q.real {a})
        ≤ klDivIndex (fun a => (c a : ℕ)) n Q) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal))
      atTop (𝓝 (-(klDivSumForm_ofVec P (fun a => Q.real {a})))) := by
  classical
  set D : ℝ := klDivSumForm_ofVec P (fun a => Q.real {a}) with hD_def
  set f : ℕ → ℝ := fun n => (1 / (n : ℝ)) * Real.log
    (((Measure.pi (fun _ : Fin n => Q))
      (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) with hf_def
  have hP_nn : ∀ a, 0 ≤ P a := fun a => (hP_full a).le
  -- Lower bound (from Phase D): -D ≤ liminf f.
  have h_liminf : -D ≤ liminf f atTop :=
    sanov_ldp_lower_bound_pointwise Q hQpos P hP_prob hP_full E h_in_E
  -- Upper bound (from B-1'): limsup f ≤ -D.
  -- Strategy: provide eventually upper bound `f ≤ -D + ε` for any ε > 0, conclude `f` bounded above.
  -- Then use ε → 0 to get limsup ≤ -D.
  have h_upper_event : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, f n ≤ -D + ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := sanov_ldp_upper_bound Q hQpos E D h_minimizer hε
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    have h_n_ge : ∀ᶠ n : ℕ in atTop, N₀ ≤ n :=
      Filter.eventually_atTop.mpr ⟨N₀, fun n hn => hn⟩
    filter_upwards [h_n_pos, h_n_ge, h_in_E] with n hn_pos hn_ge h_inE
    -- Q^n(⋃) > 0: since T_{c_n} ⊆ ⋃ and T_{c_n} nonempty, Q^n nonempty subset > 0.
    have h_meas_pos : 0 < ((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
      obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
        (fun a => (roundedTypeIndex P n a : ℕ))
        (roundedTypeIndex_sum P hP_prob hP_nn n hn_pos)
      have hx_in_union : x ∈ ⋃ c ∈ E n,
          typeClassByCount (α := α) (fun a => (c a : ℕ)) := by
        simp only [Set.mem_iUnion]
        exact ⟨roundedTypeIndex P n, ⟨h_inE, hx⟩⟩
      have h_singleton_pos : (0 : ℝ) <
          ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal := by
        rw [Measure.pi_singleton, ENNReal.toReal_prod]
        apply Finset.prod_pos
        intros i _
        exact hQpos (x i)
      have h_singleton_le : ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal
          ≤ ((Measure.pi (fun _ : Fin n => Q))
              (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
        apply ENNReal.toReal_mono
        · exact measure_ne_top _ _
        · exact measure_mono (Set.singleton_subset_iff.mpr hx_in_union)
      linarith
    exact hN₀ n hn_ge hn_pos h_meas_pos
  -- bounded above eventually: f ≤ -D + 1. (`IsBoundedUnder (·≤·)`: ∃b, eventually f ≤ b.)
  have h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop f := by
    refine ⟨-D + 1, ?_⟩
    rw [Filter.eventually_map]
    have := h_upper_event 1 (by norm_num)
    filter_upwards [this] with n hn; exact hn
  -- bounded below eventually: -D ≤ liminf is fine in the conditionally complete world,
  -- but for IsBoundedUnder ge we use the Phase D liminf bound to get a uniform finite lower bound.
  -- f n ≥ -D - 1 eventually (via Phase D or just: f bounded since 0 < Q^n ≤ 1, log ≤ 0).
  -- f n is bounded below uniformly using ` Q^n(⋃) ≥ Q^n({x}) ≥ (∏ Q(x_i)) ≥ (min Q a)^n `.
  -- ⇒ log Q^n(⋃) ≥ n · log (min Q a), so (1/n) log Q^n(⋃) ≥ log (min Q a) = -|log (min Q a)|.
  -- Pick `M := -log (min_a Q.real {a})` (positive, finite, since each Q.real {a} > 0 and finite α).
  have h_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop f := by
    -- Get minimum: m := min_a Q.real {a} > 0 since α nonempty Fintype.
    obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image (s := (Finset.univ : Finset α))
      (f := fun a => Q.real {a}) ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
    -- ha₀ : ∀ a' ∈ univ, Q.real {a₀} ≤ Q.real {a'}
    set m : ℝ := Q.real {a₀}
    have hm_pos : 0 < m := hQpos a₀
    refine ⟨Real.log m, ?_⟩
    rw [Filter.eventually_map]
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    filter_upwards [h_n_pos, h_in_E] with n hn_pos h_inE
    -- Bound f n ≥ log m.
    obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
      (fun a => (roundedTypeIndex P n a : ℕ))
      (roundedTypeIndex_sum P hP_prob hP_nn n hn_pos)
    have hx_in_union : x ∈ ⋃ c ∈ E n,
        typeClassByCount (α := α) (fun a => (c a : ℕ)) := by
      simp only [Set.mem_iUnion]
      exact ⟨roundedTypeIndex P n, ⟨h_inE, hx⟩⟩
    -- Q^n({x}) = ∏ Q.real {x_i} ≥ m^n.
    have h_singleton_eq : ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal
        = ∏ i : Fin n, Q.real {x i} := by
      rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl
    have h_singleton_ge : ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal ≥ m ^ n := by
      rw [h_singleton_eq]
      calc m ^ n = ∏ _i : Fin n, m := by rw [Finset.prod_const]; simp
        _ ≤ ∏ i : Fin n, Q.real {x i} :=
          Finset.prod_le_prod (fun i _ => hm_pos.le)
            (fun i _ => ha₀ (x i) (Finset.mem_univ _))
    have h_union_ge_m_pow : ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal ≥ m ^ n := by
      have h1 : ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal
          ≤ ((Measure.pi (fun _ : Fin n => Q))
              (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
        apply ENNReal.toReal_mono
        · exact measure_ne_top _ _
        · exact measure_mono (Set.singleton_subset_iff.mpr hx_in_union)
      linarith
    -- So log Q^n(⋃) ≥ log (m^n) = n log m, and (1/n) log ≥ log m.
    have h_pow_pos : (0 : ℝ) < m ^ n := pow_pos hm_pos _
    have h_union_pos : (0 : ℝ) < ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
      linarith
    have h_log_ge : Real.log m ≤ (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) := by
      have h_log_pow_le : Real.log (m ^ n) ≤ Real.log
        (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) :=
        Real.log_le_log h_pow_pos h_union_ge_m_pow
      rw [Real.log_pow] at h_log_pow_le
      have h_n_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have h_n_inv_pos : 0 < 1 / (n : ℝ) := by positivity
      have h := mul_le_mul_of_nonneg_left h_log_pow_le h_n_inv_pos.le
      rw [show (1 / (n : ℝ)) * ((n : ℝ) * Real.log m) = Real.log m by field_simp] at h
      exact h
    -- goal: f n ≥ Real.log m, i.e. Real.log m ≤ f n
    exact h_log_ge
  -- Now: limsup f ≤ -D.
  have h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop f :=
    h_bdd_below.isCoboundedUnder_flip
  have h_limsup : limsup f atTop ≤ -D := by
    -- For any ε > 0, limsup f ≤ -D + ε. So limsup f ≤ -D.
    by_contra h_lt
    push Not at h_lt
    -- now: -D < limsup f. Find ε > 0 small enough.
    set ε := (limsup f atTop - (-D)) / 2 with hε_def
    have hε_pos : 0 < ε := by positivity
    have h_event := h_upper_event ε hε_pos
    have h_ub : limsup f atTop ≤ -D + ε :=
      Filter.limsup_le_of_le h_cobdd h_event
    -- limsup f > -D, but limsup f ≤ -D + ε with ε = (limsup f + D)/2. Contradiction.
    have : limsup f atTop - (-D) ≤ ε := by linarith
    have : limsup f atTop - (-D) ≤ (limsup f atTop - (-D)) / 2 := by
      rw [hε_def] at this; exact this
    have h_pos : 0 < limsup f atTop - (-D) := by linarith
    linarith
  exact tendsto_of_le_liminf_of_limsup_le h_liminf h_limsup

end InformationTheory.Shannon
