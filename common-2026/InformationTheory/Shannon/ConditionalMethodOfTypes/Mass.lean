import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.StrongTypicality
import InformationTheory.Shannon.Sanov.TendstoSandwich
import InformationTheory.Shannon.TypeClassLowerBound
import InformationTheory.Shannon.RateDistortion.AchievabilityJointStrongTypicality
import InformationTheory.Shannon.ConditionalMethodOfTypes.Core

/-!
# Conditional method of types — Mass assembly

Main assembly for the conditional method of types: the marginal-Y
identification and per-`y` Y-product mass lower bound, the entropy
concentration helper `conditional_KL_concentration_ge`, and the headline
theorem `conditionalStronglyTypicalSlice_mass_ge`.

This file is part of the `ConditionalMethodOfTypes` umbrella and builds on
`InformationTheory.Shannon.ConditionalMethodOfTypes.Core`.
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
/-! ### Main assembly

The main theorem combines the four pieces:
1. **`floorMatrix` construction**: pick a single c_floor with
   row sums = typeCount x, total = n, and entries close to `n · qZ`.
2. **`floorMatrix_dist_le`**: the rounding stays within
   `ε_X + |β|/n` of `qZ`. For n large or ε > ε_X, c_floor ∈ `sliceTypeIndices`.
3. **`conditionalTypeClass_card_ge`**: the slice
   contains `conditionalTypeClass x c_floor` which has cardinality
   `≥ poly(n)⁻¹ · ∏_a (T_a^{T_a} / ∏_b c(a,b)^{c(a,b)})` (per-row multinomial).
4. **`productMass_eq_columnProd`**: for each `y` in this
   class, Y-product mass equals `∏_b qY(b)^{col_b}`.

Final algebra (the assembly): combining the cardinality bound, the per-y mass,
and the entropy chain rule `H(X) + H(Y) - H(Z) = I(X;Y)` yields the desired
exponential bound. Additionally requires marginal-compatibility hypotheses
(`hmarg_X`, `hmarg_Y`) which are typically supplied by the caller's construction
(e.g. `rdAmbient qStar` provides both marginals from a single joint pmf). -/

omit [DecidableEq α] [DecidableEq β] in
/-- **Marginal-Y identification** (helper): the Y-marginal of `qZ` equals `qY`,
i.e., `qY(b) = ∑_a qZ(a, b)`. -/
private lemma qY_eq_sum_qZ
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    (b : β) :
    (μ.map (Ys 0)).real {b} = ∑ a : α, (μ.map (jointSequence Xs Ys 0)).real {(a, b)} := by
  classical
  set qZ : α × β → ℝ := fun p ↦ (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
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
      (fun a ↦ ({(a, b)} : Set (α × β))) := by
    intro a₁ _ a₂ _ ha s hs1 hs2 p hp
    have hp1 := hs1 hp
    have hp2 := hs2 hp
    simp only [Set.mem_singleton_iff] at hp1 hp2
    have heq : (a₁, b) = (a₂, b) := hp1.symm.trans hp2
    exact (ha (Prod.mk.injEq _ _ _ _ |>.mp heq).1).elim
  have h_meas : ∀ a ∈ (Finset.univ : Finset α),
      MeasurableSet ({(a, b)} : Set (α × β)) := fun _ _ ↦ measurableSet_singleton _
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
      ≤ (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real {y} := by
  classical
  set qY : β → ℝ := fun b ↦ (μ.map (Ys 0)).real {b} with hqY_def
  set qZ : α × β → ℝ := fun p ↦ (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
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
  set col : β → ℕ := fun b ↦ ∑ a : α, c (a, b) with hcol_def
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
          refine Finset.sum_le_sum fun a _ ↦ ?_
          exact h_close (a, b)
      _ = (Fintype.card α : ℝ) * (ε_amp / (Fintype.card α : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ε_amp := by field_simp
  -- Step 3: bound ∏_b qY(b)^col_b ≥ exp(-n · (HY + ε_amp · LY)).
  -- Take log: ∑_b col_b · log qY(b) ≥ -n · (HY + ε_amp · LY).
  -- Decomposition: col_b · log qY(b) = n · qY(b) · log qY(b) + (col_b - n · qY(b)) · log qY(b).
  -- Sum: ∑_b col_b · log qY(b) = -n·HY + ∑_b (col_b - n·qY(b)) · log qY(b).
  -- |∑_b (col_b - n·qY(b)) · log qY(b)| ≤ n · ε_amp · LY.
  have h_qY_pos : ∀ b, 0 < qY b := fun b ↦ hposY b
  -- Lower bound `∏ qY^col_b ≥ exp(-n(HY + ε_amp·LY))`.
  have h_prod_pos : 0 < ∏ b : β, qY b ^ col b := by
    refine Finset.prod_pos fun b _ ↦ ?_
    exact pow_pos (h_qY_pos b) _
  rw [← Real.exp_log h_prod_pos]
  refine Real.exp_le_exp.mpr ?_
  have h_log_prod_eq : Real.log (∏ b : β, qY b ^ col b) = ∑ b : β, Real.log (qY b ^ col b) := by
    exact Real.log_prod (fun b _ ↦ (pow_pos (h_qY_pos b) _).ne')
  rw [h_log_prod_eq]
  -- log(∏ qY^col) = ∑_b col_b · log qY(b)
  have h_log_each : ∀ b, Real.log (qY b ^ col b) = (col b : ℝ) * Real.log (qY b) :=
    fun b ↦ Real.log_pow _ _
  rw [Finset.sum_congr rfl (fun b _ ↦ h_log_each b)]
  -- Goal: -(n : ℝ) * (HY + ε_amp · LY) ≤ ∑ b, (col b) · log qY(b)
  -- Bridge: HY = -∑ qY · log qY. So -n·HY = n · ∑ qY · log qY = ∑_b n·qY(b)·log qY(b).
  have h_HY_eq : -(n : ℝ) * HY = ∑ b : β, (n : ℝ) * qY b * Real.log (qY b) := by
    have h_HY_unfold : HY = ∑ b : β, Real.negMulLog (qY b) := by
      show entropy μ (Ys 0) = ∑ b : β, Real.negMulLog (qY b)
      unfold entropy
      rfl
    rw [h_HY_unfold]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Real.negMulLog]
    ring
  -- Decomposition: (col b) · log qY(b) = n·qY(b)·log qY(b) + (col b - n·qY(b)) · log qY(b).
  have h_decomp_sum :
      (∑ b : β, ((col b : ℝ) * Real.log (qY b)))
        = ∑ b : β, (n : ℝ) * qY b * Real.log (qY b)
          + ∑ b : β, ((col b : ℝ) - (n : ℝ) * qY b) * Real.log (qY b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  rw [h_decomp_sum]
  rw [show -(n : ℝ) * (HY + ε_amp * LY)
        = -(n : ℝ) * HY + (-(n : ℝ) * ε_amp * LY) from by ring]
  rw [h_HY_eq]
  -- Now: need -(n · ε_amp · LY) ≤ ∑_b (col_b - n·qY(b)) · log qY(b).
  suffices h : -((n : ℝ) * ε_amp * LY) ≤
      ∑ b : β, ((col b : ℝ) - (n : ℝ) * qY b) * Real.log (qY b) by
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
          refine Finset.sum_congr rfl fun b _ ↦ abs_mul _ _
      _ ≤ ∑ b : β, ((n : ℝ) * ε_amp) * |Real.log (qY b)| := by
          refine Finset.sum_le_sum fun b hb ↦ ?_
          exact mul_le_mul_of_nonneg_right (h_each b hb) (abs_nonneg _)
      _ = (n : ℝ) * ε_amp * ∑ b : β, |Real.log (qY b)| := by
          rw [← Finset.mul_sum]
      _ = (n : ℝ) * ε_amp * LY := by
          rfl
  have h_lb := neg_le_of_abs_le h_abs_bound
  linarith
/-! ### Entropy concentration helper (`conditional_KL_concentration_ge`)

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
lemma KL_le_chi_square_finset
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
lemma sum_diff_log_abs_le_typicality
    {γ : Type*} [Fintype γ] (p q : γ → ℝ) (δ : ℝ)
    (h_close : ∀ a, |p a - q a| ≤ δ) :
    |∑ a : γ, (p a - q a) * Real.log (q a)|
      ≤ δ * ∑ a : γ, |Real.log (q a)| := by
  calc |∑ a : γ, (p a - q a) * Real.log (q a)|
      ≤ ∑ a : γ, |(p a - q a) * Real.log (q a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : γ, |p a - q a| * |Real.log (q a)| := by
        refine Finset.sum_congr rfl fun a _ ↦ abs_mul _ _
    _ ≤ ∑ a : γ, δ * |Real.log (q a)| := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        exact mul_le_mul_of_nonneg_right (h_close a) (abs_nonneg _)
    _ = δ * ∑ a : γ, |Real.log (q a)| := by
        rw [← Finset.mul_sum]

lemma exists_nat_forall_log_succ_div_le {C : ℝ} (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.log ((n : ℝ) + 1) / n ≤ C := by
  have h_lim : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have h_log_id : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h_shift : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
    have h_nat : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
        atTop (𝓝 0) := h_log_id.comp h_shift
    have h_ratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / n) atTop (𝓝 (1 + 0)) := by
        refine tendsto_const_nhds.add ?_
        exact tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp
    have h_prod : Tendsto
        (fun n : ℕ ↦ (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
                        * (((n : ℝ) + 1) / n)) atTop (𝓝 (0 * 1)) := h_nat.mul h_ratio
    rw [zero_mul] at h_prod
    refine h_prod.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1_R : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    field_simp
  rw [Metric.tendsto_atTop] at h_lim
  obtain ⟨N, hN⟩ := h_lim _ hC
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rw [Real.dist_eq, sub_zero] at h
  have h_nn : 0 ≤ Real.log ((n : ℝ) + 1) / n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · have hn_R : (0 : ℝ) < n := by exact_mod_cast hpos
      exact div_nonneg (Real.log_nonneg (by linarith)) hn_R.le
  rw [abs_of_nonneg h_nn] at h
  exact h.le

lemma exists_nat_forall_div_le {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K / n ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (K / C)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hN_le : N ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN_lt : K / C < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hN_le)
  rw [div_lt_iff₀ hC] at hN_lt
  rw [div_le_iff₀ hn_R]
  linarith

lemma exists_nat_forall_le_nat_mul {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ (n : ℝ) * C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (K / C)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hN_le : N ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN_lt : K / C < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hN_le)
  rw [div_lt_iff₀ hC] at hN_lt
  linarith

lemma sum_log_natCast_succ_le {γ : Type*} [Fintype γ] (g : γ → ℕ) (n : ℕ)
    (hg_le : ∀ a, g a ≤ n) :
    (∑ a : γ, Real.log ((g a : ℝ) + 1)) ≤ (Fintype.card γ : ℝ) * Real.log ((n : ℝ) + 1) := by
  have h_each : ∀ a : γ, Real.log ((g a : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := by
    intro a
    have hg_le_R : (g a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hg_le a
    have hg_nn : (0 : ℝ) ≤ (g a : ℝ) := Nat.cast_nonneg _
    apply Real.log_le_log (by linarith : (0 : ℝ) < (g a : ℝ) + 1)
    linarith
  have h_sum_le : (∑ a : γ, Real.log ((g a : ℝ) + 1))
      ≤ ∑ a : γ, Real.log ((n : ℝ) + 1) :=
    Finset.sum_le_sum fun a _ ↦ h_each a
  have h_const : (∑ a : γ, Real.log ((n : ℝ) + 1))
      = (Fintype.card γ : ℝ) * Real.log ((n : ℝ) + 1) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith

lemma sum_measureReal_singleton_eq_one {γ : Type*} [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (ν : Measure γ) [IsProbabilityMeasure ν] :
    (∑ a : γ, ν.real {a}) = 1 := by
  classical
  have h_univ_eq : (Set.univ : Set γ)
      = ⋃ a ∈ (Finset.univ : Finset γ), ({a} : Set γ) := by ext a; simp
  have h_disj : (↑(Finset.univ : Finset γ) : Set γ).PairwiseDisjoint
      (fun a ↦ ({a} : Set γ)) := by
    intro a₁ _ a₂ _ ha s hs1 hs2 q hq
    have hq1 := hs1 hq; have hq2 := hs2 hq
    simp only [Set.mem_singleton_iff] at hq1 hq2
    exact (ha (hq1.symm.trans hq2)).elim
  have h_meas : ∀ a ∈ (Finset.univ : Finset γ),
      MeasurableSet ({a} : Set γ) := fun _ _ ↦ measurableSet_singleton _
  have h_sum : ν.real (Set.univ : Set γ) = ∑ a : γ, ν.real {a} := by
    rw [h_univ_eq, measureReal_biUnion_finset h_disj h_meas]
  have h_univ : ν.real (Set.univ) = 1 := probReal_univ (μ := ν)
  rw [← h_sum, h_univ]

lemma neg_sum_mul_log_eq_neg_sum_mul_log_sub_sum_mul_log_div
    {γ : Type*} [Fintype γ] (p q : γ → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hq_pos : ∀ a, 0 < q a) :
    -∑ a : γ, p a * Real.log (p a)
      = (-∑ a : γ, p a * Real.log (q a))
        - ∑ a : γ, p a * Real.log (p a / q a) := by
  have h_each : ∀ a : γ,
      p a * Real.log (p a)
        = p a * Real.log (q a) + p a * Real.log (p a / q a) := by
    intro a
    rcases lt_or_eq_of_le (hp_nn a) with hpos | hzero
    · rw [show p a * Real.log (q a) + p a * Real.log (p a / q a)
            = p a * (Real.log (q a) + Real.log (p a / q a)) from by ring]
      rw [show Real.log (q a) + Real.log (p a / q a) = Real.log (p a) from by
        rw [Real.log_div hpos.ne' (hq_pos a).ne']; ring]
    · rw [← hzero]; ring
  rw [Finset.sum_congr rfl (fun a _ ↦ h_each a)]
  rw [Finset.sum_add_distrib, neg_add]
  ring

lemma sum_sq_div_le_card_mul {γ : Type*} [Fintype γ] (f r : γ → ℝ)
    (δ m : ℝ) (hm : 0 < m) (h_close : ∀ a, |f a| ≤ δ)
    (h_pos : ∀ a, 0 < r a) (h_min : ∀ a, m ≤ r a) :
    (∑ a : γ, (f a) ^ 2 / r a) ≤ (Fintype.card γ : ℝ) * (δ ^ 2 / m) := by
  have h_each : ∀ a ∈ (Finset.univ : Finset γ), (f a) ^ 2 / r a ≤ δ ^ 2 / m := by
    intro a _
    have h_sq : (f a) ^ 2 ≤ δ ^ 2 := by
      rw [show (f a) ^ 2 = |f a| ^ 2 from (sq_abs _).symm]
      exact pow_le_pow_left₀ (abs_nonneg _) (h_close a) 2
    have h_num_le : (f a) ^ 2 / r a ≤ δ ^ 2 / r a :=
      div_le_div_of_nonneg_right h_sq (h_pos a).le
    have hδ_sq_nn : 0 ≤ δ ^ 2 := sq_nonneg _
    have h_denom_le : δ ^ 2 / r a ≤ δ ^ 2 / m :=
      div_le_div_of_nonneg_left hδ_sq_nn hm (h_min a)
    linarith
  calc ∑ a : γ, (f a) ^ 2 / r a
      ≤ ∑ a : γ, δ ^ 2 / m := Finset.sum_le_sum h_each
    _ = (Fintype.card γ : ℝ) * (δ ^ 2 / m) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma neg_sum_mul_log_le_neg_sum_mul_log_of_sum_eq
    {γ : Type*} [Fintype γ] (p q : γ → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hq_pos : ∀ a, 0 < q a)
    (h_sum_eq : (∑ a : γ, p a) = ∑ a : γ, q a) :
    -∑ a : γ, p a * Real.log (p a)
      ≤ -∑ a : γ, p a * Real.log (q a) := by
  have h_pointwise : ∀ a ∈ (Finset.univ : Finset γ),
      p a * Real.log (q a / p a) ≤ q a - p a := by
    intro a _
    rcases lt_or_eq_of_le (hp_nn a) with hpos | hzero
    · have h_ratio_pos : 0 < q a / p a := div_pos (hq_pos a) hpos
      have hlog := Real.log_le_sub_one_of_pos h_ratio_pos
      have hmul : p a * Real.log (q a / p a) ≤ p a * (q a / p a - 1) :=
        mul_le_mul_of_nonneg_left hlog hpos.le
      refine le_trans hmul ?_
      have h_ratio_ne : p a ≠ 0 := hpos.ne'
      have h_simp : p a * (q a / p a - 1) = q a - p a := by
        rw [mul_sub, mul_one, mul_div_assoc', mul_comm (p a) (q a),
            mul_div_assoc, div_self h_ratio_ne, mul_one]
      linarith
    · rw [← hzero, zero_mul]; linarith [(hq_pos a).le]
  have h_sum1 :
      (∑ a : γ, p a * Real.log (q a / p a)) ≤ ∑ a : γ, (q a - p a) :=
    Finset.sum_le_sum h_pointwise
  have h_sum_zero : (∑ a : γ, (q a - p a)) = 0 := by
    rw [Finset.sum_sub_distrib, h_sum_eq, sub_self]
  have h_diff :
      (-∑ a : γ, p a * Real.log (p a)) - (-∑ a : γ, p a * Real.log (q a))
        = ∑ a : γ, p a * Real.log (q a / p a) := by
    rw [show (-∑ a : γ, p a * Real.log (p a)) - (-∑ a : γ, p a * Real.log (q a))
          = ∑ a : γ, p a * Real.log (q a) - ∑ a : γ, p a * Real.log (p a) from by ring]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rcases lt_or_eq_of_le (hp_nn a) with hpos | hzero
    · rw [Real.log_div (hq_pos a).ne' hpos.ne']; ring
    · rw [← hzero]; simp
  linarith

lemma sum_natCast_mul_log_eq {γ : Type*} [Fintype γ] (g : γ → ℕ) {n : ℕ}
    (hn_ne : (n : ℝ) ≠ 0) (hg_sum : (∑ a : γ, (g a : ℝ)) = n) :
    (∑ a : γ, (g a : ℝ) * Real.log (g a))
      = (n : ℝ) * Real.log (n : ℝ)
        - (n : ℝ) * (-∑ a : γ, ((g a : ℝ) / n) * Real.log ((g a : ℝ) / n)) := by
  have h_each : ∀ a : γ, (g a : ℝ) * Real.log ((g a : ℝ) / n)
      = (g a : ℝ) * Real.log (g a) - (g a : ℝ) * Real.log (n : ℝ) := by
    intro a
    rcases Nat.eq_zero_or_pos (g a) with h | h
    · rw [show ((g a : ℕ) : ℝ) = 0 from by exact_mod_cast h]; simp
    · have hpos : (0 : ℝ) < (g a : ℝ) := by exact_mod_cast h
      rw [Real.log_div hpos.ne' hn_ne]; ring
  have h_sum_each :
      (∑ a : γ, (g a : ℝ) * Real.log ((g a : ℝ) / n))
        = (∑ a : γ, (g a : ℝ) * Real.log (g a))
          - (∑ a : γ, (g a : ℝ)) * Real.log (n : ℝ) := by
    rw [Finset.sum_congr rfl (fun a _ ↦ h_each a), Finset.sum_sub_distrib]
    congr 1; rw [← Finset.sum_mul]
  have hnH : (n : ℝ) * (-∑ a : γ, ((g a : ℝ) / n) * Real.log ((g a : ℝ) / n))
      = -∑ a : γ, (g a : ℝ) * Real.log ((g a : ℝ) / n) := by
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    field_simp
  rw [hg_sum] at h_sum_each
  linarith

lemma sum_typeCount {n : ℕ} (x : Fin n → α) :
    (∑ a : α, typeCount x a) = n := by
  classical
  unfold typeCount
  have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      x i ∈ (Finset.univ : Finset α) := fun _ _ ↦ Finset.mem_univ _
  have h_fiber := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset α)) h_maps (fun _ : Fin n ↦ (1 : ℕ))
  have h_card : ∀ a : α,
      ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a).card
        = ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a), (1 : ℕ) := by
    intro a; rw [Finset.sum_const, Nat.smul_one_eq_cast]; rfl
  rw [show (∑ a : α, ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a).card)
        = ∑ a : α, ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = a),
            (1 : ℕ)
      from Finset.sum_congr rfl fun a _ ↦ h_card a]
  rw [h_fiber]; simp

lemma conditionalKL_exp_finish
    (n : ℕ) (cardα cardβ ε_X hδc HX HY HZ LX LY LZ ε_amp slack target_lb card_real : ℝ)
    (hε_amp_eq : ε_amp = cardα * ε_X + cardα * cardβ / n)
    (hslack_eq : slack = cardα * ε_X * LY + ε_X * LX + ε_X * LZ + hδc)
    (htarget_lb_eq : target_lb
      = (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * (ε_X * LX + ε_X * LZ + hδc)
        + cardα * cardβ * LY)
    (hn_ne : (n : ℝ) ≠ 0)
    (hcard_exp_ge : Real.exp target_lb ≤ card_real) :
    Real.exp (-(n : ℝ) * (HX + HY - HZ + slack))
      ≤ card_real * Real.exp (-(n : ℝ) * (HY + ε_amp * LY)) := by
  have h_exp_match : target_lb + (-(n : ℝ) * (HY + ε_amp * LY))
      = -(n : ℝ) * (HX + HY - HZ + slack) := by
    rw [htarget_lb_eq, hε_amp_eq, hslack_eq]
    field_simp
    ring
  have h_exp_factor : Real.exp (-(n : ℝ) * (HX + HY - HZ + slack))
      = Real.exp target_lb * Real.exp (-(n : ℝ) * (HY + ε_amp * LY)) := by
    rw [← Real.exp_add, h_exp_match]
  rw [h_exp_factor]
  exact mul_le_mul_of_nonneg_right hcard_exp_ge (Real.exp_nonneg _)

lemma conditionalKL_HZemp_HXemp_lb
    (n : ℕ) (hn_pos : (0 : ℝ) < n) (hn_ne : (n : ℝ) ≠ 0)
    (cardβ ε_X ε_Z HX HZ HXemp HZemp LX LZ KL_val : ℝ)
    (hε_Z_eq : ε_Z = ε_X + cardβ / n)
    (h_HXemp_le : HXemp ≤ HX + ε_X * LX)
    (h_HZemp_ge : HZemp ≥ HZ - ε_Z * LZ - KL_val) :
    (n : ℝ) * (HZemp - HXemp)
      ≥ (n : ℝ) * (HZ - HX) - (n : ℝ) * ε_X * LZ
        - cardβ * LZ - (n : ℝ) * KL_val - (n : ℝ) * ε_X * LX := by
  have h_diff : HZemp - HXemp ≥ (HZ - HX) - ε_Z * LZ - KL_val - ε_X * LX := by
    linarith
  have h_eZ : ε_Z * LZ = ε_X * LZ + cardβ / n * LZ := by
    rw [hε_Z_eq]; ring
  have h_nε_Z_LZ : (n : ℝ) * (ε_Z * LZ) = (n : ℝ) * ε_X * LZ + cardβ * LZ := by
    rw [h_eZ]
    rw [show (n : ℝ) * (ε_X * LZ + cardβ / n * LZ)
          = (n : ℝ) * ε_X * LZ + (n : ℝ) * (cardβ / n * LZ) from by ring]
    congr 1
    rw [show (n : ℝ) * (cardβ / n * LZ)
          = ((n : ℝ) / n) * (cardβ * LZ) from by ring]
    rw [div_self hn_ne, one_mul]
  have h_lin : (n : ℝ) * (HZemp - HXemp)
      ≥ (n : ℝ) * ((HZ - HX) - ε_Z * LZ - KL_val - ε_X * LX) :=
    mul_le_mul_of_nonneg_left h_diff hn_pos.le
  have h_expand : (n : ℝ) * ((HZ - HX) - ε_Z * LZ - KL_val - ε_X * LX)
      = (n : ℝ) * (HZ - HX) - (n : ℝ) * (ε_Z * LZ) - (n : ℝ) * KL_val
        - (n : ℝ) * ε_X * LX := by ring
  linarith [h_nε_Z_LZ]

lemma conditionalKL_nKL_le_three_eighths
    (n : ℕ) (hn_pos : (0 : ℝ) < n) (hn_pos_nat : 0 < n) (hn_ne : (n : ℝ) ≠ 0)
    (cardα cardβ ε_X ε_Z qZ_min hδ KL_val : ℝ)
    (hqZ_min_pos : 0 < qZ_min) (hδ_pos : 0 < hδ)
    (hε_Z_sq_expand : ε_Z ^ 2 = ε_X ^ 2 + 2 * ε_X * (cardβ / n) + (cardβ / n) ^ 2)
    (hδ_dominates_kl : 8 * cardα * cardβ * ε_X ^ 2 ≤ hδ * qZ_min)
    (h_KL_chi : KL_val ≤ cardα * cardβ * ε_Z ^ 2 / qZ_min)
    (h_KL_cross_le : 2 * cardα * cardβ ^ 2 * ε_X / qZ_min ≤ (n : ℝ) * (hδ / 8))
    (h_KL_inv_le : cardα * cardβ ^ 3 / (n * qZ_min) ≤ hδ / 8) :
    (n : ℝ) * KL_val ≤ 3 * (n : ℝ) * hδ / 8 := by
  have h_nKL_lb : (n : ℝ) * KL_val
      ≤ (n : ℝ) * (cardα * cardβ * ε_Z ^ 2 / qZ_min) :=
    mul_le_mul_of_nonneg_left h_KL_chi hn_pos.le
  have h_nKL_expand : (n : ℝ) * (cardα * cardβ * ε_Z ^ 2 / qZ_min)
      = (n : ℝ) * cardα * cardβ * ε_X ^ 2 / qZ_min
        + 2 * cardα * cardβ ^ 2 * ε_X / qZ_min
        + cardα * cardβ ^ 3 / (n * qZ_min) := by
    rw [hε_Z_sq_expand]
    have hqZ_ne : qZ_min ≠ 0 := hqZ_min_pos.ne'
    field_simp
  have h_KL_main : (n : ℝ) * cardα * cardβ * ε_X ^ 2 / qZ_min
      ≤ (n : ℝ) * (hδ / 8) := by
    have h_div : cardα * cardβ * ε_X ^ 2 / qZ_min ≤ hδ / 8 := by
      rw [div_le_div_iff₀ hqZ_min_pos (by linarith : (0 : ℝ) < 8)]
      linarith
    calc (n : ℝ) * cardα * cardβ * ε_X ^ 2 / qZ_min
        = (n : ℝ) * (cardα * cardβ * ε_X ^ 2 / qZ_min) := by ring
      _ ≤ (n : ℝ) * (hδ / 8) := mul_le_mul_of_nonneg_left h_div hn_pos.le
  have h_nKL_total : (n : ℝ) * KL_val ≤ (n : ℝ) * (hδ / 8 + hδ / 8 + hδ / 8) := by
    calc (n : ℝ) * KL_val ≤ _ := h_nKL_lb
      _ = _ := h_nKL_expand
      _ ≤ (n : ℝ) * (hδ / 8) + (n : ℝ) * (hδ / 8)
            + cardα * cardβ ^ 3 / (n * qZ_min) := by
          have := h_KL_main; have := h_KL_cross_le; linarith
      _ ≤ (n : ℝ) * (hδ / 8) + (n : ℝ) * (hδ / 8) + (n : ℝ) * (hδ / 8) := by
          have h_inv_lt : cardα * cardβ ^ 3 / (n * qZ_min)
              ≤ (n : ℝ) * (hδ / 8) := by
            have h := h_KL_inv_le
            have : 1 * (hδ / 8) ≤ (n : ℝ) * (hδ / 8) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hn_pos_nat) (by linarith)
            linarith
          linarith
      _ = (n : ℝ) * (hδ / 8 + hδ / 8 + hδ / 8) := by ring
  have heq : (n : ℝ) * (hδ / 8 + hδ / 8 + hδ / 8) = 3 * (n : ℝ) * hδ / 8 := by ring
  linarith [heq]

lemma conditionalKL_logT_card_le
    {γ : Type*} [Fintype γ] (n : ℕ) (hn_pos : (0 : ℝ) < n)
    (cardα cardβ hδ : ℝ) (hα_pos : 0 < cardα) (hβ_pos : 0 < cardβ)
    (hβ_nn : 0 ≤ cardβ) (T : γ → ℝ)
    (h_logT_sum_le : (∑ a : γ, Real.log (T a + 1)) ≤ cardα * Real.log ((n : ℝ) + 1))
    (h_log : Real.log ((n : ℝ) + 1) / n ≤ hδ / (4 * cardα * cardβ)) :
    cardβ * ∑ a : γ, Real.log (T a + 1) ≤ (n : ℝ) * (hδ / 4) := by
  have h_mul : cardβ * ∑ a : γ, Real.log (T a + 1)
      ≤ cardβ * (cardα * Real.log ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left h_logT_sum_le hβ_nn
  have h_log_mul_n : Real.log ((n : ℝ) + 1)
      ≤ (n : ℝ) * (hδ / (4 * cardα * cardβ)) := by
    rw [div_le_iff₀ hn_pos] at h_log
    linarith
  have h_target_eq : cardα * cardβ
        * ((n : ℝ) * (hδ / (4 * cardα * cardβ)))
      = (n : ℝ) * (hδ / 4) := by
    have hα_ne : cardα ≠ 0 := hα_pos.ne'
    have hβ_ne : cardβ ≠ 0 := hβ_pos.ne'
    field_simp
  have hKey : cardβ * (cardα * Real.log ((n : ℝ) + 1))
      ≤ (n : ℝ) * (hδ / 4) := by
    have h1 : cardα * cardβ * Real.log ((n : ℝ) + 1)
        ≤ cardα * cardβ * ((n : ℝ) * (hδ / (4 * cardα * cardβ))) :=
      mul_le_mul_of_nonneg_left h_log_mul_n (by positivity)
    rw [h_target_eq] at h1
    linarith
  linarith

lemma conditionalKL_final_domination
    {γ : Type*} [Fintype γ] (n : ℕ) (hn_pos : (0 : ℝ) < n)
    (cardα cardβ ε_X HX HZ HXemp HZemp LX LY LZ KL_val hδ target_lb : ℝ)
    (T : γ → ℝ) (hδ_pos : 0 < hδ)
    (htarget_lb_eq : target_lb
      = (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * (ε_X * LX + ε_X * LZ + hδ)
        + cardα * cardβ * LY)
    (h_HZ_HX_lb : (n : ℝ) * (HZemp - HXemp)
      ≥ (n : ℝ) * (HZ - HX) - (n : ℝ) * ε_X * LZ
        - cardβ * LZ - (n : ℝ) * KL_val - (n : ℝ) * ε_X * LX)
    (h_nKL_3_8 : (n : ℝ) * KL_val ≤ 3 * (n : ℝ) * hδ / 8)
    (h_logT_bound : cardβ * ∑ a : γ, Real.log (T a + 1) ≤ (n : ℝ) * (hδ / 4))
    (h_const_bound : cardβ * LZ + cardα * cardβ * LY ≤ (n : ℝ) * (hδ / 4)) :
    target_lb ≤ (n : ℝ) * HZemp - (n : ℝ) * HXemp
      - cardβ * ∑ a : γ, Real.log (T a + 1) := by
  have h_target_expand : target_lb
      = (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LX
        - (n : ℝ) * ε_X * LZ - (n : ℝ) * hδ
        + cardα * cardβ * LY := by
    rw [htarget_lb_eq]; ring
  rw [h_target_expand]
  have key : (n : ℝ) * HZemp - (n : ℝ) * HXemp
      ≥ (n : ℝ) * (HZ - HX) - (n : ℝ) * ε_X * LZ
        - cardβ * LZ - (n : ℝ) * KL_val - (n : ℝ) * ε_X * LX := by linarith
  have h_alt : (n : ℝ) * HZemp - (n : ℝ) * HXemp
        - cardβ * ∑ a : γ, Real.log (T a + 1)
      ≥ (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LZ
        - cardβ * LZ - (n : ℝ) * KL_val - (n : ℝ) * ε_X * LX
        - (n : ℝ) * (hδ / 4) := by linarith
  have h_n_hδ_pos : 0 ≤ (n : ℝ) * (hδ / 8) := by
    have : 0 < (n : ℝ) * (hδ / 8) := mul_pos hn_pos (by linarith)
    exact this.le
  have h_diff_pos : (n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LZ
        - cardβ * LZ - (n : ℝ) * KL_val
        - (n : ℝ) * ε_X * LX - (n : ℝ) * (hδ / 4)
      ≥ ((n : ℝ) * HZ - (n : ℝ) * HX - (n : ℝ) * ε_X * LX
          - (n : ℝ) * ε_X * LZ - (n : ℝ) * hδ
          + cardα * cardβ * LY) := by
    nlinarith [h_const_bound, h_nKL_3_8, h_n_hδ_pos, hn_pos, hδ_pos]
  linarith [h_alt, h_diff_pos]

omit [DecidableEq α] [DecidableEq β] in
lemma qX_eq_sum_qZ
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (a : α) :
    (μ.map (Xs 0)).real {a}
      = ∑ b : β, (μ.map (jointSequence Xs Ys 0)).real {(a, b)} := by
  classical
  set qZ : α × β → ℝ := fun p ↦ (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
  have h_pre : (Prod.fst ⁻¹' ({a} : Set α) : Set (α × β))
      = ⋃ b ∈ (Finset.univ : Finset β), ({(a, b)} : Set (α × β)) := by
    ext ⟨x', y'⟩
    refine ⟨fun hx' ↦ ?_, fun hx' ↦ ?_⟩
    · have : x' = a := hx'; subst this
      refine Set.mem_iUnion.mpr ⟨y', Set.mem_iUnion.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · rcases Set.mem_iUnion.mp hx' with ⟨b', hb'⟩
      rcases Set.mem_iUnion.mp hb' with ⟨_, hb''⟩
      simp only [Set.mem_singleton_iff] at hb''
      simp [Set.mem_preimage, hb'']
  have h_map : ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a}
      = (μ.map (jointSequence Xs Ys 0)).real (Prod.fst ⁻¹' {a}) :=
    map_measureReal_apply measurable_fst (MeasurableSet.singleton a)
  have h_qX_eq : ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a}
      = (μ.map (Xs 0)).real {a} := by rw [hmarg_X]
  have h_disj : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint
      (fun b ↦ ({(a, b)} : Set (α × β))) := by
    intro b₁ _ b₂ _ hb s hs1 hs2 p hp
    have hp1 := hs1 hp; have hp2 := hs2 hp
    simp only [Set.mem_singleton_iff] at hp1 hp2
    have heq : (a, b₁) = (a, b₂) := hp1.symm.trans hp2
    exact (hb (Prod.mk.injEq _ _ _ _ |>.mp heq).2).elim
  have h_meas : ∀ b ∈ (Finset.univ : Finset β),
      MeasurableSet ({(a, b)} : Set (α × β)) := fun _ _ ↦ measurableSet_singleton _
  have h_sum : (μ.map (jointSequence Xs Ys 0)).real (Prod.fst ⁻¹' {a})
      = ∑ b : β, qZ (a, b) := by
    rw [h_pre, measureReal_biUnion_finset h_disj h_meas]
  rw [← h_qX_eq, h_map, h_sum]

lemma conditionalKL_archimedean_log
    (cardα cardβ hδ : ℝ) (hδ_pos : 0 < hδ) (hβ_pos : 0 < cardβ) (hα_pos : 0 < cardα) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.log ((n : ℝ) + 1) / n ≤ hδ / (4 * cardα * cardβ) := by
  have h_target_pos : 0 < hδ / (4 * cardα * cardβ) := by
    apply div_pos hδ_pos
    have : (0 : ℝ) < 4 * cardα := by linarith
    exact mul_pos this hβ_pos
  exact exists_nat_forall_log_succ_div_le h_target_pos

lemma conditionalKL_archimedean_const
    (cardα cardβ LY LZ hδ : ℝ) (hδ_pos : 0 < hδ)
    (hβ_nn : 0 ≤ cardβ) (hαβ_nn : 0 ≤ cardα * cardβ)
    (hLY_nn : 0 ≤ LY) (hLZ_nn : 0 ≤ LZ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cardβ * LZ + cardα * cardβ * LY) / n ≤ hδ / 4 := by
  have hC_nn : 0 ≤ cardβ * LZ + cardα * cardβ * LY := by
    have h1 : 0 ≤ cardβ * LZ := mul_nonneg hβ_nn hLZ_nn
    have h2 : 0 ≤ cardα * cardβ * LY := mul_nonneg hαβ_nn hLY_nn
    linarith
  exact exists_nat_forall_div_le hC_nn (by linarith)

lemma conditionalKL_archimedean_kl_cross
    (cardα cardβ ε_X qZ_min hδ : ℝ) (hδ_pos : 0 < hδ) (hqZ_min_pos : 0 < qZ_min)
    (hε_X : 0 ≤ ε_X) (hα_nn : 0 ≤ cardα) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * cardα * cardβ ^ 2 * ε_X / qZ_min ≤ (n : ℝ) * (hδ / 8) := by
  have hK_nn : 0 ≤ 2 * cardα * cardβ ^ 2 * ε_X / qZ_min := by
    apply div_nonneg _ hqZ_min_pos.le
    apply mul_nonneg _ hε_X
    apply mul_nonneg _ (by positivity)
    linarith
  exact exists_nat_forall_le_nat_mul hK_nn (by linarith)

lemma conditionalKL_archimedean_kl_inv
    (cardα cardβ qZ_min hδ : ℝ) (hδ_pos : 0 < hδ) (hqZ_min_pos : 0 < qZ_min)
    (hα_nn : 0 ≤ cardα) (hβ_nn : 0 ≤ cardβ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cardα * cardβ ^ 3 / (n * qZ_min) ≤ hδ / 8 := by
  have hK_nn : 0 ≤ cardα * cardβ ^ 3 / qZ_min := by
    apply div_nonneg _ hqZ_min_pos.le
    exact mul_nonneg hα_nn (pow_nonneg hβ_nn 3)
  obtain ⟨N, hN⟩ := exists_nat_forall_div_le hK_nn (show (0 : ℝ) < hδ / 8 by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h_eq : cardα * cardβ ^ 3 / (n * qZ_min)
      = cardα * cardβ ^ 3 / qZ_min / n := by
    rw [div_div, mul_comm (n : ℝ) qZ_min]
  rw [h_eq]; exact hN n hn

lemma conditionalKL_HXemp_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {n : ℕ} (hn_pos : (0 : ℝ) < n) (hn_pos_nat : 0 < n) (hn_ne : (n : ℝ) ≠ 0)
    {ε_X : ℝ} (x : Fin n → α) (hx : x ∈ stronglyTypicalSet μ Xs n ε_X)
    (qX : α → ℝ) (hqX_eq : ∀ a, qX a = (μ.map (Xs 0)).real {a})
    (hqX_pos : ∀ a, 0 < qX a) (h_qX_sum_one : (∑ a : α, qX a) = 1)
    (T : α → ℕ) (hT_eq : ∀ a, T a = typeCount x a) (hT_sum : (∑ a : α, T a) = n)
    (HX LX HXemp : ℝ) (hHX_eq : HX = entropy μ (Xs 0)) (hLX_eq : LX = logSumAbs μ Xs)
    (hHXemp_eq : HXemp = -∑ a : α, ((T a : ℝ) / n) * Real.log ((T a : ℝ) / n)) :
    HXemp ≤ HX + ε_X * LX := by
  classical
  have hT_real : ∀ a, (T a : ℝ) = (typeCount x a : ℝ) := fun a ↦ by rw [hT_eq a]
  set crossX : ℝ := -∑ a : α, ((T a : ℝ) / n) * Real.log (qX a) with hcrossX_def
  have h_gibbs_X : HXemp ≤ crossX := by
    rw [hHXemp_eq, hcrossX_def]
    refine neg_sum_mul_log_le_neg_sum_mul_log_of_sum_eq
      (fun a ↦ (T a : ℝ) / n) qX
      (fun a ↦ div_nonneg (Nat.cast_nonneg _) hn_pos.le) hqX_pos ?_
    rw [show (∑ a : α, (T a : ℝ) / n) = (∑ a : α, (T a : ℝ)) / n
          from by rw [Finset.sum_div],
      show (∑ a : α, (T a : ℝ)) = (n : ℝ) from by exact_mod_cast hT_sum,
      div_self hn_ne, h_qX_sum_one]
  have h_cross_X_typ : |crossX - HX| ≤ ε_X * LX := by
    have h_pmfLog_eq : ∀ a, pmfLog μ Xs a = -Real.log (qX a) := by
      intro a; rw [hqX_eq a]; rfl
    have h_cross_eq : (∑ i : Fin n, pmfLog μ Xs (x i)) / n = crossX := by
      set f : α → ℝ := fun a ↦ -Real.log (qX a) with hf_def
      have h_pmf_eq_f : ∀ i, pmfLog μ Xs (x i) = f (x i) := fun i ↦ h_pmfLog_eq (x i)
      have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          x i ∈ (Finset.univ : Finset α) := fun _ _ ↦ Finset.mem_univ _
      have h_fib := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset α)) h_maps f
      have h_agg : (∑ i : Fin n, pmfLog μ Xs (x i)) = ∑ a : α, (T a : ℝ) * f a := by
        rw [Finset.sum_congr rfl fun i _ ↦ h_pmf_eq_f i, ← h_fib]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.sum_const, nsmul_eq_mul, hT_real a]; rfl
      rw [h_agg, Finset.sum_div, hcrossX_def]
      rw [show (∑ a : α, (T a : ℝ) * f a / n)
            = -∑ a : α, ((T a : ℝ) / n) * Real.log (qX a) from ?_]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hf_def]
      have : (T a : ℝ) * (-Real.log (qX a)) / n = -((T a : ℝ) / n * Real.log (qX a)) := by
        ring
      exact this
    have hwk := stronglyTypical_implies_weakly_typical_bound μ Xs hXs hn_pos_nat x hx
    rw [h_cross_eq, ← hHX_eq, ← hLX_eq] at hwk
    exact hwk
  have h_cross_le : crossX ≤ HX + ε_X * LX := by
    have h := abs_sub_le_iff.mp h_cross_X_typ
    linarith [h.1]
  linarith

lemma conditionalKL_KL_chi_bound
    {γ δ : Type*} [Fintype γ] [Fintype δ] (n : ℕ) (hn_pos : (0 : ℝ) < n)
    (hn_ne : (n : ℝ) ≠ 0)
    (c : γ × δ → ℕ) (qZ : γ × δ → ℝ) (ε_Z qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_pos : ∀ p, 0 < qZ p)
    (hc_total : (∑ p : γ × δ, c p) = n)
    (h_qZ_sum_one : (∑ p : γ × δ, qZ p) = 1)
    (hc_close : ∀ p, |((c p : ℕ) : ℝ) / n - qZ p| ≤ ε_Z)
    (hqZ_min_le : ∀ p, qZ_min ≤ qZ p) :
    (∑ p : γ × δ, ((c p : ℕ) : ℝ) / n * Real.log ((((c p : ℕ) : ℝ) / n) / qZ p))
      ≤ (Fintype.card γ : ℝ) * (Fintype.card δ : ℝ) * ε_Z ^ 2 / qZ_min := by
  have h_p_nn : ∀ p ∈ (Finset.univ : Finset (γ × δ)), 0 ≤ ((c p : ℕ) : ℝ) / n :=
    fun p _ ↦ div_nonneg (Nat.cast_nonneg _) hn_pos.le
  have h_q_pos : ∀ p ∈ (Finset.univ : Finset (γ × δ)), 0 < qZ p := fun p _ ↦ hqZ_pos p
  have h_p_sum_eq : (∑ p : γ × δ, ((c p : ℕ) : ℝ) / n) = ∑ p : γ × δ, qZ p := by
    rw [← Finset.sum_div,
      show (∑ p : γ × δ, ((c p : ℕ) : ℝ)) = (n : ℝ) from by exact_mod_cast hc_total,
      div_self hn_ne, h_qZ_sum_one]
  have h_chi := KL_le_chi_square_finset (Finset.univ : Finset (γ × δ))
    (fun p ↦ ((c p : ℕ) : ℝ) / n) qZ h_p_nn h_q_pos h_p_sum_eq
  refine le_trans h_chi ?_
  have h_bound := sum_sq_div_le_card_mul (γ := γ × δ)
    (fun p ↦ ((c p : ℕ) : ℝ) / n - qZ p) qZ ε_Z qZ_min hqZ_min_pos hc_close hqZ_pos
    hqZ_min_le
  refine le_trans h_bound (le_of_eq ?_)
  rw [Fintype.card_prod]; push_cast; ring

lemma conditionalKL_crossZ_typicality
    {γ δ : Type*} [Fintype γ] [Fintype δ] (n : ℕ)
    (c : γ × δ → ℕ) (qZ : γ × δ → ℝ) (ε_Z HZ LZ crossZ : ℝ)
    (hcrossZ_eq : crossZ = -∑ p : γ × δ, ((c p : ℕ) : ℝ) / n * Real.log (qZ p))
    (hHZ_eq : HZ = ∑ p : γ × δ, Real.negMulLog (qZ p))
    (hLZ_eq : LZ = ∑ p : γ × δ, |Real.log (qZ p)|)
    (hc_close : ∀ p, |((c p : ℕ) : ℝ) / n - qZ p| ≤ ε_Z) :
    |crossZ - HZ| ≤ ε_Z * LZ := by
  have h_eq : crossZ - HZ
      = ∑ p : γ × δ, (qZ p - ((c p : ℕ) : ℝ) / n) * Real.log (qZ p) := by
    rw [hHZ_eq, hcrossZ_eq]
    have h_each : ∀ p : γ × δ,
        (qZ p - ((c p : ℕ) : ℝ) / n) * Real.log (qZ p)
          = -(((c p : ℕ) : ℝ) / n * Real.log (qZ p)) - Real.negMulLog (qZ p) := by
      intro p; rw [Real.negMulLog]; ring
    rw [Finset.sum_congr rfl (fun p _ ↦ h_each p)]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have h_neg : ∑ p : γ × δ, (qZ p - ((c p : ℕ) : ℝ) / n) * Real.log (qZ p)
      = -∑ p : γ × δ, (((c p : ℕ) : ℝ) / n - qZ p) * Real.log (qZ p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_; ring
  rw [h_eq, h_neg, abs_neg, hLZ_eq]
  exact sum_diff_log_abs_le_typicality
    (fun p ↦ ((c p : ℕ) : ℝ) / n) qZ ε_Z hc_close

lemma conditionalKL_rowProd_pos
    {γ δ : Type*} [Fintype γ] [Fintype δ] (T : γ → ℕ) (c : γ × δ → ℕ) :
    (0 : ℝ) < ∏ a : γ,
      (((T a : ℝ) + 1) ^ (Fintype.card δ : ℕ))⁻¹
        * ((T a : ℝ) ^ T a / ∏ b : δ, (c (a, b) : ℝ) ^ (c (a, b))) := by
  refine Finset.prod_pos fun a _ ↦ ?_
  have hT1 : (0 : ℝ) < ((T a : ℝ) + 1) ^ (Fintype.card δ : ℕ) := by
    have : (0 : ℝ) < (T a : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (T a : ℝ) := Nat.cast_nonneg _; linarith
    exact pow_pos this _
  have hTp : (0 : ℝ) < ((T a : ℝ)) ^ (T a) := by
    rcases Nat.eq_zero_or_pos (T a) with h | h
    · rw [h, pow_zero]; exact one_pos
    · exact pow_pos (by exact_mod_cast h) _
  have hcp : (0 : ℝ) < ∏ b : δ, (c (a, b) : ℝ) ^ (c (a, b)) :=
    Finset.prod_pos fun b _ ↦ by
      rcases Nat.eq_zero_or_pos (c (a, b)) with h | h
      · rw [h, pow_zero]; exact one_pos
      · exact pow_pos (by exact_mod_cast h) _
  exact mul_pos (inv_pos.mpr hT1) (div_pos hTp hcp)

lemma conditionalKL_log_card_lb
    {γ δ : Type*} [Fintype γ] [Fintype δ] (n : ℕ) (hn_ne : (n : ℝ) ≠ 0)
    (cardβ : ℝ) (hcardβ_eq : cardβ = (Fintype.card δ : ℝ))
    (T : γ → ℕ) (c : γ × δ → ℕ) (card_real HXemp HZemp : ℝ)
    (hHXemp_eq :
      HXemp = -∑ a : γ, ((T a : ℝ) / n) * Real.log ((T a : ℝ) / n))
    (hHZemp_eq :
      HZemp = -∑ p : γ × δ, ((c p : ℕ) : ℝ) / n * Real.log (((c p : ℕ) : ℝ) / n))
    (hT_sum : (∑ a : γ, T a) = n) (hc_total : (∑ p : γ × δ, c p) = n)
    (h_card_ge_prod :
      (∏ a : γ,
        (((T a : ℝ) + 1) ^ (Fintype.card δ : ℕ))⁻¹
          * ((T a : ℝ) ^ T a / ∏ b : δ, (c (a, b) : ℝ) ^ (c (a, b)))) ≤ card_real) :
    (n : ℝ) * HZemp - (n : ℝ) * HXemp
        - cardβ * ∑ a : γ, Real.log ((T a : ℝ) + 1)
      ≤ Real.log card_real := by
  classical
  subst hcardβ_eq
  have hT_plus_one_pos : ∀ a, (0 : ℝ) < (T a : ℝ) + 1 := by
    intro a; have : (0 : ℝ) ≤ (T a : ℝ) := Nat.cast_nonneg _; linarith
  have hT_plus_one_pow_pos : ∀ a, (0 : ℝ) < ((T a : ℝ) + 1) ^ (Fintype.card δ : ℕ) :=
    fun a ↦ pow_pos (hT_plus_one_pos a) _
  have hT_pow_pos : ∀ a, (0 : ℝ) < ((T a : ℝ)) ^ (T a) := by
    intro a
    rcases Nat.eq_zero_or_pos (T a) with h | h
    · rw [h, pow_zero]; exact one_pos
    · exact pow_pos (by exact_mod_cast h) _
  have hT_pow_ne : ∀ a, ((T a : ℝ)) ^ (T a) ≠ 0 := fun a ↦ (hT_pow_pos a).ne'
  have hc_pow_pos : ∀ a b, (0 : ℝ) < (c (a, b) : ℝ) ^ (c (a, b)) := by
    intro a b
    rcases Nat.eq_zero_or_pos (c (a, b)) with h | h
    · rw [h, pow_zero]; exact one_pos
    · exact pow_pos (by exact_mod_cast h) _
  have hc_pow_prod_pos : ∀ a, (0 : ℝ) < ∏ b : δ, (c (a, b) : ℝ) ^ (c (a, b)) :=
    fun a ↦ Finset.prod_pos fun b _ ↦ hc_pow_pos a b
  have hc_pow_prod_ne : ∀ a, (∏ b : δ, (c (a, b) : ℝ) ^ (c (a, b))) ≠ 0 :=
    fun a ↦ (hc_pow_prod_pos a).ne'
  set rowFactor : γ → ℝ := fun a ↦
    (((T a : ℝ) + 1) ^ (Fintype.card δ : ℕ))⁻¹
      * ((T a : ℝ) ^ T a / ∏ b : δ, (c (a, b) : ℝ) ^ (c (a, b))) with hrowFactor_def
  have hrowFactor_pos : ∀ a, 0 < rowFactor a := fun a ↦
    mul_pos (inv_pos.mpr (hT_plus_one_pow_pos a))
      (div_pos (hT_pow_pos a) (hc_pow_prod_pos a))
  have hrowProd_pos : 0 < ∏ a : γ, rowFactor a := Finset.prod_pos fun a _ ↦ hrowFactor_pos a
  have h_log_each : ∀ a, Real.log (rowFactor a)
      = -(Fintype.card δ : ℝ) * Real.log ((T a : ℝ) + 1)
        + (T a : ℝ) * Real.log (T a : ℝ)
        - ∑ b : δ, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ) := by
    intro a
    rw [hrowFactor_def,
      Real.log_mul (inv_ne_zero (hT_plus_one_pow_pos a).ne')
        (div_ne_zero (hT_pow_ne a) (hc_pow_prod_ne a)),
      Real.log_inv, Real.log_pow,
      Real.log_div (hT_pow_ne a) (hc_pow_prod_ne a),
      Real.log_pow]
    have h_prod_log : Real.log (∏ b : δ, (c (a, b) : ℝ) ^ (c (a, b)))
        = ∑ b : δ, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ) := by
      rw [Real.log_prod (fun b _ ↦ (hc_pow_pos a b).ne')]
      exact Finset.sum_congr rfl fun b _ ↦ Real.log_pow _ _
    rw [h_prod_log]
    ring
  have h_log_prod : Real.log (∏ a : γ, rowFactor a) = ∑ a : γ, Real.log (rowFactor a) :=
    Real.log_prod (fun a _ ↦ (hrowFactor_pos a).ne')
  have h_chain :
      (∑ a : γ, (T a : ℝ) * Real.log (T a : ℝ))
        - ∑ a : γ, ∑ b : δ, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ)
        = (n : ℝ) * HZemp - (n : ℝ) * HXemp := by
    have hT_R_sum : (∑ a : γ, (T a : ℝ)) = (n : ℝ) := by exact_mod_cast hT_sum
    have h_X : (∑ a : γ, (T a : ℝ) * Real.log (T a : ℝ))
        = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) * HXemp := by
      rw [hHXemp_eq]
      exact sum_natCast_mul_log_eq T hn_ne hT_R_sum
    have hc_R_sum : (∑ p : γ × δ, ((c p : ℕ) : ℝ)) = (n : ℝ) := by
      exact_mod_cast hc_total
    have h_Z : (∑ a : γ, ∑ b : δ, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ))
        = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) * HZemp := by
      have h_swap : (∑ a : γ, ∑ b : δ, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ))
          = ∑ p : γ × δ, ((c p : ℕ) : ℝ) * Real.log ((c p : ℕ) : ℝ) := by
        rw [← Finset.sum_product']; rfl
      rw [h_swap, hHZemp_eq]
      exact sum_natCast_mul_log_eq c hn_ne hc_R_sum
    linarith
  have h1 : Real.log (∏ a : γ, rowFactor a) ≤ Real.log card_real := by
    apply Real.log_le_log hrowProd_pos h_card_ge_prod
  refine le_trans ?_ h1
  rw [h_log_prod, Finset.sum_congr rfl (fun a _ ↦ h_log_each a)]
  have h_split :
      (∑ a : γ,
        (-(Fintype.card δ : ℝ) * Real.log ((T a : ℝ) + 1)
          + (T a : ℝ) * Real.log (T a : ℝ)
          - ∑ b : δ, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ)))
      = -(Fintype.card δ : ℝ) * ∑ a : γ, Real.log ((T a : ℝ) + 1)
        + ((∑ a : γ, (T a : ℝ) * Real.log (T a : ℝ))
            - ∑ a : γ, ∑ b : δ, (c (a, b) : ℝ) * Real.log (c (a, b) : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [show (∑ a : γ, -(Fintype.card δ : ℝ) * Real.log ((T a : ℝ) + 1))
          = -(Fintype.card δ : ℝ) * ∑ a : γ, Real.log ((T a : ℝ) + 1) from by
      rw [← Finset.mul_sum]]
    ring
  rw [h_split, h_chain]; linarith

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
              (fun p ↦ floorMatrix
                (fun p' ↦ (μ.map (jointSequence Xs Ys 0)).real {p'}) x p.1 p.2))).card : ℝ)
          * Real.exp (-(n : ℝ) *
                (entropy μ (Ys 0)
                  + ((Fintype.card α : ℝ) * ε_X
                      + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / n)
                    * logSumAbs μ Ys)) := by
  classical
  -- ── Abbreviations and bookkeeping. ──
  set qZ : α × β → ℝ := fun p ↦ (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
  set qX : α → ℝ := fun a ↦ (μ.map (Xs 0)).real {a} with hqX_def
  set HX : ℝ := entropy μ (Xs 0) with hHX_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set HZ : ℝ := entropy μ (jointSequence Xs Ys 0) with hHZ_def
  set LX : ℝ := logSumAbs μ Xs with hLX_def
  set LY : ℝ := logSumAbs μ Ys with hLY_def
  set LZ : ℝ := logSumAbs μ (jointSequence Xs Ys) with hLZ_def
  have hLY_nn : 0 ≤ LY := logSumAbs_nonneg μ Ys
  have hLZ_nn : 0 ≤ LZ := logSumAbs_nonneg μ (jointSequence Xs Ys)
  have hα_pos : (0 : ℝ) < Fintype.card α := by exact_mod_cast (Fintype.card_pos (α := α))
  have hβ_pos : (0 : ℝ) < Fintype.card β := by exact_mod_cast (Fintype.card_pos (α := β))
  have hα_nn : (0 : ℝ) ≤ Fintype.card α := hα_pos.le
  have hβ_nn : (0 : ℝ) ≤ Fintype.card β := hβ_pos.le
  have hαβ_nn : 0 ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := (mul_pos hα_pos hβ_pos).le
  -- Inherit probability measures on the pushforwards (instances for `sum_…_eq_one`).
  have hZ_meas : Measurable (jointSequence Xs Ys 0) := measurable_jointSequence Xs Ys hXs hYs 0
  have hZ_prob : IsProbabilityMeasure (μ.map (jointSequence Xs Ys 0)) :=
    Measure.isProbabilityMeasure_map hZ_meas.aemeasurable
  have hX_prob : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  -- qZ positivity.
  have hqZ_pos : ∀ p, 0 < qZ p := hposZ
  have hqZ_nn : ∀ p, 0 ≤ qZ p := fun p ↦ (hqZ_pos p).le
  -- qZ marginalizes to a probability measure on α (resp. β).
  -- ∑ p, qZ p = 1.
  have h_qZ_sum_one : (∑ p : α × β, qZ p) = 1 := by
    rw [hqZ_def]; exact sum_measureReal_singleton_eq_one (μ.map (jointSequence Xs Ys 0))
  -- ∑ a, qX a = 1.
  have h_qX_sum_one : (∑ a : α, qX a) = 1 := by
    rw [hqX_def]; exact sum_measureReal_singleton_eq_one (μ.map (Xs 0))
  -- qX a > 0 from qZ-marginal: qX a = ∑_b qZ(a, b), each term > 0.
  have hqX_pos : ∀ a : α, 0 < qX a := by
    intro a
    have h_qXa_eq : qX a = ∑ b : β, qZ (a, b) :=
      qX_eq_sum_qZ μ Xs Ys hmarg_X a
    rw [h_qXa_eq]
    exact Finset.sum_pos (fun b _ ↦ hqZ_pos (a, b)) Finset.univ_nonempty
  -- ── Archimedean choice of N. ──
  obtain ⟨N_log, hN_log⟩ := conditionalKL_archimedean_log
    (Fintype.card α : ℝ) (Fintype.card β : ℝ) hδ hδ_pos hβ_pos hα_pos
  obtain ⟨N_const, hN_const⟩ := conditionalKL_archimedean_const
    (Fintype.card α : ℝ) (Fintype.card β : ℝ) LY LZ hδ hδ_pos hβ_nn hαβ_nn hLY_nn hLZ_nn
  obtain ⟨N_KL_cross, hN_KL_cross⟩ := conditionalKL_archimedean_kl_cross
    (Fintype.card α : ℝ) (Fintype.card β : ℝ) ε_X qZ_min hδ hδ_pos hqZ_min_pos hε_X hα_nn
  obtain ⟨N_KL_inv, hN_KL_inv⟩ := conditionalKL_archimedean_kl_inv
    (Fintype.card α : ℝ) (Fintype.card β : ℝ) qZ_min hδ hδ_pos hqZ_min_pos hα_nn hβ_nn
  -- Take the max of all four (and 1 to keep n ≥ 1).
  refine ⟨max (max (max N_log N_const) (max N_KL_cross N_KL_inv)) 1,
    fun n hn_ge x hx ↦ ?_⟩
  have hn_pos_nat : 0 < n := by
    have : 1 ≤ n := le_of_max_le_right hn_ge; omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hn_pair1 : max N_log N_const ≤ n := le_of_max_le_left (le_of_max_le_left hn_ge)
  have hn_pair2 : max N_KL_cross N_KL_inv ≤ n := le_of_max_le_right (le_of_max_le_left hn_ge)
  have hn_N_log : N_log ≤ n := le_of_max_le_left hn_pair1
  have hn_N_const : N_const ≤ n := le_of_max_le_right hn_pair1
  have hn_N_KL_cross : N_KL_cross ≤ n := le_of_max_le_left hn_pair2
  have hn_N_KL_inv : N_KL_inv ≤ n := le_of_max_le_right hn_pair2
  -- Set c := floorMatrix qZ x · (joint count vector).
  set c : α × β → ℕ := fun p ↦ floorMatrix qZ x p.1 p.2 with hc_def
  set T : α → ℕ := fun a ↦ typeCount x a with hT_def
  have hc_row : ∀ a, (∑ b : β, c (a, b)) = T a :=
    fun a ↦ floorMatrix_row_sum qZ hqZ_nn x a
  have hc_total : (∑ p : α × β, c p) = n := floorMatrix_total qZ hqZ_nn x
  have hT_le_n : ∀ a, T a ≤ n := by
    intro a
    have h1 : (Finset.univ.filter (fun i : Fin n ↦ x i = a)).card ≤
        (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  have hT_sum : (∑ a : α, T a) = n := sum_typeCount x
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
  have h_card_ge_prod :
      (∏ a : α,
        (((T a : ℝ) + 1) ^ (Fintype.card β : ℕ))⁻¹
          * ((T a : ℝ) ^ T a / ∏ b : β, (c (a, b) : ℝ) ^ (c (a, b)))) ≤ card_real :=
    conditionalTypeClass_card_ge (β := β) x c hc_row
  have hrowProd_pos : (0 : ℝ) < ∏ a : α,
      (((T a : ℝ) + 1) ^ (Fintype.card β : ℕ))⁻¹
        * ((T a : ℝ) ^ T a / ∏ b : β, (c (a, b) : ℝ) ^ (c (a, b))) :=
    conditionalKL_rowProd_pos (δ := β) T c
  -- ── Step (II): Chain-rule shape S := ∑_a T_a log T_a - ∑_{ab} c log c
  --     = n · (HZemp - HXemp). ──
  set HXemp : ℝ := -∑ a : α, ((T a : ℝ) / n) * Real.log ((T a : ℝ) / n) with hHXemp_def
  set HZemp : ℝ := -∑ p : α × β, ((c p : ℕ) : ℝ) / n * Real.log (((c p : ℕ) : ℝ) / n)
    with hHZemp_def
  -- Assemble log card lower bound (Step I delegated to `conditionalKL_log_card_lb`).
  have h_log_card_lb : (n : ℝ) * HZemp - (n : ℝ) * HXemp
        - (Fintype.card β : ℝ) * ∑ a : α, Real.log ((T a : ℝ) + 1)
      ≤ Real.log card_real :=
    conditionalKL_log_card_lb (γ := α) (δ := β) n hn_ne (Fintype.card β : ℝ) rfl
      T c card_real HXemp HZemp hHXemp_def hHZemp_def hT_sum hc_total h_card_ge_prod
  -- ── Step (II'): bound ∑_a log(T_a + 1) ≤ |α| · log(n + 1). ──
  have h_logT_sum_le : (∑ a : α, Real.log ((T a : ℝ) + 1))
      ≤ (Fintype.card α : ℝ) * Real.log ((n : ℝ) + 1) :=
    sum_log_natCast_succ_le T n hT_le_n
  -- ── Step (III): Gibbs+typicality on X: HXemp ≤ HX + ε_X · LX. ──
  -- Delegated to `conditionalKL_HXemp_le`.
  have h_HXemp_le : HXemp ≤ HX + ε_X * LX :=
    conditionalKL_HXemp_le μ Xs hXs hn_pos hn_pos_nat hn_ne x hx qX
      (fun a ↦ by rw [hqX_def]) hqX_pos h_qX_sum_one T (fun a ↦ by rw [hT_def]) hT_sum
      HX LX HXemp hHX_def hLX_def hHXemp_def
  -- ── Step (IV): typicality+KL on Z: HZemp ≥ HZ - ε_Z·LZ - KL(c/n‖qZ). ──
  set crossZ : ℝ := -∑ p : α × β, ((c p : ℕ) : ℝ) / n * Real.log (qZ p) with hcrossZ_def
  have h_HZ_unfold : HZ = ∑ p : α × β, Real.negMulLog (qZ p) := by
    show entropy μ (jointSequence Xs Ys 0) = ∑ p : α × β, Real.negMulLog (qZ p)
    unfold entropy; rfl
  have hLZ_eq : LZ = ∑ p : α × β, |Real.log (qZ p)| := by
    show logSumAbs μ (jointSequence Xs Ys) = ∑ p : α × β, |Real.log (qZ p)|
    rfl
  have h_cross_Z_typ : |crossZ - HZ| ≤ ε_Z * LZ :=
    conditionalKL_crossZ_typicality (γ := α) (δ := β) n c qZ ε_Z HZ LZ crossZ
      hcrossZ_def h_HZ_unfold hLZ_eq hc_close
  -- KL upper bound (χ²-style).
  set KL_val : ℝ :=
    ∑ p : α × β, ((c p : ℕ) : ℝ) / n * Real.log ((((c p : ℕ) : ℝ) / n) / qZ p)
    with hKL_val_def
  have h_KL_chi : KL_val ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_Z^2 / qZ_min :=
    conditionalKL_KL_chi_bound (γ := α) (δ := β) n hn_pos hn_ne c qZ ε_Z qZ_min
      hqZ_min_pos hqZ_pos hc_total h_qZ_sum_one hc_close hqZ_min_le
  -- HZemp = crossZ - KL_val.
  -- Pointwise: (c/n) · log(c/n) = (c/n) · log(qZ) + (c/n) · log((c/n)/qZ) (for c/n > 0).
  -- For c = 0, both sides are 0.
  have h_HZemp_eq : HZemp = crossZ - KL_val := by
    rw [hHZemp_def, hcrossZ_def, hKL_val_def]
    exact neg_sum_mul_log_eq_neg_sum_mul_log_sub_sum_mul_log_div
      (fun p ↦ ((c p : ℕ) : ℝ) / n) qZ
      (fun p ↦ div_nonneg (Nat.cast_nonneg _) hn_pos.le) hqZ_pos
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
    -- Step (V) assembly is delegated to the four pure-arithmetic helpers below.
    have h_HZ_HX_lb := conditionalKL_HZemp_HXemp_lb n hn_pos hn_ne
      (Fintype.card β : ℝ) ε_X ε_Z HX HZ HXemp HZemp LX LZ KL_val hε_Z_def
      h_HXemp_le h_HZemp_ge
    have h_nKL_3_8 := conditionalKL_nKL_le_three_eighths n hn_pos hn_pos_nat hn_ne
      (Fintype.card α : ℝ) (Fintype.card β : ℝ) ε_X ε_Z qZ_min hδ KL_val
      hqZ_min_pos hδ_pos hε_Z_sq_expand hδ_dominates_kl h_KL_chi
      (hN_KL_cross n hn_N_KL_cross) (hN_KL_inv n hn_N_KL_inv)
    have h_logT_bound := conditionalKL_logT_card_le (γ := α) n hn_pos
      (Fintype.card α : ℝ) (Fintype.card β : ℝ) hδ hα_pos hβ_pos hβ_nn
      (fun a ↦ (T a : ℝ)) h_logT_sum_le (hN_log n hn_N_log)
    have h_const_bound : (Fintype.card β : ℝ) * LZ
          + (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * LY ≤ (n : ℝ) * (hδ / 4) := by
      have h := hN_const n hn_N_const
      rw [div_le_iff₀ hn_pos] at h
      linarith
    have hgoal := conditionalKL_final_domination (γ := α) n hn_pos
      (Fintype.card α : ℝ) (Fintype.card β : ℝ) ε_X HX HZ HXemp HZemp LX LY LZ KL_val hδ
      target_lb (fun a ↦ (T a : ℝ)) hδ_pos htarget_lb_def h_HZ_HX_lb h_nKL_3_8
      h_logT_bound h_const_bound
    exact le_trans hgoal h_log_card_lb
  -- ── Step (VI): exponentiate and finish. ──
  -- card_real ≥ exp(target_lb) (via Real.exp_log + Real.log_le_log).
  have hcard_pos : 0 < card_real := lt_of_lt_of_le hrowProd_pos h_card_ge_prod
  have hcard_exp_ge : Real.exp target_lb ≤ card_real := by
    rw [← Real.exp_log hcard_pos]
    exact Real.exp_le_exp.mpr h_log_card_target
  -- Final: LHS = exp(-n·(HX+HY-HZ+slack)) ≤ card · exp(-n·(HY + ε_amp·LY)).
  show Real.exp (-(n : ℝ) * (HX + HY - HZ + slack))
        ≤ card_real * Real.exp (-(n : ℝ) * (HY + ε_amp * LY))
  exact conditionalKL_exp_finish n (Fintype.card α : ℝ) (Fintype.card β : ℝ) ε_X hδ
    HX HY HZ LX LY LZ ε_amp slack target_lb card_real hε_amp_def hslack_def htarget_lb_def
    hn_ne hcard_exp_ge

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
    (hindep_Z_pair : Pairwise fun i j ↦
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
        ≤ (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real
              (conditionalStronglyTypicalSlice μ Xs Ys n ε x) := by
  classical
  set qZ : α × β → ℝ := fun p ↦ (μ.map (jointSequence Xs Ys 0)).real {p} with hqZ_def
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
      refine ⟨max N 1, fun n hn ↦ ?_⟩
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have hN_le : N ≤ n := le_of_max_le_left hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hN_lt : (Fintype.card β : ℝ) / (ε - ε_X) < (n : ℝ) :=
        lt_of_lt_of_le hN (by exact_mod_cast hN_le)
      rw [div_lt_iff₀ h_diff_pos] at hN_lt
      linarith
    obtain ⟨N, hN⟩ := h_archimedean
    refine ⟨max N 1, fun n hn ↦ ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hN_le : N ≤ n := le_of_max_le_left hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_le_iff₀ hn_pos]
    have := hN n hN_le
    linarith
  refine ⟨max (max N_KL N_slice) 1, fun n hn_ge x hx ↦ ?_⟩
  have hn_pos : 0 < n := by
    have : 1 ≤ n := le_of_max_le_right hn_ge
    omega
  have hn_N_KL : N_KL ≤ n := le_of_max_le_left (le_of_max_le_left hn_ge)
  have hn_N_slice : N_slice ≤ n := le_of_max_le_right (le_of_max_le_left hn_ge)
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  -- Set c_floor := floorMatrix qZ x.
  set c_floor : α × β → ℕ := fun p ↦ floorMatrix qZ x p.1 p.2 with hc_floor_def
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
      floorMatrix_row_sum qZ (fun p' ↦ (hposZ p').le) x a
    have h_single : floorMatrix qZ x a b ≤ ∑ b' : β, floorMatrix qZ x a b' :=
      Finset.single_le_sum (f := fun b' ↦ floorMatrix qZ x a b')
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ b)
    have h_T_le : typeCount x a ≤ n := by
      unfold typeCount
      have h1 : (Finset.univ.filter (fun i : Fin n ↦ x i = a)).card ≤
          (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      rw [Finset.card_univ, Fintype.card_fin] at h1
      exact h1
    calc c_floor (a, b) = floorMatrix qZ x a b := rfl
      _ ≤ ∑ b' : β, floorMatrix qZ x a b' := h_single
      _ = typeCount x a := h_row_sum
      _ ≤ n := h_T_le
  -- Lift c_floor to TypeCountIndex (= α × β → Fin (n+1)).
  let c_idx : TypeCountIndex (α × β) n := fun p ↦ ⟨c_floor p, by
    have := h_c_le p; omega⟩
  have h_c_idx_eq : ∀ p, (c_idx p : ℕ) = c_floor p := fun _ ↦ rfl
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
    -- y ∈ Cset = conditionalTypeClass x c_floor;
    -- want ∈ ⋃ c ∈ slice, conditionalTypeClass x (c : ℕ).
    -- Note: c_idx : TypeCountIndex (α × β) n; (fun p => (c_idx p : ℕ)) = c_floor by defeq.
    have h_idx_unfold : (fun p ↦ ((c_idx p : Fin (n + 1)) : ℕ)) = c_floor := by
      funext p; rfl
    refine Set.mem_iUnion.mpr ⟨c_idx, Set.mem_iUnion.mpr ⟨h_floor_in_slice, ?_⟩⟩
    rw [h_idx_unfold]
    exact hy
  have h_mass_mono :
      (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real Cset
        ≤ (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real
            (conditionalStronglyTypicalSlice μ Xs Ys n ε x) :=
    measureReal_mono (μ := Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))) h_subset
  -- Step 3: Cset is finite, mass(Cset) = ∑_{y ∈ Cset.toFinset} (μ_Y^n).real {y}.
  have h_Cset_fin : Cset.Finite := conditionalTypeClass_finite x c_floor
  set Cfin : Finset (Fin n → β) := h_Cset_fin.toFinset with hCfin_def
  have h_mass_sum :
      (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real Cset
        = ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real {y} := by
    have h_coe : (Cfin : Set (Fin n → β)) = Cset := h_Cset_fin.coe_toFinset
    rw [← h_coe, ← sum_measureReal_singleton
      (μ := Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))) Cfin]
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
        ≤ (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real {y} := by
    intro y hy
    have hy_set : y ∈ Cset := h_Cset_fin.mem_toFinset.mp hy
    exact productMass_columnProd_ge μ Xs Ys hposY hmarg_Y hn_pos hε_amp_nn
      c_floor h_floor_close_for_perY x hy_set
  -- Step 5: Sum the per-y bounds, get card × exp(-n(HY + ε_amp · LY)) ≤ ∑ y ∈ Cfin, mass {y}.
  have h_card_mass :
      (Cfin.card : ℝ) *
          Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys))
        ≤ ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real {y} := by
    calc (Cfin.card : ℝ) *
            Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys))
        = ∑ _y ∈ Cfin,
            Real.exp (-(n : ℝ) * (entropy μ (Ys 0) + ε_amp * logSumAbs μ Ys)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real {y} :=
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
  -- Now combine: target ≤ card · exp(-n(HY + ε_amp · LY)) ≤ ∑ y ∈ Cfin, ...
  --   = mass(Cset) ≤ mass(slice).
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
    _ ≤ ∑ y ∈ Cfin, (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real {y} :=
        h_card_mass
    _ = (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real Cset := h_mass_sum.symm
    _ ≤ (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real
            (conditionalStronglyTypicalSlice μ Xs Ys n ε x) := h_mass_mono

end InformationTheory.Shannon
