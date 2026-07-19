import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass.Concentration

/-!
# Conditional method of types — slice mass lower bound

The headline conditional slice-mass lower bound
`conditionalStronglyTypicalSlice_mass_ge` (Cover-Thomas 10.6.1, strong form),
assembled from the entropy-concentration helpers in `Mass.Concentration`.
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
/-- Conditional slice mass lower bound (Cover-Thomas 10.6.1, strong form,
mutual-information form). For `x` X-strongly-typical and `Y ∼ μ.map (Ys 0)^n`
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
    -- Note: c_idx : TypeCountIndex (α × β) n; (fun p ↦ (c_idx p : ℕ)) = c_floor by defeq.
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
