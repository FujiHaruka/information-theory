import InformationTheory.Shannon.Stein.Converse

/-!
# Stein's lemma: the optimal type-II exponent

The achievability and converse bounds are assembled onto the optimal type-II error
`steinOptimalBeta P Q n ε`. The two bounds do not coincide: the converse carries a `1/(1−ε)`
factor, so the rate `-(1/n) log (steinOptimalBeta P Q n ε)` is sandwiched between
`(klDiv P Q).toReal − δ` from below and `(klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε))` from
above. Letting `ε → 0⁺` collapses the upper bound back to `(klDiv P Q).toReal`.

## Main definitions

* `steinBetaSet P Q n ε` — the type-II error probabilities attainable by `ε`-level tests.
* `steinOptimalBeta P Q n ε` — the infimum of `steinBetaSet`, the optimal type-II error.

## Main statements

* `steinOptimalBeta_log_le_of_converse` and `steinOptimalBeta_log_ge_of_achievability` — the
  converse and achievability bounds expressed on `steinOptimalBeta`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### The optimal type-II exponent

The achievability and converse bounds are lifted onto the optimal type-II error
`steinOptimalBeta P Q n ε`. The two bounds do not coincide: the converse carries a `1/(1−ε)`
factor, so the rate `-(1/n) log (steinOptimalBeta P Q n ε)` is sandwiched between
`(klDiv P Q).toReal − δ` from below and `(klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε))` from
above. Letting `ε → 0⁺` collapses the upper bound back to `(klDiv P Q).toReal`. -/

/-- The set of type-II error probabilities attainable by `ε`-level tests. -/
noncomputable def steinBetaSet
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set ℝ :=
  { β : ℝ | ∃ (s : Set (Fin n → α)), MeasurableSet s ∧
        ((Measure.pi (fun _ : Fin n ↦ P)) sᶜ).toReal ≤ ε ∧
        β = ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal }

/-- The optimal type-II error subject to type-I ≤ ε. -/
@[entry_point]
noncomputable def steinOptimalBeta
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : ℝ :=
  sInf (steinBetaSet P Q n ε)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `s := Set.univ` is always an α-level test (its complement has measure 0). -/
lemma one_mem_steinBetaSet
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (1 : ℝ) ∈ steinBetaSet P Q n ε := by
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · rw [Set.compl_univ]
    simp only [measure_empty, ENNReal.toReal_zero]
    exact hε
  · show 1 = ((Measure.pi (fun _ : Fin n ↦ Q)) Set.univ).toReal
    rw [show ((Measure.pi (fun _ : Fin n ↦ Q)) Set.univ).toReal
      = (Measure.pi (fun _ : Fin n ↦ Q)).real Set.univ from rfl, probReal_univ]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma steinBetaSet_nonempty
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (steinBetaSet P Q n ε).Nonempty :=
  ⟨1, one_mem_steinBetaSet P Q n ε hε⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma steinBetaSet_bddBelow
    (P Q : Measure α) (n : ℕ) (ε : ℝ) :
    BddBelow (steinBetaSet P Q n ε) := by
  refine ⟨0, ?_⟩
  rintro β ⟨s, _, _, rfl⟩
  exact ENNReal.toReal_nonneg

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
@[entry_point]
lemma steinOptimalBeta_nonneg
    (P Q : Measure α) (n : ℕ) (ε : ℝ) :
    0 ≤ steinOptimalBeta P Q n ε := by
  by_cases h : (steinBetaSet P Q n ε).Nonempty
  · exact le_csInf h fun _ ⟨_, _, _, hβ⟩ ↦ hβ ▸ ENNReal.toReal_nonneg
  · simp [steinOptimalBeta, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
@[entry_point]
lemma steinOptimalBeta_le_one
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    steinOptimalBeta P Q n ε ≤ 1 :=
  csInf_le (steinBetaSet_bddBelow P Q n ε) (one_mem_steinBetaSet P Q n ε hε)

omit [DecidableEq α] [Nonempty α] in
/-- Exponential form of the converse: for any `ε`-level test `s`,
`exp(-n · ((klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε)))) ≤ Qⁿ s`. -/
lemma exp_le_Qn_of_alpha_level
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n)
    (s : Set (Fin n → α)) (hs : MeasurableSet s)
    (hα : ((Measure.pi (fun _ : Fin n ↦ P)) sᶜ).toReal ≤ ε) :
    Real.exp (-((n : ℝ) * ((klDiv P Q).toReal / (1 - ε)
        + Real.log 2 / ((n : ℝ) * (1 - ε)))))
      ≤ ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal := by
  -- Q^n s > 0: reproduce the argument from stein_converse_finite_n.
  set Qn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ Q)
  set Pn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ P)
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_one_sub_eps_pos : (0 : ℝ) < 1 - ε := by linarith
  -- P^n s ≥ 1 - ε > 0, hence s nonempty, hence Q^n s ≥ Q^n {x_witness} > 0.
  have h_Pn_total : Pn.real s + Pn.real sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hs]
    exact probReal_univ
  have h_Pn_sc_eq : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
  have h_Pn_s_pos : 0 < Pn.real s := by rw [h_Pn_sc_eq] at h_Pn_total; linarith
  have h_s_nonempty : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h_empty
    rw [h_empty] at h_Pn_s_pos; simp at h_Pn_s_pos
  obtain ⟨x_w, hx_in_s⟩ := h_s_nonempty
  have h_Qn_x_pos : 0 < Qn.real {x_w} := by
    show 0 < ((Measure.pi (fun _ : Fin n ↦ Q)) {x_w}).toReal
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ ↦ hQpos (x_w i))
  have h_Qn_s_pos : 0 < Qn.real s := by
    have h_subset : ({x_w} : Set (Fin n → α)) ⊆ s := by
      intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hx_in_s
    have := MeasureTheory.measureReal_mono (μ := Qn) h_subset
    linarith
  have h_Qn_s_real_pos : 0 < ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal := h_Qn_s_pos
  -- Apply stein_converse_finite_n.
  have h_conv := stein_converse_finite_n P Q hPpos hPQ hQpos hε hε1 hn s hs hα
  -- h_conv : -(1/n) * log Q^n s ≤ K/(1-ε) + log 2/(n(1-ε))
  -- Multiply both sides by -n: log Q^n s ≥ -n * (K/(1-ε) + log 2/(n(1-ε)))
  set B : ℝ := (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))
  have h_log_ge : Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal ≥ -((n : ℝ) * B) := by
    have h_neg_inv_lt : -((1 : ℝ) / n) < 0 := by
      have : (0 : ℝ) < 1 / n := one_div_pos.mpr hn_R_pos
      linarith
    -- From -(1/n) * x ≤ B and -(1/n) < 0, we get x ≥ -nB.
    -- More directly: -(1/n) * x ≤ B ⟺ x * (-(1/n)) ≤ B ⟺ x ≥ B / (-(1/n)) = -nB.
    have h_eq : -((n : ℝ) * B) = -n * B := by ring
    -- Multiply h_conv by -n (negative) flips: log Q^n s ≥ -n * B.
    -- Concretely: log Q^n s = (-n) * (-(1/n) * log Q^n s) and -(1/n) log Q^n s ≤ B.
    have h_step : (-(n : ℝ)) *
          (-((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal)
        ≥ (-(n : ℝ)) * B := by
      apply mul_le_mul_of_nonpos_left h_conv
      linarith
    have h_simp : (-(n : ℝ)) *
          (-((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal)
        = Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal := by
      field_simp
    rw [h_simp] at h_step
    linarith
  -- exp_le_exp + Real.exp_log h_Qn_s_real_pos:
  have h_exp_chain :
      Real.exp (-((n : ℝ) * B))
        ≤ Real.exp (Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal) :=
    Real.exp_le_exp.mpr h_log_ge
  rw [Real.exp_log h_Qn_s_real_pos] at h_exp_chain
  exact h_exp_chain

omit [DecidableEq α] [Nonempty α] in
/-- The optimal type-II error is bounded below in exponential form:
`exp(-n · ((klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε)))) ≤ steinOptimalBeta P Q n ε`. -/
lemma exp_le_steinOptimalBeta
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n) :
    Real.exp (-((n : ℝ) * ((klDiv P Q).toReal / (1 - ε)
        + Real.log 2 / ((n : ℝ) * (1 - ε)))))
      ≤ steinOptimalBeta P Q n ε := by
  apply le_csInf (steinBetaSet_nonempty P Q n ε hε.le)
  rintro β ⟨s, hs, hα, rfl⟩
  exact exp_le_Qn_of_alpha_level P Q hPpos hPQ hQpos hε hε1 hn s hs hα

omit [DecidableEq α] [Nonempty α] in
/-- The optimal type-II error `steinOptimalBeta` is strictly positive. -/
lemma steinOptimalBeta_pos
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n) :
    0 < steinOptimalBeta P Q n ε :=
  lt_of_lt_of_le (Real.exp_pos _) (exp_le_steinOptimalBeta P Q hPpos hPQ hQpos hε hε1 hn)

omit [DecidableEq α] [Nonempty α] in
/-- Converse-side upper bound on the type-II exponent:
`-(1/n) log (steinOptimalBeta P Q n ε) ≤ (klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε))`. -/
@[entry_point]
theorem steinOptimalBeta_log_le_of_converse
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n) :
    -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)
      ≤ (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
  have h_pos := steinOptimalBeta_pos P Q hPpos hPQ hQpos hε hε1 hn
  have h_exp_le := exp_le_steinOptimalBeta P Q hPpos hPQ hQpos hε hε1 hn
  set B : ℝ := (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))
  -- exp(-nB) ≤ steinOptimalBeta ⟹ -nB ≤ log steinOptimalBeta ⟹ -(1/n) log ≤ B.
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_log_ge : -((n : ℝ) * B) ≤ Real.log (steinOptimalBeta P Q n ε) := by
    have h_log_mono := Real.log_le_log (Real.exp_pos _) h_exp_le
    rwa [Real.log_exp] at h_log_mono
  -- Multiply by -(1/n) < 0, flips inequality.
  have h_neg_inv_neg : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_step : -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)
      ≤ -((1 : ℝ) / n) * (-((n : ℝ) * B)) :=
    mul_le_mul_of_nonpos_left h_log_ge h_neg_inv_neg
  have h_simp : -((1 : ℝ) / n) * (-((n : ℝ) * B)) = B := by field_simp
  linarith

omit [DecidableEq α] in
/-- Achievability-side lower bound on the type-II exponent: eventually
`(klDiv P Q).toReal − δ ≤ -(1/n) log (steinOptimalBeta P Q n ε)`. -/
@[entry_point]
theorem steinOptimalBeta_log_ge_of_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n ↦ P))
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (klDiv P Q).toReal - δ
        ≤ -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε) := by
  have h_ach := stein_achievability μ P Q Xs hXs hindep hident hMap hMapJoint
    hPpos hPQ hQpos hε hε1 hδ
  filter_upwards [h_ach, eventually_gt_atTop 0] with n h_ex hn_pos
  obtain ⟨s, hs_meas, hs_alpha, hs_log⟩ := h_ex
  -- hs_log : K - δ ≤ -(1/n) log Q^n s
  -- (Q^n s).toReal ∈ steinBetaSet, so steinOptimalBeta ≤ Q^n s.
  set Qn_s : ℝ := ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal with hQns_def
  have h_in_set : Qn_s ∈ steinBetaSet P Q n ε := ⟨s, hs_meas, hs_alpha, rfl⟩
  have h_optBeta_le : steinOptimalBeta P Q n ε ≤ Qn_s :=
    csInf_le (steinBetaSet_bddBelow P Q n ε) h_in_set
  -- Both sides positive: steinOptimalBeta > 0 (from converse-side bound) and Qn_s > 0.
  have h_opt_pos := steinOptimalBeta_pos P Q hPpos hPQ hQpos hε hε1 hn_pos
  -- Qn_s > 0: reproduce from the achievability proof's argument (Q^n s ≥ Q^n {x} > 0).
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  set Pn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ P)
  set Qn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ Q)
  have h_Pn_total : Pn.real s + Pn.real sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hs_meas]; exact probReal_univ
  have h_Pn_sc_eq : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
  have h_Pn_s_pos : 0 < Pn.real s := by
    rw [h_Pn_sc_eq] at h_Pn_total
    have : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
    linarith [hs_alpha, h_Pn_total]
  have h_s_nonempty : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h_empty
    rw [h_empty] at h_Pn_s_pos; simp at h_Pn_s_pos
  obtain ⟨x_w, hx_in_s⟩ := h_s_nonempty
  have h_Qn_x_pos : 0 < Qn.real {x_w} := by
    show 0 < ((Measure.pi (fun _ : Fin n ↦ Q)) {x_w}).toReal
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ ↦ hQpos (x_w i))
  have h_Qns_pos : 0 < Qn_s := by
    have h_subset : ({x_w} : Set (Fin n → α)) ⊆ s := by
      intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hx_in_s
    have := MeasureTheory.measureReal_mono (μ := Qn) h_subset
    -- Qn.real {x_w} ≤ Qn.real s = Qn_s
    have h_eq : Qn.real s = Qn_s := rfl
    linarith
  -- log monotonicity: log steinOptimalBeta ≤ log Qn_s.
  have h_log_le : Real.log (steinOptimalBeta P Q n ε) ≤ Real.log Qn_s :=
    Real.log_le_log h_opt_pos h_optBeta_le
  -- Multiply by -(1/n) ≤ 0 flips:
  have h_neg_inv_nonpos : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_rate_ge : -((1 : ℝ) / n) * Real.log Qn_s
      ≤ -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε) :=
    mul_le_mul_of_nonpos_left h_log_le h_neg_inv_nonpos
  -- Conclude from hs_log : K - δ ≤ -(1/n) log Qn_s ≤ -(1/n) log steinOptimalBeta.
  linarith

end InformationTheory.Shannon
