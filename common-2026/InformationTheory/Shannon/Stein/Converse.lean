import InformationTheory.Shannon.Stein.Achievability

/-!
# Stein's lemma: converse

The converse (upper bound) side of Stein's lemma. Every `ε`-level test obeys the matching
converse rate bound: the argument reduces the test to a Bernoulli random variable, applies the
data-processing inequality together with the KL tensorization, expands the resulting two-point
KL divergence into its sum form, and finally sharpens it using the level constraint into the
concrete rate bound.

## Main statements

* `stein_converse_finite_n` — every `ε`-level test obeys the matching converse rate bound
  `-(1/n) log Qⁿ s ≤ (klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε))`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.),
  Wiley, 2006. Theorem 11.8.3.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Stein converse

Every `ε`-level test obeys the converse rate bound. -/

omit [DecidableEq α] [Nonempty α] in
/-- The `toReal` KL divergence between two probability measures on `Bool` (with `μ ≪ ν`) expands
into the two-point sum
`μ{true} · (log μ{true} − log ν{true}) + μ{false} · (log μ{false} − log ν{false})`. -/
private lemma klDiv_bool_toReal_eq_sum
    (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal
      = (μ.real {true}) * (Real.log (μ.real {true}) - Real.log (ν.real {true}))
      + (μ.real {false}) * (Real.log (μ.real {false}) - Real.log (ν.real {false})) := by
  -- Use the same proof skeleton as Bridge.lean's `klDiv_discrete_toReal_eq_sum`,
  -- specialized to `Bool` (Fintype with 2 elements).
  have h_univ : μ Set.univ = ν Set.univ := by
    rw [measure_univ, measure_univ]
  rw [toReal_klDiv_of_measure_eq hμν h_univ]
  have h_int : Integrable (llr μ ν) μ := by
    refine ⟨(measurable_llr μ ν).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ ↦
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  rw [integral_fintype h_int]
  -- Now expand the Fintype sum over `Bool = {true, false}` and per-point rewrite.
  -- `Fintype.sum_bool` gives `∑ b : Bool, f b = f true + f false`.
  rw [show (∑ b : Bool, μ.real {b} • llr μ ν b)
      = μ.real {true} • llr μ ν true + μ.real {false} • llr μ ν false from by
        rw [Fintype.sum_bool]]
  -- Per-point rewrite: `μ.real {b} • llr μ ν b = μ.real {b} * (log μ.real{b} - log ν.real{b})`
  have h_per_point : ∀ b : Bool,
      μ.real {b} • llr μ ν b = μ.real {b} * (Real.log (μ.real {b}) - Real.log (ν.real {b})) := by
    intro b
    show μ.real {b} * Real.log (μ.rnDeriv ν b).toReal
      = μ.real {b} * (Real.log (μ.real {b}) - Real.log (ν.real {b}))
    by_cases hμb : μ.real {b} = 0
    · simp [hμb]
    -- `μ.real {b} > 0` ⇒ `ν.real {b} > 0` and rnDeriv equals their ratio.
    have hμ_ne : μ {b} ≠ 0 := by
      intro h
      apply hμb
      rw [Measure.real, h]; rfl
    have hν_ne : ν {b} ≠ 0 := fun h ↦ hμ_ne (hμν h)
    have hνb_pos : 0 < ν.real {b} := by
      refine lt_of_le_of_ne measureReal_nonneg (Ne.symm ?_)
      intro hνb
      apply hν_ne
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff,
        or_iff_left (measure_ne_top ν {b})] at hνb
    have hμb_pos : 0 < μ.real {b} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hμb)
    -- ENNReal identity: `(μ.rnDeriv ν b) * ν {b} = μ {b}`.
    have h_rnD_enn : (μ.rnDeriv ν b) * ν {b} = μ {b} := by
      have h_wd : ν.withDensity (μ.rnDeriv ν) = μ :=
        Measure.withDensity_rnDeriv_eq μ ν hμν
      have h1 : (ν.withDensity (μ.rnDeriv ν)) {b} = μ {b} := by rw [h_wd]
      rw [withDensity_apply _ (measurableSet_singleton b),
        lintegral_singleton] at h1
      exact h1
    have h_rnD_real : (μ.rnDeriv ν b).toReal * ν.real {b} = μ.real {b} := by
      rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_rnD_enn]
    have h_rnD_div : (μ.rnDeriv ν b).toReal = μ.real {b} / ν.real {b} := by
      field_simp
      linarith [h_rnD_real]
    rw [h_rnD_div, Real.log_div hμb_pos.ne' hνb_pos.ne']
  rw [h_per_point true, h_per_point false]

omit [DecidableEq α] [Nonempty α] in
/-- The `Bool`-valued indicator of a test `s : Set (Fin n → α)`. -/
private noncomputable def steinTestFn (n : ℕ) (s : Set (Fin n → α)) :
    (Fin n → α) → Bool :=
  fun x ↦ @decide (x ∈ s) (Classical.dec _)

omit [DecidableEq α] [Nonempty α] in
private lemma measurable_steinTestFn (n : ℕ) (s : Set (Fin n → α)) :
    Measurable (steinTestFn n s) := measurable_of_finite _

omit [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
private lemma steinTestFn_preimage_true (n : ℕ) (s : Set (Fin n → α)) :
    steinTestFn n s ⁻¹' {true} = s := by
  ext x
  simp [steinTestFn]

omit [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
private lemma steinTestFn_preimage_false (n : ℕ) (s : Set (Fin n → α)) :
    steinTestFn n s ⁻¹' {false} = sᶜ := by
  ext x
  simp [steinTestFn]

omit [DecidableEq α] [Nonempty α] in
private lemma steinTestFn_map_true (n : ℕ) (s : Set (Fin n → α)) (μ : Measure (Fin n → α)) :
    (μ.map (steinTestFn n s)) {true} = μ s := by
  rw [Measure.map_apply (measurable_steinTestFn n s) (measurableSet_singleton _),
      steinTestFn_preimage_true]

omit [DecidableEq α] [Nonempty α] in
private lemma steinTestFn_map_false (n : ℕ) (s : Set (Fin n → α)) (μ : Measure (Fin n → α)) :
    (μ.map (steinTestFn n s)) {false} = μ sᶜ := by
  rw [Measure.map_apply (measurable_steinTestFn n s) (measurableSet_singleton _),
      steinTestFn_preimage_false]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Absolute continuity tensorizes: `P ≪ Q` implies `Π_{Fin n} P ≪ Π_{Fin n} Q`. -/
private theorem absolutelyContinuous_pi
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ P) ≪ Measure.pi (fun _ : Fin n ↦ Q) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 ↦ P), Measure.pi_of_empty (fun _ : Fin 0 ↦ Q)]
  | succ k ih =>
    -- Use `piFinSuccAbove 0` to go via `α × (Fin k → α)`.
    set e : ((i : Fin (k + 1)) → (fun _ ↦ α) i) ≃ᵐ
              α × ((j : Fin k) → (fun _ ↦ α) ((0 : Fin (k + 1)).succAbove j)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ α) 0 with he_def
    have hP_pres : MeasurePreserving e
        (Measure.pi (fun _ : Fin (k + 1) ↦ P))
        (P.prod (Measure.pi (fun _ : Fin k ↦ P))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ P) (0 : Fin (k + 1))
    have hQ_pres : MeasurePreserving e
        (Measure.pi (fun _ : Fin (k + 1) ↦ Q))
        (Q.prod (Measure.pi (fun _ : Fin k ↦ Q))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ Q) (0 : Fin (k + 1))
    have hP_map : (Measure.pi (fun _ : Fin (k + 1) ↦ P)).map e
        = P.prod (Measure.pi (fun _ : Fin k ↦ P)) := hP_pres.map_eq
    have hQ_map : (Measure.pi (fun _ : Fin (k + 1) ↦ Q)).map e
        = Q.prod (Measure.pi (fun _ : Fin k ↦ Q)) := hQ_pres.map_eq
    -- Step 1: AC for product measures from coordinate-wise AC.
    have h_prod_ac : (P.prod (Measure.pi (fun _ : Fin k ↦ P)))
        ≪ (Q.prod (Measure.pi (fun _ : Fin k ↦ Q))) :=
      Measure.AbsolutelyContinuous.prod hPQ ih
    -- Step 2: Lift back via `e.symm` (also measure-preserving).
    have h_e_sym_meas : Measurable e.symm := e.symm.measurable
    have h_e_meas : Measurable e := e.measurable
    -- Use `e` is a MeasurableEquiv, so `(map e μ ≪ map e ν) ↔ (μ ≪ ν)`.
    have hPe : Measure.pi (fun _ : Fin (k + 1) ↦ P)
        = (P.prod (Measure.pi (fun _ : Fin k ↦ P))).map e.symm := by
      rw [← hP_map, Measure.map_map h_e_sym_meas h_e_meas, e.symm_comp_self, Measure.map_id]
    have hQe : Measure.pi (fun _ : Fin (k + 1) ↦ Q)
        = (Q.prod (Measure.pi (fun _ : Fin k ↦ Q))).map e.symm := by
      rw [← hQ_map, Measure.map_map h_e_sym_meas h_e_meas, e.symm_comp_self, Measure.map_id]
    rw [hPe, hQe]
    exact h_prod_ac.map h_e_sym_meas

omit [DecidableEq α] [Nonempty α] in
/-- For any test `s`, the KL divergence between the pushforwards of `Pⁿ` and `Qⁿ` along the test
indicator is at most `n · klDiv P Q`. -/
theorem stein_converse_bool_kl_le
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (s : Set (Fin n → α)) :
    klDiv ((Measure.pi (fun _ : Fin n ↦ P)).map (steinTestFn n s))
          ((Measure.pi (fun _ : Fin n ↦ Q)).map (steinTestFn n s))
      ≤ (n : ℝ≥0∞) * klDiv P Q := by
  rw [← klDiv_pi_eq_n_smul P Q n]
  exact klDiv_map_le (measurable_steinTestFn n s) _ _

omit [DecidableEq α] [Nonempty α] in
/-- The two-point sum form of the converse bound:
`(Pⁿ s)(log Pⁿ s − log Qⁿ s) + (Pⁿ sᶜ)(log Pⁿ sᶜ − log Qⁿ sᶜ) ≤ n · (klDiv P Q).toReal`. -/
theorem stein_converse_sum_form
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (n : ℕ) (s : Set (Fin n → α)) :
    let Pn := Measure.pi (fun _ : Fin n ↦ P)
    let Qn := Measure.pi (fun _ : Fin n ↦ Q)
    (Pn.real s) * (Real.log (Pn.real s) - Real.log (Qn.real s))
    + (Pn.real sᶜ) * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
    ≤ (n : ℝ) * (klDiv P Q).toReal := by
  classical
  intro Pn Qn
  have hPnQn : Pn ≪ Qn := absolutelyContinuous_pi P Q hPQ n
  have hf := measurable_steinTestFn n s
  have hPn_map_ac : Pn.map (steinTestFn n s) ≪ Qn.map (steinTestFn n s) := hPnQn.map hf
  -- Probability measure instances on Pi-pushforward.
  have h_Pn_map_prob : IsProbabilityMeasure (Pn.map (steinTestFn n s)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have h_Qn_map_prob : IsProbabilityMeasure (Qn.map (steinTestFn n s)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  -- Translation lemmas: pushforward Bool masses = original measures of `s` / `sᶜ`.
  have h_P_true : (Pn.map (steinTestFn n s)).real {true} = Pn.real s := by
    show ((Pn.map (steinTestFn n s)) {true}).toReal = (Pn s).toReal
    rw [steinTestFn_map_true n s Pn]
  have h_P_false : (Pn.map (steinTestFn n s)).real {false} = Pn.real sᶜ := by
    show ((Pn.map (steinTestFn n s)) {false}).toReal = (Pn sᶜ).toReal
    rw [steinTestFn_map_false n s Pn]
  have h_Q_true : (Qn.map (steinTestFn n s)).real {true} = Qn.real s := by
    show ((Qn.map (steinTestFn n s)) {true}).toReal = (Qn s).toReal
    rw [steinTestFn_map_true n s Qn]
  have h_Q_false : (Qn.map (steinTestFn n s)).real {false} = Qn.real sᶜ := by
    show ((Qn.map (steinTestFn n s)) {false}).toReal = (Qn sᶜ).toReal
    rw [steinTestFn_map_false n s Qn]
  -- Sum-form expansion of LHS = the post-DPI Bool KL.
  have h_sum_eq : (klDiv (Pn.map (steinTestFn n s)) (Qn.map (steinTestFn n s))).toReal
      = (Pn.real s) * (Real.log (Pn.real s) - Real.log (Qn.real s))
      + (Pn.real sᶜ) * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ)) := by
    rw [klDiv_bool_toReal_eq_sum _ _ hPn_map_ac]
    rw [h_P_true, h_P_false, h_Q_true, h_Q_false]
  -- DPI bound on the ENNReal side.
  have h_dpi := stein_converse_bool_kl_le P Q n s
  -- Lift to toReal using `klDiv P Q ≠ ∞`.
  have h_int_llr : Integrable (llr P Q) P := by
    refine ⟨(measurable_llr P Q).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ ↦
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  have h_kl_ne_top : klDiv P Q ≠ ∞ := klDiv_ne_top hPQ h_int_llr
  have h_n_kl_ne_top : (n : ℝ≥0∞) * klDiv P Q ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) h_kl_ne_top
  have h_dpi_real : (klDiv (Pn.map (steinTestFn n s)) (Qn.map (steinTestFn n s))).toReal
      ≤ ((n : ℝ≥0∞) * klDiv P Q).toReal :=
    ENNReal.toReal_mono h_n_kl_ne_top h_dpi
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_dpi_real
  rw [← h_sum_eq]
  exact h_dpi_real

/-! ### The converse inequality

The concrete rate bound
`-(1/n) log Qⁿ s ≤ (klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε))`. -/

omit [DecidableEq α] [Nonempty α] in
/-- **Stein's lemma** (converse, finite `n`): any measurable `ε`-level test `s` (with `Pⁿ sᶜ ≤ ε`)
and `0 < n` satisfies `-(1/n) log Qⁿ s ≤ (klDiv P Q).toReal / (1−ε) + log 2 / (n(1−ε))`. -/
@[entry_point]
theorem stein_converse_finite_n
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (_hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (_hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn_pos : 0 < n) (s : Set (Fin n → α)) (hs : MeasurableSet s)
    (hPn_sc_le : ((Measure.pi (fun _ : Fin n ↦ P)) sᶜ).toReal ≤ ε) :
    -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal
      ≤ (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
  classical
  set Pn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ P) with hPn_def
  set Qn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ Q) with hQn_def
  set K : ℝ := (klDiv P Q).toReal with hK_def
  have h_one_sub_eps_pos : (0 : ℝ) < 1 - ε := by linarith
  have h_n_R_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have h_Pn_prob : IsProbabilityMeasure Pn := by infer_instance
  have h_Qn_prob : IsProbabilityMeasure Qn := by infer_instance
  -- Step A: positivity of Pn univ = Qn univ = 1; complements of measurable sets.
  have hsc : MeasurableSet sᶜ := hs.compl
  -- Pn s + Pn sᶜ = 1.
  have h_Pn_total : Pn.real s + Pn.real sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hs]
    exact probReal_univ
  have h_Pn_sc_eq : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
  have h_Pn_s_ge : Pn.real s ≥ 1 - ε := by
    have := hPn_sc_le
    rw [← h_Pn_sc_eq] at this
    linarith
  have h_Pn_s_R_nn : 0 ≤ Pn.real s := measureReal_nonneg
  have h_Pn_sc_R_nn : 0 ≤ Pn.real sᶜ := measureReal_nonneg
  -- Step B: positivity of Qn s and Qn sᶜ.
  -- Pick any x ∈ Fin n → α; then `{x}` has positive Qn-mass since hQpos.
  -- Pn s ≥ 1 - ε > 0 implies s nonempty, so Qn s > 0.
  have h_Pn_s_pos : 0 < Pn.real s := by linarith
  -- s nonempty (from Pn.real s > 0).
  have h_s_nonempty : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h_empty
    rw [h_empty] at h_Pn_s_pos
    simp at h_Pn_s_pos
  obtain ⟨x_witness, hx_in_s⟩ := h_s_nonempty
  -- Qn {x_witness} > 0 from hQpos.
  have h_Qn_x_pos : 0 < (Qn.real {x_witness}) := by
    rw [hQn_def]
    show ((Measure.pi (fun _ : Fin n ↦ Q)) {x_witness}).toReal > 0
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ ↦ hQpos (x_witness i))
  have h_Qn_s_pos : 0 < Qn.real s := by
    have h_subset : ({x_witness} : Set (Fin n → α)) ⊆ s := by
      intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hx_in_s
    have : Qn.real {x_witness} ≤ Qn.real s := MeasureTheory.measureReal_mono h_subset
    linarith
  -- Qn sᶜ > 0: similarly, but only if sᶜ is nonempty. If s = univ, Qn sᶜ = 0;
  -- but the case Pn sᶜ = 0 is consistent with sᶜ having empty support.
  -- We handle the case Qn sᶜ = 0 separately using `log 0 = 0` convention.
  -- Step C: Bool sum-form bound from `stein_converse_sum_form`.
  have h_sum_bound := stein_converse_sum_form P Q hPQ n s
  simp only at h_sum_bound
  -- (Pn s)(log Pn s - log Qn s) + (Pn sᶜ)(log Pn sᶜ - log Qn sᶜ) ≤ n · K.
  -- Step D: Algebraic lower bound on the LHS (let `S` denote it).
  -- Key bounds:
  --   (i) Qn.real sᶜ ≤ 1, so log Qn.real sᶜ ≤ 0, so -(Pn.real sᶜ)(log Qn.real sᶜ) ≥ 0.
  --   (ii) Qn.real s ≤ 1, so log Qn.real s ≤ 0, so -log Qn.real s ≥ 0.
  --   (iii) (Pn.real s) log Pn.real s + (Pn.real sᶜ) log Pn.real sᶜ
  --         = -binEntropy(Pn.real s) ≥ -log 2.
  have h_Qn_sc_le_one : Qn.real sᶜ ≤ 1 := by
    have : Qn.real sᶜ ≤ Qn.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
    rw [show Qn.real Set.univ = 1 from probReal_univ] at this
    exact this
  have h_log_Qn_sc_nonpos : Real.log (Qn.real sᶜ) ≤ 0 :=
    Real.log_nonpos measureReal_nonneg h_Qn_sc_le_one
  have h_Qn_s_le_one : Qn.real s ≤ 1 := by
    have : Qn.real s ≤ Qn.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
    rw [show Qn.real Set.univ = 1 from probReal_univ] at this
    exact this
  have h_log_Qn_s_nonpos : Real.log (Qn.real s) ≤ 0 :=
    Real.log_nonpos measureReal_nonneg h_Qn_s_le_one
  have h_neg_log_Qn_s_nn : 0 ≤ -Real.log (Qn.real s) := by linarith
  -- Term -(Pn.real sᶜ) log Qn.real sᶜ = Pn.real sᶜ * (- log Qn.real sᶜ) ≥ 0.
  have h_term_sc_nn : 0 ≤ -(Pn.real sᶜ * Real.log (Qn.real sᶜ)) := by
    have : Pn.real sᶜ * (- Real.log (Qn.real sᶜ)) ≥ 0 :=
      mul_nonneg h_Pn_sc_R_nn (by linarith)
    linarith
  -- (Pn.real s) log Pn.real s + (Pn.real sᶜ) log Pn.real sᶜ = -binEntropy (Pn.real s).
  -- Use Pn.real sᶜ = 1 - Pn.real s.
  have h_Pn_sc_eq_1m : Pn.real sᶜ = 1 - Pn.real s := by linarith
  have h_neg_binE_eq :
      Pn.real s * Real.log (Pn.real s) + Pn.real sᶜ * Real.log (Pn.real sᶜ)
        = -Real.binEntropy (Pn.real s) := by
    rw [h_Pn_sc_eq_1m]
    -- binEntropy p = p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹ = -(p log p + (1-p) log(1-p)).
    rw [Real.binEntropy]
    rw [Real.log_inv, Real.log_inv]
    ring
  have h_binE_le_log2 : Real.binEntropy (Pn.real s) ≤ Real.log 2 :=
    Real.binEntropy_le_log_two
  -- Build S ≥ -log 2 + (Pn.real s) * (-log Qn.real s).
  have h_S_lower :
      Pn.real s * (Real.log (Pn.real s) - Real.log (Qn.real s))
      + Pn.real sᶜ * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
        ≥ -Real.log 2 + Pn.real s * (-Real.log (Qn.real s)) := by
    have h_expand :
        Pn.real s * (Real.log (Pn.real s) - Real.log (Qn.real s))
          + Pn.real sᶜ * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
        = (Pn.real s * Real.log (Pn.real s) + Pn.real sᶜ * Real.log (Pn.real sᶜ))
          + Pn.real s * (-Real.log (Qn.real s))
          + (-(Pn.real sᶜ * Real.log (Qn.real sᶜ))) := by ring
    rw [h_expand, h_neg_binE_eq]
    linarith
  -- Build (Pn.real s) * (-log Qn.real s) ≥ (1-ε) * (-log Qn.real s).
  have h_term1_lower :
      Pn.real s * (-Real.log (Qn.real s)) ≥ (1 - ε) * (-Real.log (Qn.real s)) :=
    mul_le_mul_of_nonneg_right h_Pn_s_ge h_neg_log_Qn_s_nn
  -- Combine: S ≥ -log 2 + (1-ε)(-log Qn s).
  have h_S_lower_final :
      Pn.real s * (Real.log (Pn.real s) - Real.log (Qn.real s))
      + Pn.real sᶜ * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
        ≥ -Real.log 2 + (1 - ε) * (-Real.log (Qn.real s)) := by linarith
  -- Step E: Combine S ≤ n · K with S ≥ -log 2 + (1-ε)(-log Qn s).
  have h_chain : -Real.log 2 + (1 - ε) * (-Real.log (Qn.real s)) ≤ (n : ℝ) * K :=
    le_trans h_S_lower_final h_sum_bound
  have h_div : (1 - ε) * (-Real.log (Qn.real s)) ≤ (n : ℝ) * K + Real.log 2 := by linarith
  have h_neg_log_le : -Real.log (Qn.real s) ≤ ((n : ℝ) * K + Real.log 2) / (1 - ε) := by
    rw [le_div_iff₀ h_one_sub_eps_pos]
    linarith
  -- Convert `-(1/n) log Qn s = (1/n) * (-log Qn s)`.
  have h_target_eq : -((1 : ℝ) / n) * Real.log (Qn.real s) = (1 / n) * (-Real.log (Qn.real s)) := by
    ring
  -- Multiply by 1/n (positive) on both sides.
  have h_one_div_n_pos : 0 < (1 : ℝ) / n := by positivity
  have h_div_n : (1 / (n : ℝ)) * (-Real.log (Qn.real s))
      ≤ (1 / n) * (((n : ℝ) * K + Real.log 2) / (1 - ε)) := by
    exact mul_le_mul_of_nonneg_left h_neg_log_le h_one_div_n_pos.le
  -- Simplify (1/n) * ((n*K + log 2) / (1-ε)) = K/(1-ε) + log 2 / (n(1-ε)).
  have h_simp_R : (1 / (n : ℝ)) * (((n : ℝ) * K + Real.log 2) / (1 - ε))
      = K / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
    field_simp
  -- Convert `Pn.real s = (Pn s).toReal` etc. to expected statement form.
  have h_target : -((1 : ℝ) / n) * Real.log (Qn.real s)
      ≤ K / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
    rw [h_target_eq]
    rw [← h_simp_R]
    exact h_div_n
  -- Unfold Qn.real and conclude.
  show -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal
      ≤ (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))
  exact h_target

end InformationTheory.Shannon
