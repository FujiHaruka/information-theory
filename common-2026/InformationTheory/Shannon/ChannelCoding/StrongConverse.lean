import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.StrongStein
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Channel coding strong converse — Verdú-Han single-shot lower bound

Single-shot Verdú-Han lower bound (Lemma 4.2.2) for the channel coding strong converse.
For any code `c`, reference output law `Q^n`, and `γ > 0`, with `threshold := log M + γ`:

```
1 - (c.averageErrorProb W).toReal
  ≤ exp γ + (1 / M) * ∑ m, P_m^n (highLLRSet W c Q^n threshold m)
```

where `P_m^n := Measure.pi (fun i => W (c.encoder m i))` and
`highLLRSet W c Q^n t m := { y | P_m^n.real {y} > exp(t) · Q^n.real {y} }`.

The asymptotic `Pe → 1` conclusion (for `log M / n > I + δ`) requires a WLLN step
handled in a separate file.

## Implementation notes

The reference measure `Q^n` is an arbitrary probability measure (not necessarily
i.i.d. `(outputDistribution p W)^n`), following Verdú-Han's deterministic formulation
and separating the input-distribution dependence to the caller.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ### Per-codeword information-density lower bound -/

/-- **High-LLR set for codeword `m`**: those `y` where the channel output law at
codeword `m` exceeds the reference `Q` by more than `exp(threshold)`. -/
noncomputable def highLLRSet
    {M n : ℕ} (W : Channel α β) (c : Code M n α β)
    (Q : Measure (Fin n → β)) (threshold : ℝ) (m : Fin M) :
    Set (Fin n → β) :=
  { y | (Measure.pi (fun i ↦ W (c.encoder m i))).real {y}
          > Real.exp threshold * Q.real {y} }

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
lemma measurableSet_highLLRSet
    {M n : ℕ} (W : Channel α β) (c : Code M n α β)
    (Q : Measure (Fin n → β)) (threshold : ℝ) (m : Fin M) :
    MeasurableSet (highLLRSet W c Q threshold m) :=
  (Set.toFinite _).measurableSet

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
/-- **Per-codeword Markov-style bound**: For each codeword `m`, the channel
output mass on `s \ highLLR_m` is bounded by `exp(threshold) · Q(s)`. -/
theorem channelCoding_per_codeword_markov_bound
    {M n : ℕ} (W : Channel α β) [IsMarkovKernel W] (c : Code M n α β)
    (Q : Measure (Fin n → β)) [IsFiniteMeasure Q]
    (threshold : ℝ) (m : Fin M)
    (s : Set (Fin n → β)) (_hs : MeasurableSet s) :
    ((Measure.pi (fun i ↦ W (c.encoder m i))).real
        (s \ highLLRSet W c Q threshold m))
      ≤ Real.exp threshold * Q.real s := by
  classical
  -- Pm = product of Markov kernel applications = probability measure (→ SigmaFinite).
  have hPm_prob : IsProbabilityMeasure
      (Measure.pi (fun i ↦ W (c.encoder m i))) := by infer_instance
  -- s \ highLLR is finite (Fin n → β is finite).
  set H : Set (Fin n → β) := highLLRSet W c Q threshold m with hH_def
  have hs'_finite : (s \ H).Finite := Set.toFinite _
  set Fs' : Finset (Fin n → β) := hs'_finite.toFinset
  have hFs'_coe : (Fs' : Set (Fin n → β)) = s \ H := by
    simp [Fs']
  -- Per-point bound on Fs': y ∉ H means P {y} ≤ exp(threshold) Q {y}.
  have h_per_point : ∀ y ∈ Fs',
      (Measure.pi (fun i ↦ W (c.encoder m i))).real {y}
        ≤ Real.exp threshold * Q.real {y} := by
    intro y hy
    have hy_s' : y ∈ s \ H := (Set.Finite.mem_toFinset _).mp hy
    have hy_notH : y ∉ H := hy_s'.2
    by_contra h_neg
    exact hy_notH (not_le.mp h_neg)
  -- Sum the bounds.
  have h_sum_le :
      ∑ y ∈ Fs', (Measure.pi (fun i ↦ W (c.encoder m i))).real {y}
        ≤ ∑ y ∈ Fs', Real.exp threshold * Q.real {y} :=
    Finset.sum_le_sum h_per_point
  rw [← Finset.mul_sum] at h_sum_le
  rw [MeasureTheory.sum_measureReal_singleton] at h_sum_le
  rw [MeasureTheory.sum_measureReal_singleton] at h_sum_le
  -- After these rewrites, h_sum_le has Fs' on each side as `μ.real ↑Fs'`.
  -- Convert to `μ.real (s \ H)` using hFs'_coe.
  rw [hFs'_coe] at h_sum_le
  -- Now h_sum_le : Pm.real (s \ H) ≤ exp threshold * Q.real (s \ H).
  -- Strengthen RHS via Q.real (s \ H) ≤ Q.real s.
  have h_Q_mono : Q.real (s \ H) ≤ Q.real s := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono Set.diff_subset
  have h_exp_nn : 0 ≤ Real.exp threshold := (Real.exp_pos _).le
  calc (Measure.pi (fun i ↦ W (c.encoder m i))).real (s \ H)
      ≤ Real.exp threshold * Q.real (s \ H) := h_sum_le
    _ ≤ Real.exp threshold * Q.real s :=
        mul_le_mul_of_nonneg_left h_Q_mono h_exp_nn

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
/-- **Verdú-Han single-shot strong-converse decomposition** (per-codeword):
For any codeword `m`, any measurable `s`,

```
P_m^n(s) ≤ exp(threshold) · Q(s) + P_m^n(highLLR_m)
```

The "good" (low-LLR) part is absorbed into the Q-mass term; the "bad" (high-LLR)
part is the explicit tail term. Channel-coding analogue of
`steinTypicalSet_Q_prob_ge`. -/
@[entry_point]
theorem channelCoding_per_codeword_decomposition
    {M n : ℕ} (W : Channel α β) [IsMarkovKernel W] (c : Code M n α β)
    (Q : Measure (Fin n → β)) [IsFiniteMeasure Q]
    (threshold : ℝ) (m : Fin M)
    (s : Set (Fin n → β)) (hs : MeasurableSet s) :
    (Measure.pi (fun i ↦ W (c.encoder m i))).real s
      ≤ Real.exp threshold * Q.real s
        + (Measure.pi (fun i ↦ W (c.encoder m i))).real
            (highLLRSet W c Q threshold m) := by
  classical
  set Pm : Measure (Fin n → β) := Measure.pi (fun i ↦ W (c.encoder m i))
  set H : Set (Fin n → β) := highLLRSet W c Q threshold m
  have hH_meas : MeasurableSet H := measurableSet_highLLRSet W c Q threshold m
  -- Split s = (s \ H) ⊎ (s ∩ H).
  have h_diff_meas : MeasurableSet (s \ H) := hs.diff hH_meas
  have h_inter_meas : MeasurableSet (s ∩ H) := hs.inter hH_meas
  have h_disj : Disjoint (s \ H) (s ∩ H) := by
    rw [Set.disjoint_iff]
    intro y ⟨⟨_, hyNotH⟩, ⟨_, hyH⟩⟩
    exact hyNotH hyH
  have h_split_set : s = (s \ H) ∪ (s ∩ H) := by
    ext y
    constructor
    · intro hy
      by_cases hyH : y ∈ H
      · exact Or.inr ⟨hy, hyH⟩
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  -- Pm s = Pm (s\H) + Pm (s∩H).
  have h_meas_real_split : Pm.real s = Pm.real (s \ H) + Pm.real (s ∩ H) := by
    conv_lhs => rw [h_split_set]
    have h_add_ennreal : Pm ((s \ H) ∪ (s ∩ H)) = Pm (s \ H) + Pm (s ∩ H) :=
      measure_union h_disj h_inter_meas
    rw [MeasureTheory.measureReal_def, h_add_ennreal,
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rfl
  rw [h_meas_real_split]
  have h_diff_bd : Pm.real (s \ H) ≤ Real.exp threshold * Q.real s :=
    channelCoding_per_codeword_markov_bound W c Q threshold m s hs
  have h_inter_bd : Pm.real (s ∩ H) ≤ Pm.real H := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono Set.inter_subset_right
  linarith

/-! ### Codeword-average Verdú-Han lower bound -/

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
/-- Algebraic identity: `1 - avgErrorProb = (1/M) · ∑_m Pm(decodingRegion m)`,
where `Pm = Measure.pi (fun i => W (encoder m i))`. -/
lemma channelCoding_one_sub_avgErr_eq
    {M : ℕ} (hM : 0 < M) {n : ℕ}
    (W : Channel α β) [IsMarkovKernel W] (c : Code M n α β) :
    (1 - (c.averageErrorProb W).toReal)
      = (1 / M : ℝ) * ∑ m : Fin M,
          (Measure.pi (fun i ↦ W (c.encoder m i))).real (c.decodingRegion m) := by
  have h_M_R_pos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM_ne : (M : ℝ) ≠ 0 := h_M_R_pos.ne'
  let Pm : Fin M → Measure (Fin n → β) :=
    fun m ↦ Measure.pi (fun i ↦ W (c.encoder m i))
  have h_pm_prob : ∀ m : Fin M, IsProbabilityMeasure (Pm m) := fun m ↦ by
    show IsProbabilityMeasure (Measure.pi (fun i ↦ W (c.encoder m i)))
    infer_instance
  have h_dec_meas : ∀ m : Fin M, MeasurableSet (c.decodingRegion m) :=
    fun m ↦ c.measurableSet_decodingRegion m
  have h_err_eq_one_sub : ∀ m : Fin M,
      ((Pm m) (c.errorEvent m)).toReal
        = 1 - ((Pm m) (c.decodingRegion m)).toReal := by
    intro m
    have hP : IsProbabilityMeasure (Pm m) := h_pm_prob m
    have h_compl : c.errorEvent m = (c.decodingRegion m)ᶜ := rfl
    rw [h_compl, MeasureTheory.prob_compl_eq_one_sub (h_dec_meas m)]
    rw [ENNReal.toReal_sub_of_le prob_le_one (by simp)]
    simp
  have h_avgPe_def : c.averageErrorProb W
      = (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, c.errorProbAt W m := by
    unfold Code.averageErrorProb
    simp [hM.ne']
  have h_errProbAt : ∀ m : Fin M,
      c.errorProbAt W m = (Pm m) (c.errorEvent m) := fun _ ↦ rfl
  have h_sum_errProb_toReal :
      (∑ m : Fin M, c.errorProbAt W m).toReal
        = ∑ m : Fin M, ((Pm m) (c.errorEvent m)).toReal := by
    have h_ne_top : ∀ m ∈ Finset.univ, c.errorProbAt W m ≠ ∞ :=
      fun m _ ↦ measure_ne_top _ _
    rw [ENNReal.toReal_sum h_ne_top]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [h_errProbAt m]
  have h_avgPe_toReal :
      (c.averageErrorProb W).toReal
        = (1 / M : ℝ) * ∑ m : Fin M, ((Pm m) (c.errorEvent m)).toReal := by
    rw [h_avgPe_def, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, h_sum_errProb_toReal]
    ring
  rw [h_avgPe_toReal]
  have h_sum_err_rewrite :
      ∑ m : Fin M, ((Pm m) (c.errorEvent m)).toReal
        = (M : ℝ) - ∑ m : Fin M, ((Pm m) (c.decodingRegion m)).toReal := by
    have h_step :
        ∑ m : Fin M, ((Pm m) (c.errorEvent m)).toReal
          = ∑ m : Fin M, (1 - ((Pm m) (c.decodingRegion m)).toReal) := by
      refine Finset.sum_congr rfl fun m _ ↦ h_err_eq_one_sub m
    rw [h_step, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [h_sum_err_rewrite]
  set X : ℝ := ∑ m : Fin M, ((Pm m) (c.decodingRegion m)).toReal with hX
  have h_one_div_M : (1 / M : ℝ) * (M : ℝ) = 1 := by field_simp
  have h_arith : 1 - (1 / M : ℝ) * ((M : ℝ) - X) = (1 / M : ℝ) * X := by
    have : (1 / M : ℝ) * ((M : ℝ) - X) = (1 / M : ℝ) * (M : ℝ) - (1 / M : ℝ) * X := by
      ring
    rw [this, h_one_div_M]
    ring
  rw [h_arith]
  rfl

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
/-- **Average-codeword Verdú-Han bound**:
Average the per-codeword decomposition over the uniform message distribution
to get the strong-converse-style lower bound on success probability `1 - avgPe`:

```
1 - avgPe ≤ exp(threshold) / M + (1 / M) · ∑_m P_m^n(highLLR_m)
```

The decoding regions form a measurable partition of `Fin n → β`, so summing
`Q.real (decodingRegion m)` gives `Q.real univ ≤ 1` (since `Q` is a probability
measure), and the first term collapses to `exp(threshold)/M`. -/
@[entry_point]
theorem channelCoding_average_success_le
    {M : ℕ} (hM : 0 < M) {n : ℕ}
    (W : Channel α β) [IsMarkovKernel W] (c : Code M n α β)
    (Q : Measure (Fin n → β)) [IsProbabilityMeasure Q]
    (threshold : ℝ) :
    (1 - (c.averageErrorProb W).toReal)
      ≤ Real.exp threshold / M + (1 / M : ℝ) *
          ∑ m : Fin M, (Measure.pi (fun i ↦ W (c.encoder m i))).real
            (highLLRSet W c Q threshold m) := by
  classical
  have h_M_R_pos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM_ne : (M : ℝ) ≠ 0 := h_M_R_pos.ne'
  -- Notation.
  let Pm : Fin M → Measure (Fin n → β) :=
    fun m ↦ Measure.pi (fun i ↦ W (c.encoder m i))
  -- Step 1: 1 - avgPe = (1/M) · ∑_m Pm m (decodingRegion m).
  rw [channelCoding_one_sub_avgErr_eq hM W c]
  -- Step 2: apply per-codeword decomposition.
  have h_per_m : ∀ m : Fin M,
      (Pm m).real (c.decodingRegion m)
        ≤ Real.exp threshold * Q.real (c.decodingRegion m)
          + (Pm m).real (highLLRSet W c Q threshold m) := fun m ↦
    channelCoding_per_codeword_decomposition W c Q threshold m
      (c.decodingRegion m) (c.measurableSet_decodingRegion m)
  have h_sum_le :
      ∑ m : Fin M, (Pm m).real (c.decodingRegion m)
        ≤ ∑ m : Fin M, (Real.exp threshold * Q.real (c.decodingRegion m)
            + (Pm m).real (highLLRSet W c Q threshold m)) :=
    Finset.sum_le_sum (fun m _ ↦ h_per_m m)
  have h_sum_split :
      ∑ m : Fin M, (Real.exp threshold * Q.real (c.decodingRegion m)
          + (Pm m).real (highLLRSet W c Q threshold m))
        = Real.exp threshold * ∑ m : Fin M, Q.real (c.decodingRegion m)
            + ∑ m : Fin M, (Pm m).real (highLLRSet W c Q threshold m) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h_sum_split] at h_sum_le
  -- Decoding regions are pairwise disjoint.
  have h_pairwise_disj : Pairwise (fun m m' : Fin M ↦
      Disjoint (c.decodingRegion m) (c.decodingRegion m')) := by
    intro m m' hmm'
    rw [Set.disjoint_iff]
    intro y ⟨hym, hym'⟩
    simp only [Code.decodingRegion, Set.mem_setOf_eq] at hym hym'
    exact hmm' (hym.symm.trans hym')
  -- ∑ Q.real (dec m) = Q.real (⋃ dec m) ≤ Q.real univ = 1.
  have h_Q_sum_le_one : ∑ m : Fin M, Q.real (c.decodingRegion m) ≤ 1 := by
    -- measure_iUnion gives a tsum; convert to Finset.sum via Fintype.
    have h_union_eq_tsum :
        Q (⋃ m : Fin M, c.decodingRegion m)
          = ∑' m : Fin M, Q (c.decodingRegion m) :=
      measure_iUnion (fun m m' hmm' ↦ h_pairwise_disj hmm')
        (fun m ↦ c.measurableSet_decodingRegion m)
    have h_tsum_eq_sum :
        (∑' m : Fin M, Q (c.decodingRegion m))
          = ∑ m : Fin M, Q (c.decodingRegion m) :=
      tsum_eq_sum (fun m hm ↦ absurd (Finset.mem_univ m) hm)
    have h_union_eq :
        Q (⋃ m : Fin M, c.decodingRegion m)
          = ∑ m : Fin M, Q (c.decodingRegion m) := by
      rw [h_union_eq_tsum, h_tsum_eq_sum]
    have h_le_univ : Q (⋃ m : Fin M, c.decodingRegion m) ≤ Q Set.univ :=
      measure_mono (Set.subset_univ _)
    have h_univ_eq_one : Q Set.univ = 1 := measure_univ
    have h_le_one_ennreal : (∑ m : Fin M, Q (c.decodingRegion m)) ≤ 1 := by
      rw [← h_union_eq]; rw [← h_univ_eq_one]; exact h_le_univ
    have h_each_ne_top : ∀ m ∈ Finset.univ, Q (c.decodingRegion m) ≠ ∞ :=
      fun m _ ↦ measure_ne_top _ _
    have h_toReal_sum :
        (∑ m : Fin M, Q (c.decodingRegion m)).toReal
          = ∑ m : Fin M, (Q (c.decodingRegion m)).toReal :=
      ENNReal.toReal_sum h_each_ne_top
    have h_toReal_le_one :
        (∑ m : Fin M, Q (c.decodingRegion m)).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) h_le_one_ennreal
      simpa using h
    rw [h_toReal_sum] at h_toReal_le_one
    exact h_toReal_le_one
  -- Combine.
  have h_exp_nn : 0 ≤ Real.exp threshold := (Real.exp_pos _).le
  have h_Q_part :
      Real.exp threshold * ∑ m : Fin M, Q.real (c.decodingRegion m)
        ≤ Real.exp threshold * 1 :=
    mul_le_mul_of_nonneg_left h_Q_sum_le_one h_exp_nn
  have h_total :
      ∑ m : Fin M, (Pm m).real (c.decodingRegion m)
        ≤ Real.exp threshold + ∑ m : Fin M, (Pm m).real (highLLRSet W c Q threshold m) := by
    linarith [h_sum_le, h_Q_part]
  have h_inv_nn : (0 : ℝ) ≤ 1 / M := by positivity
  have h_final :
      (1 / M : ℝ) * ∑ m : Fin M, (Pm m).real (c.decodingRegion m)
        ≤ (1 / M : ℝ) * (Real.exp threshold +
            ∑ m : Fin M, (Pm m).real (highLLRSet W c Q threshold m)) :=
    mul_le_mul_of_nonneg_left h_total h_inv_nn
  rw [mul_add] at h_final
  have h_first_rew : (1 / M : ℝ) * Real.exp threshold = Real.exp threshold / M := by
    field_simp
  rw [h_first_rew] at h_final
  -- Done.
  exact h_final

/-! ### Main form with `threshold := log M + γ` -/

end InformationTheory.Shannon.ChannelCoding
