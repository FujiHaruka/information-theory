import InformationTheory.Shannon.Sanov.LiminfBound

/-!
# Sanov LDP equality form (Tendsto sandwich)

Cover-Thomas Theorem 11.4.1, simplified open-set form:

```
(1/n) log Q^n(⋃ c ∈ E n, T_c)  →  -D   as n → ∞
```

where `D = klDivSumForm_ofVec P (Q.real ∘ singleton)`, given `E n` eventually contains
`roundedTypeIndex P n` and `∀ c ∈ E n, D ≤ klDivIndex c n Q`.

## Main statements

* `sanov_ldp_equality` — sandwich: `Tendsto (1/n) log Q^n(⋃ c ∈ E n, T_c) → -D`.

## Implementation notes

* The equality closes via `tendsto_of_le_liminf_of_limsup_le`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.),
  Wiley, 2006. Theorem 11.4.1.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Tendsto sandwich (main theorem) -/

omit [MeasurableSingletonClass α] in
theorem iUnion_typeClassByCount_pos_of_mem
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    {n : ℕ} (hn_pos : 0 < n)
    (h_inE : roundedTypeIndex P n ∈ E n) :
    0 < ((Measure.pi (fun _ : Fin n ↦ Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal := by
  classical
  obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
    (fun a ↦ (roundedTypeIndex P n a : ℕ))
    (roundedTypeIndex_sum P hP_prob hP_nn n hn_pos)
  have hx_in_union : x ∈ ⋃ c ∈ E n,
      typeClassByCount (α := α) (fun a ↦ (c a : ℕ)) := by
    simp only [Set.mem_iUnion]
    exact ⟨roundedTypeIndex P n, ⟨h_inE, hx⟩⟩
  have h_singleton_pos : (0 : ℝ) <
      ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal := by
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    apply Finset.prod_pos
    intros i _
    exact hQpos (x i)
  have h_singleton_le : ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal
      ≤ ((Measure.pi (fun _ : Fin n ↦ Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal := by
    apply ENNReal.toReal_mono
    · exact measure_ne_top _ _
    · exact measure_mono (Set.singleton_subset_iff.mpr hx_in_union)
  linarith

omit [MeasurableSingletonClass α] in
theorem log_le_inv_mul_log_iUnion_of_forall_le
    (Q : Measure α) [IsProbabilityMeasure Q]
    (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    {n : ℕ} (hn_pos : 0 < n)
    (h_inE : roundedTypeIndex P n ∈ E n)
    {m : ℝ} (hm_pos : 0 < m) (hm_le : ∀ a, m ≤ Q.real {a}) :
    Real.log m ≤ (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n ↦ Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal) := by
  classical
  obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
    (fun a ↦ (roundedTypeIndex P n a : ℕ))
    (roundedTypeIndex_sum P hP_prob hP_nn n hn_pos)
  have hx_in_union : x ∈ ⋃ c ∈ E n,
      typeClassByCount (α := α) (fun a ↦ (c a : ℕ)) := by
    simp only [Set.mem_iUnion]
    exact ⟨roundedTypeIndex P n, ⟨h_inE, hx⟩⟩
  -- Q^n({x}) = ∏ Q.real {x_i} ≥ m^n.
  have h_singleton_eq : ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal
      = ∏ i : Fin n, Q.real {x i} := by
    rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl
  have h_singleton_ge : ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal ≥ m ^ n := by
    rw [h_singleton_eq]
    calc m ^ n = ∏ _i : Fin n, m := by rw [Finset.prod_const]; simp
      _ ≤ ∏ i : Fin n, Q.real {x i} :=
        Finset.prod_le_prod (fun i _ ↦ hm_pos.le) (fun i _ ↦ hm_le (x i))
  have h_union_ge_m_pow : ((Measure.pi (fun _ : Fin n ↦ Q))
      (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal ≥ m ^ n := by
    have h1 : ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal
        ≤ ((Measure.pi (fun _ : Fin n ↦ Q))
            (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal := by
      apply ENNReal.toReal_mono
      · exact measure_ne_top _ _
      · exact measure_mono (Set.singleton_subset_iff.mpr hx_in_union)
    linarith
  -- So log Q^n(⋃) ≥ log (m^n) = n log m, and (1/n) log ≥ log m.
  have h_pow_pos : (0 : ℝ) < m ^ n := pow_pos hm_pos _
  have h_log_pow_le : Real.log (m ^ n) ≤ Real.log
      (((Measure.pi (fun _ : Fin n ↦ Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal) :=
    Real.log_le_log h_pow_pos h_union_ge_m_pow
  rw [Real.log_pow] at h_log_pow_le
  have h_n_inv_pos : 0 < 1 / (n : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left h_log_pow_le h_n_inv_pos.le
  rw [show (1 / (n : ℝ)) * ((n : ℝ) * Real.log m) = Real.log m by field_simp] at h
  exact h

/-- **Sanov's theorem** (LDP, equality form):

```
(1/n) log Q^n(⋃ c ∈ E n, T_c)  →  -klDivSumForm_ofVec P (Q.real ∘ singleton)
```

for the minimizer `P` whose rounded type sequence eventually lies in `E n`. -/
@[entry_point]
theorem sanov_ldp_equality
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (P : α → ℝ) (hP_prob : (∑ a, P a) = 1)
    (hP_full : ∀ a, 0 < P a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n)
    (h_minimizer : ∀ n, ∀ c ∈ E n,
      klDivSumForm_ofVec P (fun a ↦ Q.real {a})
        ≤ klDivIndex (fun a ↦ (c a : ℕ)) n Q) :
    Tendsto
      (fun n : ℕ ↦ (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n ↦ Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal))
      atTop (𝓝 (-(klDivSumForm_ofVec P (fun a ↦ Q.real {a})))) := by
  classical
  set D : ℝ := klDivSumForm_ofVec P (fun a ↦ Q.real {a}) with hD_def
  set f : ℕ → ℝ := fun n ↦ (1 / (n : ℝ)) * Real.log
    (((Measure.pi (fun _ : Fin n ↦ Q))
      (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal) with hf_def
  have hP_nn : ∀ a, 0 ≤ P a := fun a ↦ (hP_full a).le
  -- Lower bound: -D ≤ liminf f.
  have h_liminf : -D ≤ liminf f atTop :=
    sanov_ldp_lower_bound_pointwise Q hQpos P hP_prob hP_full E h_in_E
  -- Upper bound: limsup f ≤ -D.
  -- Strategy: provide eventually upper bound `f ≤ -D + ε` for any ε > 0,
  -- conclude `f` bounded above.
  -- Then use ε → 0 to get limsup ≤ -D.
  have h_upper_event : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, f n ≤ -D + ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := sanov_ldp_upper_bound Q hQpos E D h_minimizer hε
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ hn⟩
    have h_n_ge : ∀ᶠ n : ℕ in atTop, N₀ ≤ n :=
      Filter.eventually_atTop.mpr ⟨N₀, fun n hn ↦ hn⟩
    filter_upwards [h_n_pos, h_n_ge, h_in_E] with n hn_pos hn_ge h_inE
    -- Q^n(⋃) > 0: since T_{c_n} ⊆ ⋃ and T_{c_n} nonempty, Q^n nonempty subset > 0.
    have h_meas_pos : 0 < ((Measure.pi (fun _ : Fin n ↦ Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal :=
      iUnion_typeClassByCount_pos_of_mem Q hQpos P hP_prob hP_nn E hn_pos h_inE
    exact hN₀ n hn_ge hn_pos h_meas_pos
  -- bounded above eventually: f ≤ -D + 1. (`IsBoundedUnder (·≤·)`: ∃b, eventually f ≤ b.)
  have h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop f := by
    refine ⟨-D + 1, ?_⟩
    rw [Filter.eventually_map]
    have := h_upper_event 1 (by norm_num)
    filter_upwards [this] with n hn; exact hn
  -- bounded below eventually: -D ≤ liminf is fine in the conditionally complete world,
  -- but for IsBoundedUnder ge we use the liminf bound to get a uniform finite lower bound.
  -- f n ≥ -D - 1 eventually (via the liminf bound or just: f bounded since 0 < Q^n ≤ 1, log ≤ 0).
  -- f n is bounded below uniformly using ` Q^n(⋃) ≥ Q^n({x}) ≥ (∏ Q(x_i)) ≥ (min Q a)^n `.
  -- ⇒ log Q^n(⋃) ≥ n · log (min Q a), so (1/n) log Q^n(⋃) ≥ log (min Q a) = -|log (min Q a)|.
  -- Pick `M := -log (min_a Q.real {a})` (positive, finite, since each Q.real {a} > 0 and finite α).
  have h_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop f := by
    -- Get minimum: m := min_a Q.real {a} > 0 since α nonempty Fintype.
    obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image (s := (Finset.univ : Finset α))
      (f := fun a ↦ Q.real {a}) ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
    -- ha₀ : ∀ a' ∈ univ, Q.real {a₀} ≤ Q.real {a'}
    set m : ℝ := Q.real {a₀}
    have hm_pos : 0 < m := hQpos a₀
    have hm_le : ∀ a, m ≤ Q.real {a} := fun a ↦ ha₀ a (Finset.mem_univ _)
    refine ⟨Real.log m, ?_⟩
    rw [Filter.eventually_map]
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ hn⟩
    filter_upwards [h_n_pos, h_in_E] with n hn_pos h_inE
    -- goal: f n ≥ Real.log m, i.e. Real.log m ≤ f n
    exact log_le_inv_mul_log_iUnion_of_forall_le Q P hP_prob hP_nn E hn_pos h_inE hm_pos hm_le
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
