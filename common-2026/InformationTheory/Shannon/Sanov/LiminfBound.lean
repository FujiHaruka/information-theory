import InformationTheory.Shannon.Sanov.MultinomialLowerBound

/-!
# Sanov LDP liminf lower bound

The liminf lower bound for Sanov's theorem (Cover-Thomas Theorem 11.4.1):
`liminf (1/n) log Q^n(⋃ c ∈ E n, T_c) ≥ -D`, extracted by sandwiching the
per-`n` lower bound with `|α| log(n+1)/n → 0`.

## Main statements

* `sanov_ldp_lower_bound_pointwise` — `liminf (1/n) log Q^n(⋃ c ∈ E n, T_c) ≥ -D`.

## Implementation notes

* The `liminf` bound is extracted by sandwiching with `|α| log(n+1)/n → 0`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### liminf lower bound -/

theorem neg_card_mul_logSucc_div_sub_klDivIndex_le_inv_mul_log_iUnion
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    {n : ℕ} (hn_pos : 0 < n)
    (h_inE : roundedTypeIndex P n ∈ E n) :
    -(Fintype.card α : ℝ) * (Real.log ((n : ℝ) + 1) / (n : ℝ))
        - klDivIndex (fun a => (roundedTypeIndex P n a : ℕ)) n Q
      ≤ (1 / (n : ℝ)) * Real.log
          (((Measure.pi (fun _ : Fin n => Q))
            (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) := by
  classical
  set c_n : α → ℕ := fun a => (roundedTypeIndex P n a : ℕ) with hc_n_def
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  -- T_{c_n} ⊆ ⋃ c ∈ E n, T_c (because c_n ∈ E n).
  have h_subset :
      (typeClassByCount (α := α) (n := n) c_n)
      ⊆ ⋃ c ∈ E n, typeClassByCount (α := α) (n := n) (fun a => (c a : ℕ)) := by
    intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨roundedTypeIndex P n, h_inE, hx⟩
  -- Q^n(T_{c_n}) ≥ (n+1)^{-|α|} exp(-n klDivIndex c_n n Q).
  have h_Qn_ge := typeClassByCount_Qn_ge Q hQpos hn_pos c_n
    (roundedTypeIndex_sum P hP_prob hP_nn n hn_pos)
  -- Q^n(⋃) ≥ Q^n(T_{c_n}).
  have h_union_ge : ((Measure.pi (fun _ : Fin n => Q))
        (typeClassByCount (α := α) c_n)).toReal
      ≤ ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
    apply ENNReal.toReal_mono
    · exact measure_ne_top _ _
    · exact measure_mono h_subset
  -- Combine: Q^n(⋃) ≥ (n+1)^{-|α|} exp(-n klDivIndex).
  have h_union_lb :
      (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
        * Real.exp (-((n : ℝ) * klDivIndex c_n n Q))
      ≤ ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal :=
    h_Qn_ge.trans h_union_ge
  -- Take log: log Q^n(⋃) ≥ -|α| log(n+1) - n klDivIndex.
  have h_lb_pos : (0 : ℝ) <
      (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
        * Real.exp (-((n : ℝ) * klDivIndex c_n n Q)) := by
    apply mul_pos
    · positivity
    · exact Real.exp_pos _
  have h_log_mono : Real.log
      ((((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
        * Real.exp (-((n : ℝ) * klDivIndex c_n n Q)))
      ≤ Real.log (((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) :=
    Real.log_le_log h_lb_pos h_union_lb
  -- Compute log of LHS.
  have h_log_lhs : Real.log
      ((((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
        * Real.exp (-((n : ℝ) * klDivIndex c_n n Q)))
      = -(Fintype.card α : ℝ) * Real.log ((n : ℝ) + 1) - (n : ℝ) * klDivIndex c_n n Q := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne']
    rw [Real.log_inv, Real.log_pow, Real.log_exp]
    ring
  rw [h_log_lhs] at h_log_mono
  -- Divide by n: -K log(n+1)/n - klDivIndex ≤ (1/n) log Q^n(⋃).
  have h_one_div_pos : 0 < 1 / (n : ℝ) := by positivity
  have h_mul := mul_le_mul_of_nonneg_left h_log_mono h_one_div_pos.le
  have h_lhs_eq : (1 / (n : ℝ)) * (-(Fintype.card α : ℝ) * Real.log ((n : ℝ) + 1)
        - (n : ℝ) * klDivIndex c_n n Q)
      = -(Fintype.card α : ℝ) * (Real.log ((n : ℝ) + 1) / (n : ℝ)) - klDivIndex c_n n Q := by
    field_simp
  rw [h_lhs_eq] at h_mul
  exact h_mul

omit [Nonempty α] [MeasurableSingletonClass α] in
theorem inv_mul_log_iUnion_typeClassByCount_le_zero
    (Q : Measure α) [IsProbabilityMeasure Q]
    (E : ∀ n, Finset (TypeCountIndex α n))
    {n : ℕ} (hn_pos : 0 < n) :
    (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) ≤ 0 := by
  classical
  have h_Qn_le_one : ((Measure.pi (fun _ : Fin n => Q))
      (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal ≤ 1 := by
    have := MeasureTheory.measureReal_le_one (μ := Measure.pi (fun _ : Fin n => Q))
      (s := ⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))
    simpa [MeasureTheory.measureReal_def] using this
  have h_one_div_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have h_log_le : Real.log
        (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) ≤ 0 := by
    apply Real.log_nonpos
    · exact ENNReal.toReal_nonneg
    · exact h_Qn_le_one
  exact mul_nonpos_of_nonneg_of_nonpos h_one_div_nn h_log_le

/-- **Sanov LDP lower bound (rounding sequence)**:
if `roundedTypeIndex P n ∈ E n` eventually, then
`liminf (1/n) log Q^n(⋃ c ∈ E n, T_c) ≥ -klDivSumForm_ofVec P (Q.real ∘ singleton)`. -/
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
    show g n ≤ f n
    rw [hg_def, hf_def, hK_def]
    exact neg_card_mul_logSucc_div_sub_klDivIndex_le_inv_mul_log_iUnion
      Q hQpos P hP_prob hP_nn E hn_pos h_inE
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
  -- Equivalently: f's eventual lower bounds are bounded. Since f ≥ log m (some fixed value),
  -- this holds.
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
    exact inv_mul_log_iUnion_typeClassByCount_le_zero Q E hn_pos
  have h_f_cobdd : Filter.IsCoboundedUnder (· ≥ ·) atTop f :=
    h_f_bdd_above.isCoboundedUnder_flip
  have h_liminf_le : liminf g atTop ≤ liminf f atTop :=
    Filter.liminf_le_liminf h_f_ge_g h_g_bdd_below h_f_cobdd
  rw [hg_tendsto.liminf_eq] at h_liminf_le
  exact h_liminf_le

end InformationTheory.Shannon
