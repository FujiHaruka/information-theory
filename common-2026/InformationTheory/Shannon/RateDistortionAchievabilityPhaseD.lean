import InformationTheory.Shannon.RateDistortionAchievabilityPhaseC
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Rate-distortion achievability — Phase D MVP (asymptotic decay)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)

Phase D-MVP supplies the *purely asymptotic* part of the rate-distortion
achievability argument: assuming the per-`n` bounds delivered by Phases B and C
(joint-typicality probability `≥ (1-η)·exp(-n·θ)`, codebook size
`M_n ≥ ⌈exp(n·R)⌉`, and the source-averaged failure bound
`(1 - p_typ)^M ≤ exp(-M · p_typ)`), the random-coding failure probability tends
to `0` provided `R > θ ≥ 0`.

Three lemmas:

* `ceil_exp_mul_exp_neg_tendsto_atTop` — `M_n · exp(-nθ) → ∞` when `R > θ`.
* `exp_neg_tendsto_zero_of_tendsto_atTop` — `f n → ∞ ⟹ exp(-f n) → 0`.
* `source_averaged_failure_tendsto_zero` — composition: a sequence sandwiched
  between `0` and `exp(-M_n · (1-η) · exp(-nθ))` tends to `0`.

## Phase D.5 — distortion decomposition

The distortion-typical event lets us decompose the block distortion of the
joint-typical encoder into two cases:

* `distortionMax d` — the worst-case single-letter distortion `(α × β)` value as a
  real number, an absolute upper bound on `blockDistortion`.
* `blockDistortion_le_distortionMax` — `blockDistortion ≤ distortionMax`.
* `blockDistortion_decompose` — case split: if `(x, y) ∈ distortionTypicalSet`,
  use the within-`δ` bound; otherwise use `distortionMax`.
* `source_avg_distortion_le_simpler` — codebook-fixed Bochner integral form of
  the decomposition: `∫ x, blockDistortion ∂P_X` is bounded by
  `(𝔼d + δ) + distortionMax · Pr(encoder fails distortion-typicality)`.

Entropy bridge (`θ = I(X;Y) + something`) and the random-codebook Fubini are
deferred to a later session.
-/

namespace InformationTheory.Shannon

open Filter Topology MeasureTheory
open InformationTheory.Shannon.ChannelCoding (Codebook jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **D.2 — `M_n · exp(-nθ) → ∞`** when `M_n ≥ ⌈exp(nR)⌉` and `R > θ`. -/
lemma ceil_exp_mul_exp_neg_tendsto_atTop
    {R θ : ℝ} (hRθ : θ < R) :
    Filter.Tendsto (fun n : ℕ =>
        (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) * Real.exp (-(n : ℝ) * θ))
      Filter.atTop Filter.atTop := by
  -- Lower bound: `(⌈exp(nR)⌉ : ℝ) · exp(-nθ) ≥ exp(nR) · exp(-nθ) = exp(n(R-θ))`.
  have h_diff_pos : 0 < R - θ := sub_pos.mpr hRθ
  -- `(n : ℝ) → ∞` as `n : ℕ → ∞`.
  have h_nat_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  -- `(n : ℝ) * (R - θ) → ∞`.
  have h_lin : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (R - θ)) Filter.atTop Filter.atTop :=
    h_nat_atTop.atTop_mul_const h_diff_pos
  -- `exp((n : ℝ) * (R - θ)) → ∞`.
  have h_exp_lin : Filter.Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (R - θ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp h_lin
  -- Squeeze: show `exp((n : ℝ) * (R - θ)) ≤ (⌈exp(nR)⌉ : ℝ) * exp(-nθ)` for all `n`.
  refine Filter.tendsto_atTop_mono (fun n => ?_) h_exp_lin
  have h_exp_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
  have h_exp_neg_pos : 0 < Real.exp (-(n : ℝ) * θ) := Real.exp_pos _
  -- Step 1: `exp(nR) ≤ (⌈exp(nR)⌉ : ℝ)`.
  have h_ceil : Real.exp ((n : ℝ) * R) ≤ (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) :=
    Nat.le_ceil _
  -- Step 2: multiply by `exp(-nθ) ≥ 0`.
  have h_mul : Real.exp ((n : ℝ) * R) * Real.exp (-(n : ℝ) * θ)
      ≤ (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) * Real.exp (-(n : ℝ) * θ) :=
    mul_le_mul_of_nonneg_right h_ceil h_exp_neg_pos.le
  -- Step 3: rewrite the lhs as `exp(n(R - θ))`.
  have h_eq : Real.exp ((n : ℝ) * R) * Real.exp (-(n : ℝ) * θ)
      = Real.exp ((n : ℝ) * (R - θ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_eq] at h_mul
  exact h_mul

/-- **D.3 — `exp(-f n) → 0`** when `f n → ∞`. -/
lemma exp_neg_tendsto_zero_of_tendsto_atTop
    {f : ℕ → ℝ} (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => Real.exp (-(f n))) Filter.atTop (𝓝 0) := by
  have h_neg : Filter.Tendsto (fun n => -(f n)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hf
  exact Real.tendsto_exp_atBot.comp h_neg


/-! ## Phase D.5 — distortion decomposition -/

section D5
variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- **D.5.1 — Maximum single-letter distortion** over the (finite, nonempty)
alphabet `α × β`, taken as a real number. Used as the worst-case bound for
`blockDistortion` on the encoder-fail event. -/
noncomputable def distortionMax (d : DistortionFn α β) : ℝ :=
  (Finset.univ : Finset (α × β)).sup' Finset.univ_nonempty
    (fun ab : α × β => ((d ab.1 ab.2 : NNReal) : ℝ))

/-- `distortionMax` is non-negative. -/
lemma distortionMax_nonneg (d : DistortionFn α β) : 0 ≤ distortionMax d := by
  unfold distortionMax
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  obtain ⟨b⟩ := (inferInstance : Nonempty β)
  have h_mem : (a, b) ∈ (Finset.univ : Finset (α × β)) := Finset.mem_univ _
  have h_le : ((d a b : NNReal) : ℝ)
      ≤ (Finset.univ : Finset (α × β)).sup' Finset.univ_nonempty
          (fun ab : α × β => ((d ab.1 ab.2 : NNReal) : ℝ)) :=
    Finset.le_sup' (f := fun ab : α × β => ((d ab.1 ab.2 : NNReal) : ℝ)) h_mem
  exact le_trans (NNReal.coe_nonneg _) h_le

/-- Per-symbol bound: each `((d a b : NNReal) : ℝ) ≤ distortionMax d`. -/
lemma distortion_le_distortionMax (d : DistortionFn α β) (a : α) (b : β) :
    ((d a b : NNReal) : ℝ) ≤ distortionMax d := by
  unfold distortionMax
  exact Finset.le_sup' (f := fun ab : α × β => ((d ab.1 ab.2 : NNReal) : ℝ))
    (Finset.mem_univ (a, b))

/-- **D.5.1 main** — `blockDistortion d n x y ≤ distortionMax d`. -/
lemma blockDistortion_le_distortionMax
    (d : DistortionFn α β) (n : ℕ) (x : Fin n → α) (y : Fin n → β) :
    blockDistortion d n x y ≤ distortionMax d := by
  unfold blockDistortion
  by_cases hn : n = 0
  · subst hn
    simp
    exact distortionMax_nonneg d
  · have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h_sum_le :
        ∑ i, ((d (x i) (y i) : NNReal) : ℝ)
          ≤ (n : ℝ) * distortionMax d := by
      have h_each : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          ((d (x i) (y i) : NNReal) : ℝ) ≤ distortionMax d :=
        fun i _ => distortion_le_distortionMax d (x i) (y i)
      have h_sum := Finset.sum_le_sum h_each
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h_sum
      have h_nsmul : (n : ℕ) • distortionMax d = (n : ℝ) * distortionMax d := by
        rw [nsmul_eq_mul]
      rw [h_nsmul] at h_sum
      exact h_sum
    have h_inv_nn : 0 ≤ (1 / (n : ℝ)) := by positivity
    have h_mul_le :
        (1 / (n : ℝ)) * ∑ i, ((d (x i) (y i) : NNReal) : ℝ)
          ≤ (1 / (n : ℝ)) * ((n : ℝ) * distortionMax d) :=
      mul_le_mul_of_nonneg_left h_sum_le h_inv_nn
    have h_simp : (1 / (n : ℝ)) * ((n : ℝ) * distortionMax d) = distortionMax d := by
      field_simp
    rw [h_simp] at h_mul_le
    exact h_mul_le

/-- `expectedJointDistortion` is non-negative (integrand is `NNReal`-valued). -/
lemma expectedJointDistortion_nonneg
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (d : DistortionFn α β) :
    0 ≤ expectedJointDistortion μ X Y d := by
  unfold expectedJointDistortion
  exact integral_nonneg (fun _ => NNReal.coe_nonneg _)


/-- **D.5.3 (simplified form) — codebook-fixed average distortion decomposition.**

For a fixed deterministic codebook `c : Codebook M n β` and the joint-typical
lossy encoder, the source-averaged block distortion satisfies

```
∫ x, blockDistortion d n x (c (encoder x)) ∂P_X
  ≤ (𝔼[d(X_0, Y_0)] + δ)
    + distortionMax d
      · P_X { x | (x, c (encoder x)) ∉ distortionTypicalSet }
```

The failure event is stated **encoder-side**: the encoder's chosen codeword is
not distortion-typical. Compared to the existence form
`{ x | ∃ m, (x, c m) ∈ distortionTypicalSet }`, this version is what the proof
naturally delivers and is no harder for Phase E to dominate by the existence
form (any encoder failure implies absence of any distortion-typical match for
the encoder's choice; Phase E will bound the existence-form failure separately).

`hδ : 0 ≤ δ` is used to ensure `Edδ := 𝔼[d] + δ ≥ 0`, simplifying the
decomposition `dMax ≤ Edδ + dMax * 1`. -/
@[entry_point]
theorem source_avg_distortion_le_simpler
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) {M n : ℕ} (hM : 0 < M) (ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (c : Codebook M n β)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X] :
    ∫ x, blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x)) ∂P_X
      ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ)
        + distortionMax d *
          P_X.real
            { x | (x, c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
                    ∉ distortionTypicalSet μ Xs Ys d n ε δ } := by
  classical
  -- Notation
  set Edδ : ℝ := expectedJointDistortion μ (Xs 0) (Ys 0) d + δ with hEdδ_def
  set dMax : ℝ := distortionMax d with hdMax_def
  set B : Set (Fin n → α) :=
      { x | (x, c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
              ∉ distortionTypicalSet μ Xs Ys d n ε δ } with hB_def
  -- Non-negativity facts
  have h_Ed_nn : 0 ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d :=
    expectedJointDistortion_nonneg μ (Xs 0) (Ys 0) d
  have h_Edδ_nn : 0 ≤ Edδ := by rw [hEdδ_def]; linarith
  have h_dMax_nn : 0 ≤ dMax := distortionMax_nonneg d
  -- Measurability of `B` (subset of finite ambient `Fin n → α`).
  have h_B_meas : MeasurableSet B := (Set.toFinite _).measurableSet
  -- Pointwise bound:
  --   blockDistortion ≤ Edδ + dMax * (B.indicator (fun _ => 1) x).
  have h_pointwise : ∀ x : Fin n → α,
      blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
        ≤ Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x) := by
    intro x
    by_cases hxB : x ∈ B
    · -- Encoder's choice not in distortionTypicalSet ⇒ blockDistortion ≤ dMax.
      have h_bd :
          blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
            ≤ dMax :=
        blockDistortion_le_distortionMax d n x _
      have h_ind : B.indicator (fun _ : Fin n → α => (1 : ℝ)) x = 1 :=
        Set.indicator_of_mem hxB _
      calc blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
          ≤ dMax := h_bd
        _ = 0 + dMax * 1 := by ring
        _ ≤ Edδ + dMax * 1 := by linarith
        _ = Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x) := by rw [h_ind]
    · -- Encoder's choice IS in distortionTypicalSet ⇒ blockDistortion ≤ Edδ.
      have hxB' : (x, c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
          ∈ distortionTypicalSet μ Xs Ys d n ε δ := by
        rw [hB_def, Set.mem_setOf_eq, not_not] at hxB
        exact hxB
      have h_bd :
          blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
            ≤ Edδ :=
        blockDistortion_le_of_mem_distortionTypicalSet μ Xs Ys d n ε δ hxB'
      have h_ind : B.indicator (fun _ : Fin n → α => (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem hxB _
      calc blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
          ≤ Edδ := h_bd
        _ = Edδ + dMax * 0 := by ring
        _ = Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x) := by rw [h_ind]
  -- Step 2: integrate the pointwise bound over `P_X`.
  -- LHS / RHS measurability for `integral_mono`.
  have h_meas_f : Measurable
      (fun x : Fin n → α =>
        blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x)) ) :=
    measurable_of_finite _
  have h_meas_g : Measurable
      (fun x : Fin n → α => Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x)) :=
    measurable_of_finite _
  -- Integrability: both functions are bounded (LHS by dMax, RHS by Edδ + dMax)
  -- on a probability measure ⇒ integrable.
  have h_f_le : ∀ x, ‖blockDistortion d n x
        (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))‖ ≤ dMax := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (blockDistortion_nonneg d n x _)]
    exact blockDistortion_le_distortionMax d n x _
  have h_int_f : Integrable
      (fun x : Fin n → α =>
        blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))) P_X := by
    refine Integrable.mono' (g := fun _ => dMax) (integrable_const dMax)
      h_meas_f.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall h_f_le
  have h_int_g : Integrable
      (fun x : Fin n → α => Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x)) P_X := by
    refine Integrable.mono' (g := fun _ => Edδ + dMax) (integrable_const (Edδ + dMax))
      h_meas_g.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_ind_le : (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ 1 := by
      by_cases hxB : x ∈ B
      · rw [Set.indicator_of_mem hxB]
      · rw [Set.indicator_of_notMem hxB]; linarith
    have h_ind_nn : 0 ≤ (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have h_val_le : Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x)
        ≤ Edδ + dMax := by
      have h_inner :
          dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ dMax := by
        calc dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x)
            ≤ dMax * 1 := mul_le_mul_of_nonneg_left h_ind_le h_dMax_nn
          _ = dMax := by ring
      linarith
    have h_val_nn : 0 ≤ Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
      add_nonneg h_Edδ_nn (mul_nonneg h_dMax_nn h_ind_nn)
    rw [Real.norm_eq_abs, abs_of_nonneg h_val_nn]
    exact h_val_le
  -- Monotone integral.
  have h_int_mono :
      ∫ x, blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x)) ∂P_X
        ≤ ∫ x, Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ∂P_X :=
    integral_mono h_int_f h_int_g h_pointwise
  -- Evaluate the RHS integral.
  have h_int_const : ∫ _x : Fin n → α, Edδ ∂P_X = Edδ := by
    rw [integral_const]; simp
  have h_int_indicator_const :
      ∫ x : Fin n → α, dMax * (B.indicator (fun _ => (1 : ℝ)) x) ∂P_X
        = dMax * P_X.real B := by
    have h_ind_eq :
        (fun x : Fin n → α => dMax * (B.indicator (fun _ => (1 : ℝ)) x))
          = B.indicator (fun _ : Fin n → α => dMax) := by
      funext x
      by_cases hxB : x ∈ B
      · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB]; ring
      · rw [Set.indicator_of_notMem hxB, Set.indicator_of_notMem hxB]; ring
    rw [h_ind_eq, integral_indicator_const dMax h_B_meas]
    rw [smul_eq_mul]; ring
  have h_int_split :
      ∫ x, Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ∂P_X
        = Edδ + dMax * P_X.real B := by
    have h_const_int : Integrable (fun _ : Fin n → α => Edδ) P_X := integrable_const Edδ
    have h_ind_int : Integrable
        (fun x : Fin n → α => dMax * (B.indicator (fun _ => (1 : ℝ)) x)) P_X := by
      have h_meas' : Measurable
          (fun x : Fin n → α => dMax * (B.indicator (fun _ => (1 : ℝ)) x)) :=
        measurable_of_finite _
      refine Integrable.mono' (g := fun _ => dMax) (integrable_const dMax)
        h_meas'.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h_ind_le : (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ 1 := by
        by_cases hxB : x ∈ B
        · rw [Set.indicator_of_mem hxB]
        · rw [Set.indicator_of_notMem hxB]; linarith
      have h_ind_nn : 0 ≤ (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have h_val_nn : 0 ≤ dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
        mul_nonneg h_dMax_nn h_ind_nn
      have h_val_le : dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ dMax := by
        calc dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x)
            ≤ dMax * 1 := mul_le_mul_of_nonneg_left h_ind_le h_dMax_nn
          _ = dMax := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg h_val_nn]
      exact h_val_le
    rw [integral_add h_const_int h_ind_int, h_int_const, h_int_indicator_const]
  -- Combine.
  rw [h_int_split] at h_int_mono
  exact h_int_mono

end D5

end InformationTheory.Shannon
