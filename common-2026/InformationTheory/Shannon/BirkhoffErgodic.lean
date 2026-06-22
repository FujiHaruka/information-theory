import InformationTheory.Meta.EntryPoint
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Birkhoff individual ergodic theorem via Garsia's maximal ergodic inequality

This file proves the **Birkhoff individual ergodic theorem** (Petersen
*Ergodic Theory* Thm 2.3, Walters *An Introduction to Ergodic Theory*
Thm 1.14, 1931):

> Let `T : Ω → Ω` be a measure-preserving ergodic transformation of a
> probability space `(Ω, μ)`, and let `f : Ω → ℝ` be integrable. Then
> the time averages
>
>     A_n ω := (∑_{i=0}^{n} f (T^[i] ω)) / (n + 1)
>
> converge almost everywhere to the spatial mean `∫ f dμ`.

## Strategy: Garsia (1965) — maximal ergodic inequality + sandwich

The proof uses Garsia's elementary proof of the **maximal ergodic
inequality**, followed by a sandwich argument bounding both
`limsup A_n` and `liminf A_n` by `∫f dμ`.

> **Historical note.** A previous iteration of this file attempted the
> backward-martingale Hopf identity route (Williams §14.4). That route
> is only valid for **i.i.d. processes** and is **mathematically false**
> for general measure-preserving ergodic systems: the cyclic system on
> `{0, 1, 2}` with `T(x) = (x + 1) mod 3` and `f(x) = x` is a concrete
> counter-example to the would-be exchangeability lemma
> `μ[f ∘ T | σ(S_3, S_4, …)] =ᵐ μ[f | σ(S_3, S_4, …)]`. The Petersen
> Thm 2.2 reference for the "Hopf identity" was conflated with the
> (different) Hopf maximal ergodic inequality used here.

## Proof structure

* **§1 Definitions** — `birkhoffAverageReal`, `birkhoffPartialSum`,
  `maxPartialSum` (running max `M_n := max(S_0, S_1, …, S_n)`).
* **§2 Integral preservation** — `∫ A_n dμ = ∫ f dμ`.
* **§3 Birkhoff sum recursion** — `S_{k+1}(ω) = f(ω) + S_k(T ω)`,
  `A_n(T ω) = ((n+2)·A_{n+1}(ω) - f(ω))/(n+1)`.
* **§4 Garsia maximal ergodic inequality** — `∫_{M_n > 0} f dμ ≥ 0`.
* **§5 Sandwich** — `limsup A_n ≤ ∫f` and `liminf A_n ≥ ∫f` a.e.
* **§6 Main theorem** — `birkhoff_ergodic_ae`.

## Main results

* `birkhoffAverageReal_comp_T` — recursion for the time average.
* `integral_birkhoffAverageReal_eq` — `∫ A_n dμ = ∫ f dμ`.
* `birkhoffPartialSum_succ_eq` — `S_{k+1}(ω) = f(ω) + S_k(T ω)`.
* `maxPartialSum_sub_comp_T_le_indicator` — Garsia pointwise
  `M_n(ω) - M_n(T ω) ≤ 1_{M_n > 0}(ω) · f(ω)`.
* `maximal_ergodic_inequality` — `∫_{M_n > 0} f dμ ≥ 0`.
* `birkhoff_ergodic_ae_of_limit` — γ.3 + γ.4 hypothesis form.
* `birkhoff_ergodic_ae` — **main theorem**.
-/

namespace InformationTheory.Shannon

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-! ## §1 Definitions -/

/-- Birkhoff time average with `n + 1` terms.

`birkhoffAverageReal T f n ω := (∑_{i=0}^{n} f (T^[i] ω)) / (n + 1)`.

The `n + 1` denominator side-steps the `n = 0` division issue; this is
the sequence we want to converge to `∫ f dμ` under Birkhoff's theorem. -/
noncomputable def birkhoffAverageReal (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / (n + 1 : ℝ)

/-- Partial Birkhoff sum with `k` terms.
`birkhoffPartialSum T f k ω := ∑_{i=0}^{k-1} f (T^[i] ω)`. -/
noncomputable def birkhoffPartialSum (T : Ω → Ω) (f : Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range k, f (T^[i] ω)

/-- Average and partial sum are related: `A_n = S_{n+1} / (n + 1)`. -/
lemma birkhoffAverageReal_eq_partialSum_div (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffAverageReal T f n ω = birkhoffPartialSum T f (n + 1) ω / (n + 1 : ℝ) := rfl

@[simp] lemma birkhoffPartialSum_zero (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    birkhoffPartialSum T f 0 ω = 0 := by
  simp [birkhoffPartialSum]

/-- Partial sums are measurable when `T` and `f` are. -/
lemma birkhoffPartialSum_measurable {T : Ω → Ω} (hT : Measurable T)
    {f : Ω → ℝ} (hf : Measurable f) (k : ℕ) :
    Measurable (birkhoffPartialSum T f k) := by
  unfold birkhoffPartialSum
  refine Finset.measurable_sum _ (fun i _ ↦ ?_)
  exact hf.comp (hT.iterate i)

/-- Running maximum of Birkhoff partial sums:
`maxPartialSum T f n ω = max{S_0(ω), S_1(ω), …, S_n(ω)}`.

Since `S_0 = 0`, this satisfies `maxPartialSum T f n ω ≥ 0`. -/
noncomputable def maxPartialSum (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => max (maxPartialSum T f n ω) (birkhoffPartialSum T f (n+1) ω)

@[simp] lemma maxPartialSum_zero (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    maxPartialSum T f 0 ω = 0 := rfl

lemma maxPartialSum_succ (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxPartialSum T f (n + 1) ω
      = max (maxPartialSum T f n ω) (birkhoffPartialSum T f (n + 1) ω) := rfl

lemma maxPartialSum_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ maxPartialSum T f n ω := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih => rw [maxPartialSum_succ]; exact le_max_of_le_left ih

lemma maxPartialSum_measurable {T : Ω → Ω} (hT : Measurable T)
    {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (maxPartialSum T f n) := by
  induction n with
  | zero =>
    show Measurable (fun _ : Ω ↦ (0 : ℝ))
    exact measurable_const
  | succ n ih =>
    show Measurable (fun ω ↦ max (maxPartialSum T f n ω) (birkhoffPartialSum T f (n + 1) ω))
    exact ih.max (birkhoffPartialSum_measurable hT hf (n + 1))

lemma birkhoffPartialSum_le_maxPartialSum (T : Ω → Ω) (f : Ω → ℝ)
    (n : ℕ) {k : ℕ} (hk : k ≤ n) (ω : Ω) :
    birkhoffPartialSum T f k ω ≤ maxPartialSum T f n ω := by
  induction n with
  | zero =>
    have hk_zero : k = 0 := Nat.le_zero.mp hk
    rw [hk_zero, birkhoffPartialSum_zero, maxPartialSum_zero]
  | succ n ih =>
    rw [maxPartialSum_succ]
    by_cases hk' : k ≤ n
    · exact le_max_of_le_left (ih hk')
    · have hk' : n + 1 ≤ k := Nat.lt_iff_add_one_le.mp (Nat.not_le.mp hk')
      have hk_eq : k = n + 1 := Nat.le_antisymm hk hk'
      rw [hk_eq]
      exact le_max_right _ _

/-! ## §2 Integral preservation -/

/-- Each term `f ∘ T^[i]` has the same integral as `f`. -/
@[entry_point]
lemma integral_comp_iterate_eq (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (i : ℕ) :
    ∫ ω, f (T^[i] ω) ∂μ = ∫ ω, f ω ∂μ := by
  have hTi : MeasurePreserving (T^[i]) μ μ := hT.iterate i
  have h_map : Measure.map (T^[i]) μ = μ := hTi.map_eq
  have hf_strong_map : AEStronglyMeasurable f (Measure.map (T^[i]) μ) := by
    rw [h_map]; exact hf.aestronglyMeasurable
  have h_int_map :
      ∫ y, f y ∂Measure.map (T^[i]) μ = ∫ x, f (T^[i] x) ∂μ :=
    MeasureTheory.integral_map hTi.aemeasurable hf_strong_map
  rw [h_map] at h_int_map
  exact h_int_map.symm

/-- Integral of the `(n+1)`-term Birkhoff average equals `∫ f`. -/
@[entry_point]
lemma integral_birkhoffAverageReal_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (n : ℕ) :
    ∫ ω, birkhoffAverageReal T f n ω ∂μ = ∫ ω, f ω ∂μ := by
  classical
  unfold birkhoffAverageReal
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  have h1 :
      ∫ ω, (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / ((n : ℝ) + 1) ∂μ
        = (∫ ω, ∑ i ∈ Finset.range (n + 1), f (T^[i] ω) ∂μ) / ((n : ℝ) + 1) := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
  rw [h1]
  have h_int_each : ∀ i ∈ Finset.range (n + 1),
      Integrable (fun ω ↦ f (T^[i] ω)) μ := by
    intro i _
    exact (hT.iterate i).integrable_comp_of_integrable hf
  rw [integral_finsetSum _ h_int_each]
  have h_each : ∀ i ∈ Finset.range (n + 1),
      ∫ ω, f (T^[i] ω) ∂μ = ∫ ω, f ω ∂μ := by
    intro i _
    exact integral_comp_iterate_eq μ hT hf i
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Nat.cast_add, Nat.cast_one]
  field_simp

/-! ## §3 Birkhoff sum recursion -/

/-- Recursion `S_{k+1}(ω) = f(ω) + S_k(T ω)`. -/
lemma birkhoffPartialSum_succ_eq (T : Ω → Ω) (f : Ω → ℝ) (k : ℕ) (ω : Ω) :
    birkhoffPartialSum T f (k + 1) ω = f ω + birkhoffPartialSum T f k (T ω) := by
  classical
  unfold birkhoffPartialSum
  rw [Finset.sum_range_succ' (fun i ↦ f (T^[i] ω)) k, add_comm]
  refine congr_arg₂ (· + ·) rfl ?_
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  exact congr_arg f (Function.iterate_succ_apply T i ω)

/-- Algebraic recursion for time averages:
`A_n(T ω) = ((n+2) · A_{n+1}(ω) - f(ω)) / (n+1)`. -/
lemma birkhoffAverageReal_comp_T (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffAverageReal T f n (T ω)
      = ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (n + 1) := by
  classical
  unfold birkhoffAverageReal
  have h_iter : ∀ i, T^[i] (T ω) = T^[i + 1] ω := fun i ↦ by
    rw [show T^[i] (T ω) = (T^[i] ∘ T) ω from rfl]
    rw [show (T^[i] ∘ T) = T^[i + 1] from (Function.iterate_succ T i).symm]
  have h_lhs_sum :
      (∑ i ∈ Finset.range (n + 1), f (T^[i] (T ω)))
        = (∑ i ∈ Finset.range (n + 1), f (T^[i + 1] ω)) := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [h_iter i]
  have h_reindex :
      (∑ i ∈ Finset.range (n + 1), f (T^[i + 1] ω))
        = (∑ j ∈ Finset.range (n + 2), f (T^[j] ω)) - f (T^[0] ω) := by
    rw [Finset.sum_range_succ' (fun j ↦ f (T^[j] ω)) (n + 1)]
    ring
  have h_T0 : T^[0] ω = ω := rfl
  rw [h_lhs_sum, h_reindex, h_T0]
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn2_ne : ((n : ℝ) + 2) ≠ 0 := ne_of_gt hn2_pos
  rw [show ((↑(n + 1) : ℝ) + 1) = (n : ℝ) + 2 from by push_cast; ring]
  field_simp

/-! ## §4 Garsia maximal ergodic inequality -/

/-- Bound `M_n ≤ ∑_{i < n} |f ∘ T^[i]|`, used for integrability. -/
lemma maxPartialSum_le_sum_abs (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxPartialSum T f n ω ≤ ∑ i ∈ Finset.range n, |f (T^[i] ω)| := by
  induction n with
  | zero => simp [maxPartialSum_zero]
  | succ n ih =>
    rw [maxPartialSum_succ]
    refine max_le ?_ ?_
    · refine ih.trans ?_
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · unfold birkhoffPartialSum
      exact Finset.sum_le_sum (fun i _ ↦ le_abs_self _)

/-- `M_n` is integrable when `f` is, in finite measure. -/
lemma maxPartialSum_integrable {μ : Measure Ω}
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (hf_int : Integrable f μ) (n : ℕ) :
    Integrable (maxPartialSum T f n) μ := by
  have h_M_meas : Measurable (maxPartialSum T f n) :=
    maxPartialSum_measurable hT.measurable hf n
  have h_RHS_int : Integrable (fun ω ↦ ∑ i ∈ Finset.range n, |f (T^[i] ω)|) μ := by
    refine integrable_finsetSum _ (fun i _ ↦ ?_)
    exact ((hT.iterate i).integrable_comp_of_integrable hf_int).abs
  refine h_RHS_int.mono h_M_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (maxPartialSum_nonneg T f n ω)]
  refine (maxPartialSum_le_sum_abs T f n ω).trans ?_
  exact le_abs_self _

/-- Existence of an index `k ∈ {1, …, n}` achieving the running max
when the max is strictly positive. -/
lemma exists_pos_index_attaining_max (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω)
    (h_pos : 0 < maxPartialSum T f n ω) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ birkhoffPartialSum T f k ω = maxPartialSum T f n ω := by
  induction n with
  | zero =>
    rw [maxPartialSum_zero] at h_pos
    exact absurd h_pos (lt_irrefl 0)
  | succ n ih =>
    rw [maxPartialSum_succ]
    rw [maxPartialSum_succ] at h_pos
    by_cases h_cmp : maxPartialSum T f n ω ≤ birkhoffPartialSum T f (n + 1) ω
    · have h_max : max (maxPartialSum T f n ω) (birkhoffPartialSum T f (n + 1) ω)
          = birkhoffPartialSum T f (n + 1) ω := max_eq_right h_cmp
      refine ⟨n + 1, by omega, le_refl _, h_max.symm⟩
    · have h_cmp : birkhoffPartialSum T f (n + 1) ω < maxPartialSum T f n ω := not_le.mp h_cmp
      have h_max : max (maxPartialSum T f n ω) (birkhoffPartialSum T f (n + 1) ω)
          = maxPartialSum T f n ω := max_eq_left h_cmp.le
      rw [h_max] at h_pos
      obtain ⟨k, hk1, hkn, hk_eq⟩ := ih h_pos
      refine ⟨k, hk1, hkn.trans n.le_succ, ?_⟩
      rw [h_max, hk_eq]

/-- **Garsia pointwise inequality** (key step for the maximal ergodic
inequality): for all `ω : Ω`,

  M_n(ω) - M_n(T ω) ≤ 1_{M_n > 0}(ω) · f(ω).

Proof: on `{M_n > 0}`, picking `k* ∈ {1, …, n}` with `S_{k*}(ω) = M_n(ω)`
and using `S_{k*}(ω) = f(ω) + S_{k* - 1}(T ω)` with
`S_{k* - 1}(T ω) ≤ M_n(T ω)` gives `f(ω) ≥ M_n(ω) - M_n(T ω)`.
On `{M_n = 0}` (the complement), `M_n(ω) - M_n(T ω) = -M_n(T ω) ≤ 0`. -/
lemma maxPartialSum_sub_comp_T_le_indicator
    (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxPartialSum T f n ω - maxPartialSum T f n (T ω)
      ≤ {ω | 0 < maxPartialSum T f n ω}.indicator f ω := by
  by_cases h_pos : 0 < maxPartialSum T f n ω
  · have h_mem : ω ∈ {ω' | 0 < maxPartialSum T f n ω'} := h_pos
    rw [Set.indicator_of_mem h_mem]
    obtain ⟨k, hk1, hkn, hk_eq⟩ := exists_pos_index_attaining_max T f n ω h_pos
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
      ⟨k - 1, (Nat.succ_pred_eq_of_pos hk1).symm⟩
    have hk'_le_n : k' ≤ n := by omega
    have hS_succ : birkhoffPartialSum T f (k' + 1) ω = f ω + birkhoffPartialSum T f k' (T ω) :=
      birkhoffPartialSum_succ_eq T f k' ω
    have hS_le_M : birkhoffPartialSum T f k' (T ω) ≤ maxPartialSum T f n (T ω) :=
      birkhoffPartialSum_le_maxPartialSum T f n hk'_le_n (T ω)
    linarith
  · have h_nmem : ω ∉ {ω' | 0 < maxPartialSum T f n ω'} := h_pos
    rw [Set.indicator_of_notMem h_nmem]
    have h_pos : maxPartialSum T f n ω ≤ 0 := not_lt.mp h_pos
    have h_zero : maxPartialSum T f n ω = 0 :=
      le_antisymm h_pos (maxPartialSum_nonneg T f n ω)
    rw [h_zero]
    linarith [maxPartialSum_nonneg T f n (T ω)]

/-- **Maximal ergodic inequality** (Garsia 1965). For `T : Ω → Ω`
measure-preserving on a probability/finite-measure space and `f : Ω → ℝ`
integrable, for every `n : ℕ`,

  ∫_{ω : 0 < maxPartialSum T f n ω} f dμ ≥ 0.

Proof: integrate the Garsia pointwise inequality
`M_n(ω) - M_n(T ω) ≤ 1_{M_n > 0}(ω) · f(ω)` over `μ`, and use
`∫ M_n ∘ T dμ = ∫ M_n dμ` (measure preservation). -/
@[entry_point]
theorem maximal_ergodic_inequality {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (hf_int : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < maxPartialSum T f n ω}, f ω ∂μ := by
  set M := maxPartialSum T f n with hM_def
  set A := {ω | 0 < maxPartialSum T f n ω} with hA_def
  have hM_meas : Measurable M := maxPartialSum_measurable hT.measurable hf n
  have hA_meas : MeasurableSet A := hM_meas measurableSet_Ioi
  have hM_int : Integrable M μ := maxPartialSum_integrable hT hf hf_int n
  have hM_compT_int : Integrable (fun ω ↦ M (T ω)) μ :=
    hT.integrable_comp hM_int.aestronglyMeasurable |>.mpr hM_int
  -- Garsia pointwise inequality.
  have h_ptwise : ∀ ω, M ω - M (T ω) ≤ A.indicator f ω := fun ω ↦
    maxPartialSum_sub_comp_T_le_indicator T f n ω
  -- Indicator integral equals set integral.
  have h_indicator_int : Integrable (A.indicator f) μ :=
    hf_int.indicator hA_meas
  have h_indicator_eq : ∫ ω, A.indicator f ω ∂μ = ∫ ω in A, f ω ∂μ :=
    integral_indicator hA_meas
  -- Integrate pointwise inequality.
  have h_int_le : ∫ ω, (M ω - M (T ω)) ∂μ ≤ ∫ ω, A.indicator f ω ∂μ :=
    integral_mono_ae (hM_int.sub hM_compT_int) h_indicator_int
      (Filter.Eventually.of_forall h_ptwise)
  -- Measure preservation: ∫ M ∘ T = ∫ M.
  have h_int_eq : ∫ ω, M (T ω) ∂μ = ∫ ω, M ω ∂μ := by
    have hM_smeas : AEStronglyMeasurable M μ := hM_meas.aestronglyMeasurable
    have := MeasureTheory.integral_map hT.aemeasurable
      (by rw [hT.map_eq]; exact hM_smeas)
    rw [hT.map_eq] at this
    exact this.symm
  rw [integral_sub hM_int hM_compT_int, h_int_eq, sub_self] at h_int_le
  rw [← h_indicator_eq]
  exact h_int_le

/-! ## §5 Sandwich

The sandwich proof shows that for ergodic `T` and integrable `f`,
both `limsup A_n ≤ ∫f` and `liminf A_n ≥ ∫f` hold a.e., implying
`A_n → ∫f` a.e.

The argument: fix `ε > 0` and let `α := ∫f dμ`. Define
`A_ε := {ω : limsup A_n(f, ω) > α + ε}`. Then `A_ε` is T-invariant
(via the recursion `A_n(T ω) = …`). For ergodic `T`, `μ(A_ε) ∈ {0, 1}`.
Suppose `μ(A_ε) = 1`. For `g := f - α - ε` (so `∫g = -ε < 0`), apply
the maximal ergodic inequality at each `n` to get
`∫_{M_n^g > 0} g dμ ≥ 0`. The sets `{M_n^g > 0}` are monotone in `n`
and exhaust `B := {sup_n S_n(g) > 0} ⊇ A_ε`. By DCT,
`∫_B g dμ = lim ∫_{M_n^g > 0} g dμ ≥ 0`. But `B ⊇ A_ε` (full measure)
gives `∫_B g dμ = ∫_Ω g dμ = -ε < 0`. Contradiction. Hence `μ(A_ε) = 0`. -/

section Sandwich

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
  {T : Ω → Ω}

/-- For ergodic `T` and integrable `g` with `∫g dμ < 0`, the
"infinitely often positive partial sum" set
`{ω | ∀ n, ∃ N ≥ n, S_N(g, ω) > 0}` cannot have full measure.

Proof: that set is contained in
`B := ⋃_n {ω | maxPartialSum T g n ω > 0}` (= {ω | ∃ N ≥ 1, S_N(g, ω) > 0}).
By the maximal ergodic inequality, `∫_{M_n > 0} g dμ ≥ 0` for each `n`.
By dominated convergence, `∫_B g dμ = lim_n ∫_{M_n > 0} g dμ ≥ 0`.
If the "infinitely often" set has full measure, so does `B`, hence
`∫_B g dμ = ∫_Ω g dμ < 0`. Contradiction.

(Ergodicity is not actually needed here; the contradiction is direct
from the maximal ergodic inequality + DCT.) -/
lemma birkhoff_neg_mean_sup_null (hT : MeasurePreserving T μ μ) (_hT_erg : Ergodic T μ)
    {g : Ω → ℝ} (hg : Measurable g) (hg_int : Integrable g μ)
    (hg_neg : ∫ ω, g ω ∂μ < 0)
    (hA_full : μ {ω | ∀ n : ℕ, ∃ N ≥ n,
      birkhoffPartialSum T g N ω > 0} = μ Set.univ) :
    False := by
  classical
  -- B_n := {ω | maxPartialSum T g n ω > 0}, monotone in n, ⋃ = B_∞.
  set B : ℕ → Set Ω := fun n ↦ {ω | 0 < maxPartialSum T g n ω} with hB_def
  set B_inf : Set Ω := ⋃ n, B n with hB_inf_def
  have hB_meas : ∀ n, MeasurableSet (B n) := fun n ↦
    (maxPartialSum_measurable hT.measurable hg n) measurableSet_Ioi
  have hB_inf_meas : MeasurableSet B_inf := MeasurableSet.iUnion hB_meas
  -- B_n monotone non-decreasing.
  have hB_mono : Monotone B := by
    intro m n hmn ω hω
    -- ω ∈ B m means M_m(ω) > 0. Show M_n(ω) > 0.
    show 0 < maxPartialSum T g n ω
    have hkn : ∃ k ≤ m, 1 ≤ k ∧ birkhoffPartialSum T g k ω = maxPartialSum T g m ω := by
      obtain ⟨k, hk1, hkm, hk_eq⟩ := exists_pos_index_attaining_max T g m ω hω
      exact ⟨k, hkm, hk1, hk_eq⟩
    obtain ⟨k, hkm, _hk1, hk_eq⟩ := hkn
    have hkn' : k ≤ n := hkm.trans hmn
    calc (0 : ℝ) < maxPartialSum T g m ω := hω
      _ = birkhoffPartialSum T g k ω := hk_eq.symm
      _ ≤ maxPartialSum T g n ω := birkhoffPartialSum_le_maxPartialSum T g n hkn' ω
  -- Infinitely-often set A ⊆ B_inf.
  set A : Set Ω := {ω | ∀ n : ℕ, ∃ N ≥ n, 0 < birkhoffPartialSum T g N ω} with hA_def
  have hA_sub : A ⊆ B_inf := by
    intro ω hω
    obtain ⟨N, hN1, hN_pos⟩ := hω 1
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    -- M_N(ω) ≥ S_N(ω) > 0.
    show 0 < maxPartialSum T g N ω
    exact lt_of_lt_of_le hN_pos (birkhoffPartialSum_le_maxPartialSum T g N le_rfl ω)
  -- μ(B_inf) = 1 from μ(A) = 1.
  have hμA : μ A = 1 := by
    rw [hA_full]
    exact measure_univ
  have hμB_inf : μ B_inf = 1 := by
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = μ A := hμA.symm
      _ ≤ μ B_inf := measure_mono hA_sub
  -- DCT: ∫_{B n} g → ∫_{B_inf} g.
  -- Set h_n := g · 1_{B n}, h_∞ := g · 1_{B_inf}.
  set h : ℕ → Ω → ℝ := fun n ↦ (B n).indicator g with hh_def
  set h_inf : Ω → ℝ := B_inf.indicator g with hh_inf_def
  have h_ptwise_lim : ∀ ω, Tendsto (fun n ↦ h n ω) atTop (𝓝 (h_inf ω)) := by
    intro ω
    by_cases h_in : ω ∈ B_inf
    · obtain ⟨k, hk⟩ : ∃ k, ω ∈ B k := Set.mem_iUnion.mp h_in
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop k] with n hn
      show h_inf ω = h n ω
      change B_inf.indicator g ω = (B n).indicator g ω
      rw [Set.indicator_of_mem h_in, Set.indicator_of_mem (hB_mono hn hk)]
    · have h_const : ∀ n, h n ω = h_inf ω := fun n ↦
        show (B n).indicator g ω = B_inf.indicator g ω by
          rw [Set.indicator_of_notMem (fun hin ↦ h_in (Set.mem_iUnion.mpr ⟨n, hin⟩)),
              Set.indicator_of_notMem h_in]
      have h_funext : (fun n ↦ h n ω) = (fun _ : ℕ ↦ h_inf ω) := funext h_const
      rw [h_funext]
      exact tendsto_const_nhds
  have h_dom : ∀ n ω, ‖h n ω‖ ≤ ‖g ω‖ := by
    intro n ω
    simp only [hh_def, Set.indicator]
    split_ifs <;> simp [Real.norm_eq_abs, abs_nonneg]
  have hg_smeas : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have h_meas : ∀ n, AEStronglyMeasurable (h n) μ :=
    fun n ↦ (hg.indicator (hB_meas n)).aestronglyMeasurable
  have h_int_tendsto :
      Tendsto (fun n ↦ ∫ ω, h n ω ∂μ) atTop (𝓝 (∫ ω, h_inf ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (G := ℝ) (fun ω ↦ ‖g ω‖)
      h_meas hg_int.norm
      (fun n ↦ Filter.Eventually.of_forall (fun ω ↦ h_dom n ω))
      (Filter.Eventually.of_forall fun ω ↦ h_ptwise_lim ω)
  -- ∫_{B n} g ≥ 0 (maximal ergodic).
  have h_each_nn : ∀ n, 0 ≤ ∫ ω, h n ω ∂μ := by
    intro n
    rw [hh_def, integral_indicator (hB_meas n)]
    exact maximal_ergodic_inequality hT hg hg_int n
  -- Hence ∫ h_∞ ≥ 0.
  have h_inf_nn : 0 ≤ ∫ ω, h_inf ω ∂μ :=
    ge_of_tendsto h_int_tendsto (Filter.Eventually.of_forall h_each_nn)
  -- But ∫ h_∞ = ∫_{B_inf} g = ∫_Ω g (since μ(B_inf) = 1).
  have h_int_eq : ∫ ω, h_inf ω ∂μ = ∫ ω, g ω ∂μ := by
    rw [hh_inf_def, integral_indicator hB_inf_meas]
    have h_ae_in : ∀ᵐ ω ∂μ, ω ∈ B_inf := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hB_inf_meas).mpr hμB_inf
    exact (integral_eq_setIntegral h_ae_in g).symm
  linarith

/-- **Hardy bound (finite n)**: for any `m n : ℕ`,
`m · μ({maxPartialSum T (g - m) n > 0}) ≤ ‖g‖₁`.

The maximal ergodic inequality `0 ≤ ∫_E (g - m)` rearranges to
`m · μ(E) ≤ ∫_E g ≤ ∫|g|`, where `E := {maxPartialSum (g - m) n > 0}`.
For `m = 0` the bound is trivial. -/
lemma maxPartialSum_meas_le
    (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Measurable g) (hg_int : Integrable g μ) (m n : ℕ) :
    (m : ℝ≥0∞) * μ {ω | 0 < maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) n ω}
      ≤ ENNReal.ofReal (∫ ω, |g ω| ∂μ) := by
  set g_m : Ω → ℝ := fun ω ↦ g ω - (m : ℝ)
  have hg_m_meas : Measurable g_m := hg.sub_const _
  have hg_m_int : Integrable g_m μ := hg_int.sub (integrable_const _)
  set E : Set Ω := {ω | 0 < maxPartialSum T g_m n ω}
  have hE_meas : MeasurableSet E :=
    (maxPartialSum_measurable hT.measurable hg_m_meas n) measurableSet_Ioi
  have h_max := maximal_ergodic_inequality hT hg_m_meas hg_m_int n
  -- ∫_E g_m = ∫_E g - m · μ(E).toReal
  have h_decomp : ∫ ω in E, g_m ω ∂μ = ∫ ω in E, g ω ∂μ - (m : ℝ) * (μ E).toReal := by
    rw [show g_m = fun ω ↦ g ω - (m : ℝ) from rfl,
        integral_sub hg_int.integrableOn (integrable_const _).integrableOn,
        setIntegral_const]
    rw [show μ.real E = (μ E).toReal from rfl]
    ring
  rw [h_decomp] at h_max
  -- m · μ(E).toReal ≤ ∫_E g ≤ ∫|g|.
  have h_mu_lt : μ E < ⊤ := measure_lt_top _ _
  have h_abs_int : Integrable (fun ω ↦ |g ω|) μ := hg_int.abs
  have h_g_le_abs : ∫ ω in E, g ω ∂μ ≤ ∫ ω, |g ω| ∂μ := by
    calc ∫ ω in E, g ω ∂μ
        ≤ ∫ ω in E, |g ω| ∂μ :=
          setIntegral_mono_ae hg_int.integrableOn h_abs_int.integrableOn
            (Filter.Eventually.of_forall fun ω ↦ le_abs_self _)
      _ ≤ ∫ ω, |g ω| ∂μ :=
          setIntegral_le_integral h_abs_int
            (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _)
  have h_real : (m : ℝ) * (μ E).toReal ≤ ∫ ω, |g ω| ∂μ := by linarith
  -- Lift to ENNReal.
  have h_m_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [show (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) from
    (ENNReal.ofReal_natCast m).symm]
  rw [show μ E = ENNReal.ofReal (μ E).toReal from
    (ENNReal.ofReal_toReal h_mu_lt.ne).symm]
  rw [← ENNReal.ofReal_mul h_m_nn]
  exact ENNReal.ofReal_le_ofReal h_real

/-- **Hardy bound (union)**: union of `{maxPartialSum (g - m) n > 0}` over
`n` is bounded by `‖g‖₁ / m` (in ENNReal). -/
lemma maxPartialSum_meas_iUnion_le
    (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Measurable g) (hg_int : Integrable g μ) (m : ℕ) :
    (m : ℝ≥0∞) *
      μ (⋃ n, {ω | 0 < maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) n ω})
      ≤ ENNReal.ofReal (∫ ω, |g ω| ∂μ) := by
  -- Monotonicity of {0 < maxPartialSum (g - m) n} in n.
  have h_mono : Monotone (fun n ↦
      {ω | 0 < maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) n ω}) := by
    intro a b hab ω hω
    show 0 < maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) b ω
    obtain ⟨k, _, hka, hk_eq⟩ :=
      exists_pos_index_attaining_max T (fun ω ↦ g ω - (m : ℝ)) a ω hω
    calc (0 : ℝ)
        < maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) a ω := hω
      _ = birkhoffPartialSum T (fun ω ↦ g ω - (m : ℝ)) k ω := hk_eq.symm
      _ ≤ maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) b ω :=
          birkhoffPartialSum_le_maxPartialSum T _ b (hka.trans hab) ω
  rw [h_mono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n ↦ maxPartialSum_meas_le hT hg hg_int m n

/-- **A.e. boundedness of Birkhoff averages** (Hardy-Littlewood-style).
For `T` measure-preserving and `g` integrable, the sequence
`n ↦ birkhoffAverageReal T g n ω` has bounded range a.e.

Proof: combine `maxPartialSum_meas_iUnion_le` (Hardy union bound) with
the inclusion `{¬BddAbove range A_·} ⊆ ⋂_m ⋃_n {maxPartialSum (g-m) n > 0}`
(positive Birkhoff sum from `A_k > m`) and `exists_nat_gt` (Archimedean
choice of `m` large to push `‖g‖₁/m < ε`). -/
lemma birkhoffAverageReal_ae_bddAbove
    (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Measurable g) (hg_int : Integrable g μ) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range (fun n ↦ birkhoffAverageReal T g n ω)) := by
  classical
  rw [ae_iff]
  set U : ℕ → Set Ω := fun m ↦
    ⋃ n, {ω | 0 < maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) n ω}
  -- Step 1: {¬BddAbove} ⊆ ⋂_m U m.
  have h_subset :
      {ω | ¬ BddAbove (Set.range (fun n ↦ birkhoffAverageReal T g n ω))}
        ⊆ ⋂ m, U m := by
    intro ω hω
    rw [Set.mem_setOf_eq, not_bddAbove_iff] at hω
    refine Set.mem_iInter.mpr fun m ↦ ?_
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hω (m : ℝ)
    refine Set.mem_iUnion.mpr ⟨k + 1, ?_⟩
    show 0 < maxPartialSum T (fun ω ↦ g ω - (m : ℝ)) (k + 1) ω
    -- A_k(g, ω) > m ⟹ S_{k+1}(g - m, ω) > 0.
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hS_eq : birkhoffPartialSum T (fun ω ↦ g ω - (m : ℝ)) (k + 1) ω
        = (k + 1 : ℝ) * birkhoffAverageReal T g k ω - (k + 1 : ℝ) * m := by
      unfold birkhoffPartialSum birkhoffAverageReal
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hk1_ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk1_pos
      field_simp
      push_cast
      ring
    have hS_pos : 0 < birkhoffPartialSum T (fun ω ↦ g ω - (m : ℝ)) (k + 1) ω := by
      rw [hS_eq]; nlinarith
    exact hS_pos.trans_le
      (birkhoffPartialSum_le_maxPartialSum T _ (k + 1) le_rfl ω)
  -- Step 2: μ(⋂_m U m) = 0 via Archimedean.
  refine measure_mono_null h_subset ?_
  -- Bound: for every m, (m : ℝ≥0∞) * μ(U m) ≤ ‖g‖₁.
  have h_U_bound : ∀ m : ℕ, (m : ℝ≥0∞) * μ (U m) ≤ ENNReal.ofReal (∫ ω, |g ω| ∂μ) :=
    fun m ↦ maxPartialSum_meas_iUnion_le hT hg hg_int m
  -- Use Archimedean to get μ(⋂_m U m) ≤ ε for arbitrary ε > 0.
  rw [← nonpos_iff_eq_zero]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε h_top ↦ ?_
  -- Pick m > ‖g‖₁ / ε (real division).
  obtain ⟨m, hm⟩ := exists_nat_gt ((∫ ω, |g ω| ∂μ) / (ε : ℝ))
  -- m ≥ 1 because m > ‖g‖₁/ε ≥ 0 and m : ℕ (so m ≥ 1 if m > 0; we'll separately handle m = 0).
  have hε_pos : (0 : ℝ) < ε := by exact_mod_cast hε
  have h_int_nn : 0 ≤ ∫ ω, |g ω| ∂μ := integral_nonneg fun _ ↦ abs_nonneg _
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      have h_div : 0 ≤ (∫ ω, |g ω| ∂μ) / (ε : ℝ) := div_nonneg h_int_nn hε_pos.le
      push_cast at hm
      linarith
    · exact h
  have hm_ne : (m : ℝ≥0∞) ≠ 0 := by
    simp only [Ne, Nat.cast_eq_zero]; omega
  have hm_top : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  -- μ(⋂_m U m) ≤ μ(U m) ≤ ‖g‖₁/m < ε.
  have h_lt : μ (⋂ m, U m) < (ε : ℝ≥0∞) := by
    calc μ (⋂ m, U m)
        ≤ μ (U m) := measure_mono (Set.iInter_subset U m)
      _ ≤ ENNReal.ofReal (∫ ω, |g ω| ∂μ) / (m : ℝ≥0∞) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hm_ne) (Or.inl hm_top), mul_comm]
          exact h_U_bound m
      _ < (ε : ℝ≥0∞) := by
          have h_real_lt : (∫ ω, |g ω| ∂μ) / (m : ℝ) < (ε : ℝ) := by
            rw [div_lt_iff₀ hm_real_pos]
            rw [div_lt_iff₀ hε_pos] at hm
            linarith
          have h_rhs_eq : ENNReal.ofReal (∫ ω, |g ω| ∂μ) / (m : ℝ≥0∞)
              = ENNReal.ofReal ((∫ ω, |g ω| ∂μ) / (m : ℝ)) := by
            rw [show (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) from
                (ENNReal.ofReal_natCast m).symm]
            rw [← ENNReal.ofReal_div_of_pos hm_real_pos]
          rw [h_rhs_eq, show ((ε : ℝ≥0∞)) = ENNReal.ofReal ((ε : ℝ)) from
              (ENNReal.ofReal_coe_nnreal).symm]
          exact (ENNReal.ofReal_lt_ofReal_iff hε_pos).mpr h_real_lt
  calc μ (⋂ m, U m)
      ≤ (ε : ℝ≥0∞) := le_of_lt h_lt
    _ = 0 + (ε : ℝ≥0∞) := by rw [zero_add]

/-- **T-invariance of the Birkhoff-average limsup (a.e.)**. For measure
preserving `T` and integrable `f`, the function
`limsupAvg ω := limsup_n A_n(f, ω)` satisfies `limsupAvg ∘ T =ᵐ limsupAvg`.

Proof: from `birkhoffAverageReal_ae_bddAbove` applied to `f` and to `-f`,
a.e. the sequence `A_n(f, ω)` is bounded. The recursion
`A_n(f, Tω) - A_{n+1}(f, ω) = (A_{n+1}(f, ω) - f(ω))/(n+1)` then
gives `A_n(f, Tω) - A_{n+1}(f, ω) → 0` (bounded numerator / `n+1`).
Combining with `Filter.limsup_nat_add` shifts back to
`limsup A_n(f, Tω) = limsup A_n(f, ω)`. -/
lemma birkhoffAverageReal_limsup_comp_T_ae
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Measurable f) (hf_int : Integrable f μ) :
    (fun ω ↦ Filter.limsup (fun n ↦ birkhoffAverageReal T f n ω) Filter.atTop) ∘ T
      =ᵐ[μ] fun ω ↦ Filter.limsup (fun n ↦ birkhoffAverageReal T f n ω) Filter.atTop := by
  classical
  have h_above := birkhoffAverageReal_ae_bddAbove hT hf hf_int
  have h_below : ∀ᵐ ω ∂μ, BddBelow (Set.range (fun n ↦ birkhoffAverageReal T f n ω)) := by
    have h := birkhoffAverageReal_ae_bddAbove hT hf.neg hf_int.neg
    filter_upwards [h] with ω hω
    obtain ⟨b, hb⟩ := hω
    refine ⟨-b, ?_⟩
    rintro y ⟨n, rfl⟩
    have h_neg : birkhoffAverageReal T (fun ω ↦ -f ω) n ω = -birkhoffAverageReal T f n ω := by
      unfold birkhoffAverageReal
      have h_sum : (∑ i ∈ Finset.range (n + 1), -f (T^[i] ω))
          = -∑ i ∈ Finset.range (n + 1), f (T^[i] ω) := by
        rw [← Finset.sum_neg_distrib]
      rw [h_sum, neg_div]
    have := hb ⟨n, h_neg⟩
    linarith
  filter_upwards [h_above, h_below] with ω h_ab h_bel
  show Filter.limsup (fun n ↦ birkhoffAverageReal T f n (T ω)) Filter.atTop
    = Filter.limsup (fun n ↦ birkhoffAverageReal T f n ω) Filter.atTop
  obtain ⟨B_up, hB_up⟩ := h_ab
  obtain ⟨B_lo, hB_lo⟩ := h_bel
  -- M := bound on |A_{n+1}(f, ω) - f(ω)|.
  set M : ℝ := |B_up| + |B_lo| + |f ω| with hM_def
  have h_bd_diff : ∀ n : ℕ, |birkhoffAverageReal T f (n + 1) ω - f ω| ≤ M := by
    intro n
    have h1 : birkhoffAverageReal T f (n + 1) ω ≤ B_up := hB_up ⟨n + 1, rfl⟩
    have h2 : B_lo ≤ birkhoffAverageReal T f (n + 1) ω := hB_lo ⟨n + 1, rfl⟩
    have hBup_abs : B_up ≤ |B_up| := le_abs_self _
    have hBlo_abs : -|B_lo| ≤ B_lo := neg_abs_le _
    have hf_abs : f ω ≤ |f ω| := le_abs_self _
    have hf_neg_abs : -|f ω| ≤ f ω := neg_abs_le _
    have hBlo_nn : 0 ≤ |B_lo| := abs_nonneg _
    have hBup_nn : 0 ≤ |B_up| := abs_nonneg _
    rw [abs_sub_le_iff]
    constructor <;> linarith
  -- Recursion: A_n(f, T ω) - A_{n+1}(f, ω) = (A_{n+1}(f, ω) - f(ω))/(n+1).
  have h_diff_eq : ∀ n : ℕ,
      birkhoffAverageReal T f n (T ω) - birkhoffAverageReal T f (n + 1) ω
        = (birkhoffAverageReal T f (n + 1) ω - f ω) / ((n : ℝ) + 1) := by
    intro n
    have h_recur := birkhoffAverageReal_comp_T T f n ω
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1_pos
    rw [h_recur]
    field_simp
    ring
  -- u_n := A_n(f, T ω), v_n := A_{n+1}(f, ω). u_n - v_n → 0.
  have h_diff_tendsto : Tendsto (fun n : ℕ ↦
      birkhoffAverageReal T f n (T ω) - birkhoffAverageReal T f (n + 1) ω) atTop (𝓝 0) := by
    rw [funext h_diff_eq]
    have hM_div_tendsto : Tendsto (fun n : ℕ ↦ M / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ ↦ M * (1 / ((n : ℝ) + 1))) atTop (𝓝 (M * 0)) :=
        h1.const_mul M
      simp only [mul_zero] at h2
      convert h2 using 1
      funext n; rw [mul_one_div]
    refine squeeze_zero_norm (fun n ↦ ?_) hM_div_tendsto
    rw [Real.norm_eq_abs, abs_div]
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [abs_of_pos hn1_pos]
    exact div_le_div_of_nonneg_right (h_bd_diff n) hn1_pos.le
  -- Bounded under hypotheses for v_n = A_{n+1}(f, ω).
  have h_v_bdd_above : Filter.atTop.IsBoundedUnder (· ≤ ·)
      (fun n : ℕ ↦ birkhoffAverageReal T f (n + 1) ω) :=
    Filter.isBoundedUnder_of_eventually_le (a := B_up) <|
      Filter.Eventually.of_forall fun n ↦ hB_up ⟨n + 1, rfl⟩
  have h_v_bdd_below : Filter.atTop.IsBoundedUnder (· ≥ ·)
      (fun n : ℕ ↦ birkhoffAverageReal T f (n + 1) ω) :=
    Filter.isBoundedUnder_of_eventually_ge (a := B_lo) <|
      Filter.Eventually.of_forall fun n ↦ hB_lo ⟨n + 1, rfl⟩
  -- u_n bounded above: from v_n + diff (diff bounded by 1 eventually).
  have h_u_bdd_above : Filter.atTop.IsBoundedUnder (· ≤ ·)
      (fun n : ℕ ↦ birkhoffAverageReal T f n (T ω)) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := B_up + 1) ?_
    filter_upwards [h_diff_tendsto.eventually (Metric.ball_mem_nhds 0 one_pos)] with n hn
    rw [Real.dist_eq, abs_sub_lt_iff, sub_zero] at hn
    have : birkhoffAverageReal T f n (T ω) - birkhoffAverageReal T f (n + 1) ω < 1 := hn.1
    have hv : birkhoffAverageReal T f (n + 1) ω ≤ B_up := hB_up ⟨n + 1, rfl⟩
    linarith
  have h_u_bdd_below : Filter.atTop.IsBoundedUnder (· ≥ ·)
      (fun n : ℕ ↦ birkhoffAverageReal T f n (T ω)) := by
    refine Filter.isBoundedUnder_of_eventually_ge (a := B_lo - 1) ?_
    filter_upwards [h_diff_tendsto.eventually (Metric.ball_mem_nhds 0 one_pos)] with n hn
    rw [Real.dist_eq, abs_sub_lt_iff, sub_zero] at hn
    have : -1 < birkhoffAverageReal T f n (T ω) - birkhoffAverageReal T f (n + 1) ω := by linarith
    have hv : B_lo ≤ birkhoffAverageReal T f (n + 1) ω := hB_lo ⟨n + 1, rfl⟩
    linarith
  -- limsup u_n ≤ limsup v_n (and vice versa) via "u_n ≤ v_n + ε eventually".
  have h_le : Filter.limsup (fun n ↦ birkhoffAverageReal T f n (T ω)) Filter.atTop
      ≤ Filter.limsup (fun n ↦ birkhoffAverageReal T f (n + 1) ω) Filter.atTop := by
    rw [le_iff_forall_pos_lt_add]
    intro ε hε
    have h_event : ∀ᶠ n in Filter.atTop,
        birkhoffAverageReal T f n (T ω) ≤ birkhoffAverageReal T f (n + 1) ω + ε / 2 := by
      filter_upwards [h_diff_tendsto.eventually (Metric.ball_mem_nhds 0 (half_pos hε))] with n hn
      rw [Real.dist_eq, abs_sub_lt_iff, sub_zero] at hn
      linarith [hn.1]
    have h_v_const_bdd : Filter.atTop.IsBoundedUnder (· ≤ ·)
        (fun n : ℕ ↦ birkhoffAverageReal T f (n + 1) ω + ε / 2) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := B_up + ε / 2) ?_
      refine Filter.Eventually.of_forall fun n ↦ ?_
      have : birkhoffAverageReal T f (n + 1) ω ≤ B_up := hB_up ⟨n + 1, rfl⟩
      linarith
    have h_step : Filter.limsup (fun n ↦ birkhoffAverageReal T f n (T ω)) Filter.atTop
        ≤ Filter.limsup (fun n ↦ birkhoffAverageReal T f (n + 1) ω + ε / 2) Filter.atTop :=
      Filter.limsup_le_limsup h_event h_u_bdd_below.isCoboundedUnder_le h_v_const_bdd
    have h_const_eq :
        Filter.limsup (fun n : ℕ ↦ birkhoffAverageReal T f (n + 1) ω + ε / 2) Filter.atTop
          = Filter.limsup (fun n ↦ birkhoffAverageReal T f (n + 1) ω) Filter.atTop + ε / 2 :=
      limsup_add_const Filter.atTop _ (ε / 2) h_v_bdd_above
        h_v_bdd_below.isCoboundedUnder_le
    linarith [h_step.trans_eq h_const_eq]
  have h_ge : Filter.limsup (fun n ↦ birkhoffAverageReal T f (n + 1) ω) Filter.atTop
      ≤ Filter.limsup (fun n ↦ birkhoffAverageReal T f n (T ω)) Filter.atTop := by
    rw [le_iff_forall_pos_lt_add]
    intro ε hε
    have h_event : ∀ᶠ n in Filter.atTop,
        birkhoffAverageReal T f (n + 1) ω ≤ birkhoffAverageReal T f n (T ω) + ε / 2 := by
      filter_upwards [h_diff_tendsto.eventually (Metric.ball_mem_nhds 0 (half_pos hε))] with n hn
      rw [Real.dist_eq, abs_sub_lt_iff, sub_zero] at hn
      linarith [hn.2]
    have h_u_const_bdd : Filter.atTop.IsBoundedUnder (· ≤ ·)
        (fun n : ℕ ↦ birkhoffAverageReal T f n (T ω) + ε / 2) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := B_up + 1 + ε / 2) ?_
      filter_upwards [h_diff_tendsto.eventually (Metric.ball_mem_nhds 0 one_pos)] with n hn
      rw [Real.dist_eq, abs_sub_lt_iff, sub_zero] at hn
      have hv : birkhoffAverageReal T f (n + 1) ω ≤ B_up := hB_up ⟨n + 1, rfl⟩
      linarith [hn.1]
    have h_step : Filter.limsup (fun n ↦ birkhoffAverageReal T f (n + 1) ω) Filter.atTop
        ≤ Filter.limsup (fun n ↦ birkhoffAverageReal T f n (T ω) + ε / 2) Filter.atTop :=
      Filter.limsup_le_limsup h_event h_v_bdd_below.isCoboundedUnder_le h_u_const_bdd
    have h_const_eq :
        Filter.limsup (fun n : ℕ ↦ birkhoffAverageReal T f n (T ω) + ε / 2) Filter.atTop
          = Filter.limsup (fun n ↦ birkhoffAverageReal T f n (T ω)) Filter.atTop + ε / 2 :=
      limsup_add_const Filter.atTop _ (ε / 2) h_u_bdd_above
        h_u_bdd_below.isCoboundedUnder_le
    linarith [h_step.trans_eq h_const_eq]
  have h_shift : Filter.limsup (fun n ↦ birkhoffAverageReal T f (n + 1) ω) Filter.atTop
      = Filter.limsup (fun n ↦ birkhoffAverageReal T f n ω) Filter.atTop :=
    Filter.limsup_nat_add (fun n ↦ birkhoffAverageReal T f n ω) 1
  rw [← h_shift]
  exact le_antisymm h_le h_ge

omit [IsProbabilityMeasure μ] in
/-- Measurability of `ω ↦ limsup A_n(f, ω)` (as a real-valued function;
when the sequence is unbounded the value is the `Real.limsup` junk value
but the function remains measurable). -/
lemma birkhoffAverageReal_limsup_aestronglyMeasurable
    {T : Ω → Ω} (hT_meas : Measurable T) {f : Ω → ℝ} (hf : Measurable f) :
    AEStronglyMeasurable
      (fun ω ↦ Filter.limsup (fun n ↦ birkhoffAverageReal T f n ω) Filter.atTop) μ := by
  refine (Measurable.limsup ?_).aestronglyMeasurable
  intro n
  unfold birkhoffAverageReal
  exact ((Finset.measurable_sum _ (fun i _ ↦ hf.comp (hT_meas.iterate i))).div_const _)

/-- **Ergodic limsup discharge**: for ergodic `T` and integrable `g` with
`∫g dμ < 0`, the limsup of Birkhoff averages of `g` is `≤ 0` a.e.

Proof: by T-invariance (`birkhoffAverageReal_limsup_comp_T_ae`) and
ergodicity (`Ergodic.ae_eq_const_of_ae_eq_comp_ae`), `lsa =ᵐ const c`
for some `c : ℝ`. We show `c ≤ 0` by contradiction: if `c > 0`, then a.e.
`∃ᶠ n, A_n(g, ω) > c/2 > 0` (from limsup = c), hence
`∀ k, ∃ N ≥ k, S_N(g, ω) > 0` (with `N := n + 1`). This full-measure set
violates `birkhoff_neg_mean_sup_null`. -/
lemma birkhoffAverageReal_limsup_le_zero_of_int_neg
    (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {g : Ω → ℝ} (hg : Measurable g) (hg_int : Integrable g μ)
    (hg_neg : ∫ ω, g ω ∂μ < 0) :
    ∀ᵐ ω ∂μ, Filter.limsup (fun n ↦ birkhoffAverageReal T g n ω) Filter.atTop ≤ 0 := by
  set lsa : Ω → ℝ :=
    fun ω ↦ Filter.limsup (fun n ↦ birkhoffAverageReal T g n ω) Filter.atTop with hlsa_def
  have h_meas : AEStronglyMeasurable lsa μ :=
    birkhoffAverageReal_limsup_aestronglyMeasurable hT.measurable hg
  have h_inv : lsa ∘ T =ᵐ[μ] lsa :=
    birkhoffAverageReal_limsup_comp_T_ae hT g hg hg_int
  obtain ⟨c, hc⟩ := hT_erg.ae_eq_const_of_ae_eq_comp_ae h_meas h_inv
  suffices hc_nn : c ≤ 0 by
    filter_upwards [hc] with ω hω
    show lsa ω ≤ 0
    rw [hω]; exact hc_nn
  by_contra hc_neg
  have hc_neg : 0 < c := lt_of_not_ge hc_neg
  have hc_half : 0 < c / 2 := half_pos hc_neg
  have h_below := birkhoffAverageReal_ae_bddAbove hT hg.neg hg_int.neg
  -- For a.e. ω: ∀ k, ∃ N ≥ k, S_N(g, ω) > 0.
  have h_inf_often : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ N ≥ k, 0 < birkhoffPartialSum T g N ω := by
    filter_upwards [hc, h_below] with ω hω hω_bdd
    have hω' : Filter.limsup (fun n ↦ birkhoffAverageReal T g n ω) Filter.atTop = c := hω
    -- BddBelow A_·(g, ω) via BddAbove A_·(-g, ω).
    obtain ⟨b, hb⟩ := hω_bdd
    have h_bdd_below : Filter.atTop.IsBoundedUnder (· ≥ ·)
        (fun n ↦ birkhoffAverageReal T g n ω) := by
      refine Filter.isBoundedUnder_of_eventually_ge (a := -b) ?_
      refine Filter.Eventually.of_forall fun n ↦ ?_
      have h_neg : birkhoffAverageReal T (fun ω ↦ -g ω) n ω
          = -birkhoffAverageReal T g n ω := by
        unfold birkhoffAverageReal
        have h_sum : (∑ i ∈ Finset.range (n + 1), -g (T^[i] ω))
            = -∑ i ∈ Finset.range (n + 1), g (T^[i] ω) := by
          rw [← Finset.sum_neg_distrib]
        rw [h_sum, neg_div]
      have := hb ⟨n, h_neg⟩
      linarith
    have h_freq : ∃ᶠ n in Filter.atTop, c / 2 < birkhoffAverageReal T g n ω := by
      apply Filter.frequently_lt_of_lt_limsup h_bdd_below.isCoboundedUnder_le
      rw [hω']; linarith
    intro k
    obtain ⟨n, hn_avg, hn_ge⟩ :=
      (h_freq.and_eventually (Filter.eventually_ge_atTop k)).exists
    refine ⟨n + 1, by omega, ?_⟩
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hS_eq : birkhoffPartialSum T g (n + 1) ω
        = (n + 1 : ℝ) * birkhoffAverageReal T g n ω := by
      rw [birkhoffAverageReal_eq_partialSum_div]
      field_simp
    rw [hS_eq]
    exact mul_pos hn1_pos (lt_trans hc_half hn_avg)
  -- Apply birkhoff_neg_mean_sup_null.
  apply birkhoff_neg_mean_sup_null hT hT_erg hg hg_int hg_neg
  have h_meas_set : MeasurableSet
      {ω | ∀ k : ℕ, ∃ N ≥ k, 0 < birkhoffPartialSum T g N ω} := by
    have h_eq : {ω : Ω | ∀ k : ℕ, ∃ N ≥ k, 0 < birkhoffPartialSum T g N ω}
        = ⋂ k : ℕ, ⋃ N : ℕ, ⋃ (_ : N ≥ k), {ω : Ω | 0 < birkhoffPartialSum T g N ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, ge_iff_le, exists_prop]
    rw [h_eq]
    refine MeasurableSet.iInter fun k ↦ MeasurableSet.iUnion fun N ↦
      MeasurableSet.iUnion fun _ ↦ ?_
    exact (birkhoffPartialSum_measurable hT.measurable hg N) measurableSet_Ioi
  rw [measure_univ]
  rw [ae_iff] at h_inf_often
  -- h_inf_often : μ {ω | ¬ ∀ k, ∃ N ≥ k, ...} = 0
  -- {good}ᶜ = {ω | ¬ good ω}, so μ {good}ᶜ = 0 ⟺ μ {good} = 1.
  exact (prob_compl_eq_zero_iff h_meas_set).mp h_inf_often

/-- **Upper sandwich**: for every `ε > 0`, a.e. `ω`, eventually
`birkhoffAverageReal T f n ω < ∫f dμ + ε`. -/
lemma birkhoff_eventually_lt_integral_add
    (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Measurable f) (hf_int : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      birkhoffAverageReal T f n ω < ∫ x, f x ∂μ + ε := by
  set α : ℝ := ∫ x, f x ∂μ with hα
  set ε' : ℝ := ε / 2 with hε'
  have hε'_pos : 0 < ε' := half_pos hε
  set g : Ω → ℝ := fun ω ↦ f ω - α - ε' with hg
  have hg_meas : Measurable g := (hf.sub measurable_const).sub measurable_const
  have hg_int : Integrable g μ :=
    (hf_int.sub (integrable_const α)).sub (integrable_const ε')
  have hg_int_eq : ∫ ω, g ω ∂μ = -ε' := by
    have h_g_eq : ∀ ω, g ω = f ω - (α + ε') := fun ω ↦ by simp [hg]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h_g_eq),
        integral_sub hf_int (integrable_const _),
        integral_const]
    simp [← hα]
  have hg_neg : ∫ ω, g ω ∂μ < 0 := by rw [hg_int_eq]; linarith
  have h_limsup : ∀ᵐ ω ∂μ,
      Filter.limsup (fun n ↦ birkhoffAverageReal T g n ω) Filter.atTop ≤ 0 :=
    birkhoffAverageReal_limsup_le_zero_of_int_neg hT hT_erg hg_meas hg_int hg_neg
  have h_ae_bdd : ∀ᵐ ω ∂μ,
      BddAbove (Set.range (fun n ↦ birkhoffAverageReal T g n ω)) :=
    birkhoffAverageReal_ae_bddAbove hT hg_meas hg_int
  -- Convert: limsup ≤ 0 ⟹ eventually A_n(g) < ε' ⟹ A_n(f) < α + ε' + ε' = α + ε.
  filter_upwards [h_limsup, h_ae_bdd] with ω hω hω_bdd
  -- ∀ε'' > 0, ∀ᶠ n, A_n(g) < ε''. Apply with ε'' := ε'.
  have h_freq_lt : ∀ᶠ n in Filter.atTop, birkhoffAverageReal T g n ω < ε' := by
    have h_lt : Filter.limsup (fun n ↦ birkhoffAverageReal T g n ω) Filter.atTop < ε' :=
      lt_of_le_of_lt hω hε'_pos
    exact Filter.eventually_lt_of_limsup_lt h_lt hω_bdd.isBoundedUnder_of_range
  filter_upwards [h_freq_lt] with n hn
  -- A_n(g, ω) = A_n(f, ω) - α - ε' < ε' ⟹ A_n(f, ω) < α + 2ε' = α + ε.
  have h_decomp : birkhoffAverageReal T g n ω = birkhoffAverageReal T f n ω - α - ε' := by
    unfold birkhoffAverageReal
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [show g = fun ω' ↦ f ω' - α - ε' from rfl]
    rw [show (fun ω' : Ω ↦ f ω' - α - ε')
      = (fun ω' : Ω ↦ f ω' - (α + ε')) from by funext ω'; ring]
    -- ∑ (f(T^i ω) - (α + ε')) = (∑ f(T^i ω)) - (n+1)(α + ε')
    have h_sum_eq : (∑ i ∈ Finset.range (n + 1), (f (T^[i] ω) - (α + ε')))
        = (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) - ((n : ℝ) + 1) * (α + ε') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [h_sum_eq]
    field_simp
    ring
  linarith [h_decomp, hn]

/-- **Lower sandwich**: for every `ε > 0`, a.e. `ω`, eventually
`∫f dμ - ε < birkhoffAverageReal T f n ω`.

Proof: apply the upper sandwich to `-f` and negate. -/
lemma birkhoff_eventually_gt_integral_sub
    (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Measurable f) (hf_int : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      ∫ x, f x ∂μ - ε < birkhoffAverageReal T f n ω := by
  have h_upper := birkhoff_eventually_lt_integral_add hT hT_erg hf.neg hf_int.neg hε
  filter_upwards [h_upper] with ω hω
  filter_upwards [hω] with n hn
  -- A_n(-f, ω) = -A_n(f, ω); ∫(-f) = -∫f.
  have h_neg_avg : birkhoffAverageReal T (fun ω ↦ -f ω) n ω = -birkhoffAverageReal T f n ω := by
    unfold birkhoffAverageReal
    rw [show (fun ω' : Ω ↦ -f ω') = (fun ω' : Ω ↦ -(f ω')) from rfl]
    have h_sum_neg : (∑ i ∈ Finset.range (n + 1), -f (T^[i] ω))
        = -(∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) := by
      rw [← Finset.sum_neg_distrib]
    rw [h_sum_neg, neg_div]
  have h_int_neg : ∫ x, (-f x) ∂μ = -∫ x, f x ∂μ := integral_neg _
  rw [h_neg_avg, h_int_neg] at hn
  linarith

end Sandwich

/-! ## §6 Main theorem -/

/-- **Birkhoff individual ergodic theorem.**

For a probability-preserving ergodic transformation `T : Ω → Ω` and an
integrable observable `f : Ω → ℝ`, the Birkhoff time averages

    A_n ω := (∑_{i=0}^{n} f (T^[i] ω)) / (n + 1)

converge almost everywhere to the spatial mean `∫ f dμ`. -/
@[entry_point]
theorem birkhoff_ergodic_ae {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  classical
  -- Replace `f` with a measurable model `f'` (AE-equal).
  set f' : Ω → ℝ := hf.aestronglyMeasurable.mk f with hf'_def
  have hf'_meas : Measurable f' :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf'_ae : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hf'_int : Integrable f' μ := hf.congr hf'_ae
  have h_int_eq : ∫ ω, f ω ∂μ = ∫ ω, f' ω ∂μ := integral_congr_ae hf'_ae
  -- A_n(f, ω) =ᵐ A_n(f', ω).
  have h_A_ae : ∀ n : ℕ, birkhoffAverageReal T f n =ᵐ[μ] birkhoffAverageReal T f' n := by
    intro n
    have h_each : ∀ i, (fun ω ↦ f (T^[i] ω)) =ᵐ[μ] fun ω ↦ f' (T^[i] ω) := fun i ↦
      (hT.iterate i).quasiMeasurePreserving.ae_eq hf'_ae
    have h_all : ∀ᵐ ω ∂μ, ∀ i : ℕ, f (T^[i] ω) = f' (T^[i] ω) := by
      rw [ae_all_iff]; exact h_each
    filter_upwards [h_all] with ω hω
    unfold birkhoffAverageReal
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ hω i)
  have h_all_A_ae : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      birkhoffAverageReal T f n ω = birkhoffAverageReal T f' n ω := by
    rw [ae_all_iff]; exact h_A_ae
  -- Apply upper/lower sandwich for each positive rational, then take countable
  -- intersection to get Tendsto via `Metric.tendsto_atTop`.
  have h_upper_rat : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      birkhoffAverageReal T f' n ω < ∫ x, f' x ∂μ + (q : ℝ) := fun q hq ↦
    birkhoff_eventually_lt_integral_add hT hT_erg hf'_meas hf'_int (by exact_mod_cast hq)
  have h_lower_rat : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      ∫ x, f' x ∂μ - (q : ℝ) < birkhoffAverageReal T f' n ω := fun q hq ↦
    birkhoff_eventually_gt_integral_sub hT hT_erg hf'_meas hf'_int (by exact_mod_cast hq)
  have h_upper_all : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 < q → ∀ᶠ n in Filter.atTop,
      birkhoffAverageReal T f' n ω < ∫ x, f' x ∂μ + (q : ℝ) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · exact (h_upper_rat q hq).mono fun _ hω _ ↦ hω
    · exact Filter.Eventually.of_forall fun _ h ↦ absurd h hq
  have h_lower_all : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 < q → ∀ᶠ n in Filter.atTop,
      ∫ x, f' x ∂μ - (q : ℝ) < birkhoffAverageReal T f' n ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · exact (h_lower_rat q hq).mono fun _ hω _ ↦ hω
    · exact Filter.Eventually.of_forall fun _ h ↦ absurd h hq
  -- Combine: ∀ᵐ ω, convergence A_n(f) → ∫f.
  filter_upwards [h_upper_all, h_lower_all, h_all_A_ae] with ω h_up h_lo h_ae_eq
  -- The sequences A_n(f, ω) and A_n(f', ω) agree pointwise.
  have h_seq_eq : (fun n ↦ birkhoffAverageReal T f n ω)
      = fun n ↦ birkhoffAverageReal T f' n ω := funext h_ae_eq
  rw [h_seq_eq, h_int_eq]
  -- Now show A_n(f', ω) → ∫f' via metric/ε.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Pick rational q ∈ (0, ε).
  obtain ⟨q, hq_pos, hq_lt⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < ε := by
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (0 : ℝ) < ε from hε)
    exact ⟨q, hq1, hq2⟩
  have hq_pos' : (0 : ℚ) < q := by exact_mod_cast hq_pos
  -- Get the eventual upper and lower bounds with this q.
  have h_up' : ∀ᶠ n in Filter.atTop,
      birkhoffAverageReal T f' n ω < ∫ x, f' x ∂μ + (q : ℝ) := h_up q hq_pos'
  have h_lo' : ∀ᶠ n in Filter.atTop,
      ∫ x, f' x ∂μ - (q : ℝ) < birkhoffAverageReal T f' n ω := h_lo q hq_pos'
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_up'.and h_lo')
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨h_u, h_l⟩ := hN n hn
  rw [Real.dist_eq, abs_sub_lt_iff]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

end InformationTheory.Shannon
