import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SMB.ChainRule
import InformationTheory.Shannon.SMB.McMillanBreiman
import InformationTheory.Probability.TwoSidedExtension
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## D.2 — k-Markov approximation -/

/-- `k`-Markov approximation to the per-step conditional log-likelihood:
for `i ≤ k`, use the genuine `pmfLogCond μ p i`; for `i > k`, use the
`k`-th conditional log-likelihood evaluated at the time-shifted point. -/
noncomputable def pmfLogCondMarkov
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k i : ℕ) :
    Ω → ℝ :=
  fun ω ↦ if i ≤ k then pmfLogCond μ p i ω
           else pmfLogCond μ p k (p.T^[i - k] ω)

omit [DecidableEq α] in
/-- Measurability of `pmfLogCondMarkov μ p k i`. -/
theorem measurable_pmfLogCondMarkov
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k i : ℕ) :
    Measurable (pmfLogCondMarkov μ p k i) := by
  -- The `i ≤ k` test doesn't depend on `ω`, so this is just two cases.
  unfold pmfLogCondMarkov
  by_cases h : i ≤ k
  · simp only [h, if_true]
    exact measurable_pmfLogCond μ p i
  · simp only [h, if_false]
    exact (measurable_pmfLogCond μ p k).comp (p.measurable_iterate (i - k))

omit [DecidableEq α] in
theorem pmfLogCondMarkov_sum_div_eq_add_birkhoffAverageReal
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k : ℕ) (ω : Ω)
    {n : ℕ} (hkn : k ≤ n) :
    (∑ i ∈ Finset.range (n + 1), pmfLogCondMarkov μ p k i ω) / (n + 1 : ℝ)
      = ((∑ i ∈ Finset.range (k + 1), pmfLogCond μ p i ω)
            - pmfLogCond μ p k ω) / (n + 1 : ℝ)
        + ((n - k + 1 : ℕ) : ℝ) / (n + 1 : ℝ)
          * birkhoffAverageReal p.T (pmfLogCond μ p k) (n - k) ω := by
  -- Split Finset.range (n+1) = range (k+1) ∪ Ico (k+1) (n+1).
  have h_sum_split :
      ∑ i ∈ Finset.range (n + 1), pmfLogCondMarkov μ p k i ω
        = (∑ i ∈ Finset.range (k + 1), pmfLogCondMarkov μ p k i ω)
          + ∑ i ∈ Finset.Ico (k + 1) (n + 1), pmfLogCondMarkov μ p k i ω := by
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hkn)]
  -- First piece: i ≤ k ⇒ pmfLogCondMarkov = pmfLogCond μ p i.
  have h_first :
      ∑ i ∈ Finset.range (k + 1), pmfLogCondMarkov μ p k i ω
        = ∑ i ∈ Finset.range (k + 1), pmfLogCond μ p i ω := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    show (if i ≤ k then pmfLogCond μ p i ω
      else pmfLogCond μ p k (p.T^[i - k] ω))
        = pmfLogCond μ p i ω
    simp [hi_le]
  -- Second piece: reindex j = i - (k+1), so i = j + k + 1 and j ∈ range (n-k).
  have h_second :
      ∑ i ∈ Finset.Ico (k + 1) (n + 1), pmfLogCondMarkov μ p k i ω
        = ∑ j ∈ Finset.range (n - k), pmfLogCond μ p k (p.T^[j + 1] ω) := by
    -- Apply Finset.sum_Ico_eq_sum_range.
    rw [Finset.sum_Ico_eq_sum_range]
    have h_len : n + 1 - (k + 1) = n - k := by omega
    rw [h_len]
    refine Finset.sum_congr rfl ?_
    intro j _
    -- i = (k+1) + j, so i ≤ k is false (since i ≥ k+1), and i - k = j + 1.
    show (if (k + 1) + j ≤ k then pmfLogCond μ p ((k+1)+j) ω
      else pmfLogCond μ p k (p.T^[(k+1)+j - k] ω))
        = pmfLogCond μ p k (p.T^[j + 1] ω)
    have h_not_le : ¬ (k + 1 + j ≤ k) := by omega
    have h_sub : (k + 1 + j) - k = j + 1 := by omega
    simp [h_not_le, h_sub]
  -- Now: second piece = ∑_{j=0}^{n-k-1} f(T^[j+1] ω)
  --     = (∑_{j=0}^{n-k} f(T^[j] ω)) - f(T^[0] ω)
  --     = (n-k+1) · birkhoffAverageReal T f (n-k) ω - f ω.
  have h_second_eq :
      ∑ j ∈ Finset.range (n - k), pmfLogCond μ p k (p.T^[j + 1] ω)
        = ((n - k + 1 : ℕ) : ℝ) * birkhoffAverageReal p.T (pmfLogCond μ p k) (n - k) ω
            - pmfLogCond μ p k ω := by
    have h_partial : (∑ j ∈ Finset.range (n - k + 1), pmfLogCond μ p k (p.T^[j] ω))
        = ((n - k + 1 : ℕ) : ℝ)
            * birkhoffAverageReal p.T (pmfLogCond μ p k) (n - k) ω := by
      unfold birkhoffAverageReal
      have h_ne : ((n - k : ℕ) : ℝ) + 1 ≠ 0 := by
        have : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have h_cast : ((n - k + 1 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [h_cast]
      field_simp
    have h_shift : (∑ j ∈ Finset.range (n - k + 1), pmfLogCond μ p k (p.T^[j] ω))
        = pmfLogCond μ p k (p.T^[0] ω)
          + ∑ j ∈ Finset.range (n - k), pmfLogCond μ p k (p.T^[j + 1] ω) := by
      rw [Finset.sum_range_succ']
      ring
    have h_T0 : p.T^[0] ω = ω := by rfl
    rw [h_T0] at h_shift
    linarith [h_partial, h_shift]
  rw [h_sum_split, h_first, h_second, h_second_eq]
  -- (C + (... - f ω)) / (n+1) = (C - f ω)/(n+1) + (n-k+1)/(n+1) * avg
  field_simp
  ring

omit [DecidableEq α] in
/-- Cesàro average of the `k`-Markov approximation converges a.s. to
`conditionalEntropyTail μ p k` (Birkhoff applied to `pmfLogCond μ p k`). -/
theorem birkhoffAverage_pmfLogCondMarkov_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ ↦
        (∑ i ∈ Finset.range (n + 1),
            pmfLogCondMarkov μ p.toStationaryProcess k i ω) / (n + 1 : ℝ))
      Filter.atTop (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k)) := by
  -- Strategy: split the sum at `k`. For `n ≥ k`,
  --   ∑_{i=0}^n pmfLogCondMarkov μ p k i ω
  --     = ∑_{i=0}^k pmfLogCond p i ω + ∑_{j=1}^{n-k} pmfLogCond p k (T^[j] ω)
  --     = C(ω) - f(ω) + (n-k+1) · birkhoffAverageReal T f (n-k) ω
  -- where f := pmfLogCond p k and C(ω) := ∑_{i=0}^k pmfLogCond p i ω.
  -- Then divide by (n+1): the constant tends to 0, the ratio (n-k+1)/(n+1) → 1,
  -- and Birkhoff gives the inner average → ∫f = H_k.
  set f : Ω → ℝ := pmfLogCond μ p.toStationaryProcess k with hf_def
  have h_birk : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n ↦ birkhoffAverageReal p.T f n ω) Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k)) :=
    birkhoffAverage_pmfLogCond_tendsto μ p k
  filter_upwards [h_birk] with ω h_birk_ω
  -- Define C(ω) := ∑_{i=0}^k f_i (a constant in n).
  set C : ℝ := ∑ i ∈ Finset.range (k + 1),
    pmfLogCond μ p.toStationaryProcess i ω with hC_def
  -- Eventual decomposition (holds for n ≥ k):
  have h_split : ∀ n, k ≤ n →
      (∑ i ∈ Finset.range (n + 1),
          pmfLogCondMarkov μ p.toStationaryProcess k i ω) / (n + 1 : ℝ)
        = (C - f ω) / (n + 1 : ℝ)
          + ((n - k + 1 : ℕ) : ℝ) / (n + 1 : ℝ)
            * birkhoffAverageReal p.T f (n - k) ω := by
    intro n hkn
    rw [hC_def, hf_def]
    exact pmfLogCondMarkov_sum_div_eq_add_birkhoffAverageReal μ p.toStationaryProcess k ω hkn
  -- Now establish three convergence facts.
  -- (a) (C - f ω) / (n+1) → 0.
  have h_inv : Filter.Tendsto
      (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ)) Filter.atTop (𝓝 0) := by
    have h_nat : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ)) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 := h_nat.inv_tendsto_atTop
    refine h2.congr (fun n ↦ ?_)
    simp [one_div]
  have h_a : Filter.Tendsto
      (fun n : ℕ ↦ (C - f ω) / (n + 1 : ℝ)) Filter.atTop (𝓝 0) := by
    have := h_inv.const_mul (C - f ω)
    simp only [mul_zero] at this
    refine this.congr (fun n ↦ ?_)
    rw [mul_one_div]
  -- (b) (n-k+1)/(n+1) → 1.
  have h_b : Filter.Tendsto
      (fun n : ℕ ↦ ((n - k + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) Filter.atTop (𝓝 1) := by
    -- Eventually equals (n+1-k)/(n+1) = 1 - k/(n+1) → 1.
    have h_eq : ∀ᶠ n in Filter.atTop,
        ((n - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) = 1 - (k : ℝ) / ((n : ℝ) + 1) := by
      filter_upwards [Filter.eventually_ge_atTop k] with n hkn
      have h_sub : (n - k + 1 : ℕ) = (n + 1) - k := by omega
      rw [h_sub]
      have hk_le : k ≤ n + 1 := Nat.le_succ_of_le hkn
      have h_cast : ((n + 1 - k : ℕ) : ℝ) = ((n : ℝ) + 1) - (k : ℝ) := by
        rw [Nat.cast_sub hk_le]; push_cast; ring
      rw [h_cast]
      have h_pos : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    refine Filter.Tendsto.congr' (h_eq.mono (fun n hn ↦ hn.symm)) ?_
    have h_kdiv : Filter.Tendsto
        (fun n : ℕ ↦ (k : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      have h := h_inv.const_mul (k : ℝ)
      simp only [mul_zero] at h
      refine h.congr (fun n ↦ ?_)
      rw [mul_one_div]
    have h_one : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (𝓝 1) :=
      tendsto_const_nhds
    have h_sub := h_one.sub h_kdiv
    simp only [sub_zero] at h_sub
    exact h_sub
  -- (c) birkhoffAverageReal T f (n-k) ω → H_k via composing Birkhoff with `n ↦ n-k`.
  have h_c : Filter.Tendsto
      (fun n : ℕ ↦ birkhoffAverageReal p.T f (n - k) ω) Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k)) :=
    h_birk_ω.comp (Filter.tendsto_sub_atTop_nat k)
  -- Combine (b) * (c) + (a):
  have h_bc := h_b.mul h_c
  simp only [one_mul] at h_bc
  have h_combine := h_a.add h_bc
  simp only [zero_add] at h_combine
  -- Match the goal via eventual equality from h_split.
  refine Filter.Tendsto.congr' ?_ h_combine
  filter_upwards [Filter.eventually_ge_atTop k] with n hkn
  exact (h_split n hkn).symm

/-- Negative log-likelihood of the `k`-Markov approximation over the block of
length `n`. -/
noncomputable def negLogQk
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, pmfLogCondMarkov μ p k i ω

omit [DecidableEq α] in
/-- `negLogQk μ p k n / n → conditionalEntropyTail μ p k` a.s. as `n → ∞`. -/
@[entry_point]
theorem negLogQk_div_tendsto_condEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ ↦ negLogQk μ p.toStationaryProcess k n ω / n)
      Filter.atTop (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k)) := by
  -- From `birkhoffAverage_pmfLogCondMarkov_tendsto`: for almost every ω,
  --   (∑_{i=0}^m markov k i ω)/(m+1) → H_k
  -- Compose with `n ↦ n - 1`, eventually n ≥ 1 ⇒ n - 1 + 1 = n and the sum
  -- becomes the `negLogQk μ p k n` (range n = range ((n-1)+1)).
  have h_birk := birkhoffAverage_pmfLogCondMarkov_tendsto μ p k
  filter_upwards [h_birk] with ω h_birk_ω
  -- Compose `h_birk_ω` with the monotone map `n ↦ n - 1`.
  have h_comp := h_birk_ω.comp (Filter.tendsto_sub_atTop_nat 1)
  -- Now `h_comp n = (∑_{i=0}^{n-1} markov k i ω) / ((n-1)+1)`.
  -- Eventually for n ≥ 1, this equals negLogQk μ p k n ω / n.
  refine Filter.Tendsto.congr' ?_ h_comp
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h_succ : (n - 1) + 1 = n := by omega
  show ((∑ i ∈ Finset.range ((n - 1) + 1),
        pmfLogCondMarkov μ p.toStationaryProcess k i ω) / (((n - 1) : ℕ) + 1 : ℝ))
      = negLogQk μ p.toStationaryProcess k n ω / n
  rw [h_succ]
  unfold negLogQk
  have h_cast : (((n - 1) : ℕ) + 1 : ℝ) = (n : ℝ) := by
    rw [show (((n - 1) : ℕ) + 1 : ℝ) = (((n - 1) + 1 : ℕ) : ℝ) by push_cast; ring]
    rw [h_succ]
  rw [h_cast]

end InformationTheory.Shannon
