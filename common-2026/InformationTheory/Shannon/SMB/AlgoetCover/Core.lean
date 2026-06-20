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
  fun ω => if i ≤ k then pmfLogCond μ p i ω
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
/-- Cesàro average of the `k`-Markov approximation converges a.s. to
`conditionalEntropyTail μ p k` (Birkhoff applied to `pmfLogCond μ p k`). -/
theorem birkhoffAverage_pmfLogCondMarkov_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ =>
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
      (fun n => birkhoffAverageReal p.T f n ω) Filter.atTop
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
    -- Split Finset.range (n+1) = range (k+1) ∪ Ico (k+1) (n+1).
    have h_sum_split :
        ∑ i ∈ Finset.range (n + 1),
          pmfLogCondMarkov μ p.toStationaryProcess k i ω
          = (∑ i ∈ Finset.range (k + 1),
              pmfLogCondMarkov μ p.toStationaryProcess k i ω)
            + ∑ i ∈ Finset.Ico (k + 1) (n + 1),
                pmfLogCondMarkov μ p.toStationaryProcess k i ω := by
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hkn)]
    -- First piece: i ≤ k ⇒ pmfLogCondMarkov = pmfLogCond μ p i.
    have h_first :
        ∑ i ∈ Finset.range (k + 1),
            pmfLogCondMarkov μ p.toStationaryProcess k i ω = C := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      show (if i ≤ k then pmfLogCond μ p.toStationaryProcess i ω
        else pmfLogCond μ p.toStationaryProcess k (p.T^[i - k] ω))
          = pmfLogCond μ p.toStationaryProcess i ω
      simp [hi_le]
    -- Second piece: reindex j = i - (k+1), so i = j + k + 1 and j ∈ range (n-k).
    have h_second :
        ∑ i ∈ Finset.Ico (k + 1) (n + 1),
            pmfLogCondMarkov μ p.toStationaryProcess k i ω
          = ∑ j ∈ Finset.range (n - k), f (p.T^[j + 1] ω) := by
      -- Apply Finset.sum_Ico_eq_sum_range.
      rw [Finset.sum_Ico_eq_sum_range]
      have h_len : n + 1 - (k + 1) = n - k := by omega
      rw [h_len]
      refine Finset.sum_congr rfl ?_
      intro j _
      -- i = (k+1) + j, so i ≤ k is false (since i ≥ k+1), and i - k = j + 1.
      show (if (k + 1) + j ≤ k then pmfLogCond μ p.toStationaryProcess ((k+1)+j) ω
        else pmfLogCond μ p.toStationaryProcess k (p.T^[(k+1)+j - k] ω))
          = f (p.T^[j + 1] ω)
      have h_not_le : ¬ (k + 1 + j ≤ k) := by omega
      have h_sub : (k + 1 + j) - k = j + 1 := by omega
      simp [h_not_le, h_sub, hf_def]
    -- Now: second piece = ∑_{j=0}^{n-k-1} f(T^[j+1] ω)
    --     = (∑_{j=0}^{n-k} f(T^[j] ω)) - f(T^[0] ω)
    --     = (n-k+1) · birkhoffAverageReal T f (n-k) ω - f ω.
    have h_second_eq :
        ∑ j ∈ Finset.range (n - k), f (p.T^[j + 1] ω)
          = ((n - k + 1 : ℕ) : ℝ) * birkhoffAverageReal p.T f (n - k) ω - f ω := by
      have h_partial : (∑ j ∈ Finset.range (n - k + 1), f (p.T^[j] ω))
          = ((n - k + 1 : ℕ) : ℝ) * birkhoffAverageReal p.T f (n - k) ω := by
        unfold birkhoffAverageReal
        have h_ne : ((n - k : ℕ) : ℝ) + 1 ≠ 0 := by
          have : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have h_cast : ((n - k + 1 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [h_cast]
        field_simp
      have h_shift : (∑ j ∈ Finset.range (n - k + 1), f (p.T^[j] ω))
          = f (p.T^[0] ω) + ∑ j ∈ Finset.range (n - k), f (p.T^[j + 1] ω) := by
        rw [Finset.sum_range_succ']
        ring
      have h_T0 : p.T^[0] ω = ω := by rfl
      rw [h_T0] at h_shift
      linarith [h_partial, h_shift]
    rw [h_sum_split, h_first, h_second, h_second_eq]
    -- (C + (... - f ω)) / (n+1) = (C - f ω)/(n+1) + (n-k+1)/(n+1) * avg
    field_simp
    ring
  -- Now establish three convergence facts.
  -- (a) (C - f ω) / (n+1) → 0.
  have h_inv : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) Filter.atTop (𝓝 0) := by
    have h_nat : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 := h_nat.inv_tendsto_atTop
    refine h2.congr (fun n => ?_)
    simp [one_div]
  have h_a : Filter.Tendsto
      (fun n : ℕ => (C - f ω) / (n + 1 : ℝ)) Filter.atTop (𝓝 0) := by
    have := h_inv.const_mul (C - f ω)
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [mul_one_div]
  -- (b) (n-k+1)/(n+1) → 1.
  have h_b : Filter.Tendsto
      (fun n : ℕ => ((n - k + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) Filter.atTop (𝓝 1) := by
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
    refine Filter.Tendsto.congr' (h_eq.mono (fun n hn => hn.symm)) ?_
    have h_kdiv : Filter.Tendsto
        (fun n : ℕ => (k : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      have h := h_inv.const_mul (k : ℝ)
      simp only [mul_zero] at h
      refine h.congr (fun n => ?_)
      rw [mul_one_div]
    have h_one : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) :=
      tendsto_const_nhds
    have h_sub := h_one.sub h_kdiv
    simp only [sub_zero] at h_sub
    exact h_sub
  -- (c) birkhoffAverageReal T f (n-k) ω → H_k via composing Birkhoff with `n ↦ n-k`.
  have h_c : Filter.Tendsto
      (fun n : ℕ => birkhoffAverageReal p.T f (n - k) ω) Filter.atTop
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
  fun ω => ∑ i ∈ Finset.range n, pmfLogCondMarkov μ p k i ω

omit [DecidableEq α] in
/-- `negLogQk μ p k n / n → conditionalEntropyTail μ p k` a.s. as `n → ∞`. -/
@[entry_point]
theorem negLogQk_div_tendsto_condEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => negLogQk μ p.toStationaryProcess k n ω / n)
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

/-! ## D.3 — Likelihood ratio + Borel–Cantelli -/

/-- The `k`-Markov conditional-kernel mass at the last index of a `Fin (n+1)`-tuple.
For `n ≤ k`: uses the full prefix `Fin.init y : Fin n → α` and the kernel
`condDistrib (obs n) (blockRV n) μ`. For `n > k`: uses the last `k` symbols of
the prefix (a window indexed `n-k+j`) and the kernel
`condDistrib (obs k) (blockRV k) μ`. -/
noncomputable def markovFactor
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k n : ℕ)
    (y : Fin (n + 1) → α) : ℝ≥0∞ :=
  if h : n ≤ k then
    (condDistrib (p.obs n) (p.blockRV n) μ (Fin.init y)) {y (Fin.last n)}
  else
    (condDistrib (p.obs k) (p.blockRV k) μ
        (fun j : Fin k => y ⟨n - k + j,
          by have hk : k ≤ n := Nat.le_of_lt (Nat.lt_of_not_le h)
             omega⟩))
      {y (Fin.last n)}

/-- The `k`-Markov joint mass of a path `y : Fin n → α`, defined recursively as
the product of `markovFactor`s along the path. When evaluated at `y = blockRV n ω`,
this equals (a.s.) `exp(-negLogQk μ p k n ω)`. -/
noncomputable def qkSingleton
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k : ℕ) :
    (n : ℕ) → (Fin n → α) → ℝ≥0∞
  | 0, _ => 1
  | n + 1, y => qkSingleton μ p k n (Fin.init y) * markovFactor μ p k n y

omit [DecidableEq α] in
/-- Per-state, `markovFactor μ p k n` is a genuine probability distribution over the
next symbol: summing over all continuations `a : α` of a fixed prefix `z` gives
exactly `1`. This holds because `markovFactor` is a `condDistrib` kernel singleton
mass and `condDistrib` is an `IsMarkovKernel` (so `kernel z univ = 1`). It is the
enabler for the correct-direction conditional log-sum (the per-step factor of the
`k`-Markov measure is a bona-fide sub-distribution that telescopes to `qkSingleton`). -/
lemma markovFactor_sum_eq_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ)
    (z : Fin n → α) :
    ∑ a : α, markovFactor μ p k n (Fin.snoc z a) = 1 := by
  -- markovFactor only depends on (Fin.init (snoc z a)) = z and (snoc z a) (last n) = a.
  -- For the prefix arg: either Fin.init (snoc z a) = z, or the window
  -- `fun j => snoc z a ⟨n-k+j, _⟩`. Since n-k+j < n (when j < k ≤ n), these
  -- indices fall in `castSucc` range, so `snoc z a` returns `z` at them.
  -- Either way, the prefix arg depends only on z (not a). So we get
  -- ∑_a, kernel(prefix(z)) {a} = (kernel(prefix(z))) univ = 1.
  by_cases hnk : n ≤ k
  · -- Branch n ≤ k: markovFactor = (cd (init (snoc z a))) {(snoc z a)(last n)}
    --                            = (cd z) {a}.
    have h_unfold : ∀ a : α, markovFactor μ p k n (Fin.snoc z a)
        = (condDistrib (p.obs n) (p.blockRV n) μ z) {a} := by
      intro a
      unfold markovFactor
      simp only [hnk, dif_pos, Fin.init_snoc, Fin.snoc_last]
    simp_rw [h_unfold]
    -- ∑_a kernel z {a} = kernel z univ = 1.
    haveI : IsMarkovKernel (condDistrib (p.obs n) (p.blockRV n) μ) := inferInstance
    have h_sum : ∑ a : α, (condDistrib (p.obs n) (p.blockRV n) μ z) {a}
        = (condDistrib (p.obs n) (p.blockRV n) μ z) Set.univ := by
      rw [show (Set.univ : Set α) = (Finset.univ : Finset α) from
        (Finset.coe_univ).symm]
      exact sum_measure_singleton
    rw [h_sum, measure_univ]
  · -- Branch n > k: window uses indices n-k+j where j < k, all < n, so window
    -- only sees z; the kernel arg doesn't depend on a.
    have hkn : k ≤ n := Nat.le_of_lt (Nat.lt_of_not_le hnk)
    have h_unfold : ∀ a : α,
        markovFactor μ p k n (Fin.snoc z a)
          = (condDistrib (p.obs k) (p.blockRV k) μ
              (fun j : Fin k => z ⟨n - k + j.val,
                by have := j.isLt; omega⟩)) {a} := by
      intro a
      unfold markovFactor
      simp only [hnk, dif_neg, not_false_iff]
      -- Compute snoc at last n (singleton arg) and at castSucc indices (kernel arg).
      -- Lock in non-dependent type for snoc: snoc z a : Fin (n+1) → α.
      set sa : Fin (n + 1) → α := Fin.snoc z a with hsa_def
      have h_arg : (fun j : Fin k =>
            sa (⟨n - k + j.val, by have := j.isLt; omega⟩ : Fin (n + 1)))
          = (fun j : Fin k => z ⟨n - k + j.val,
              by have := j.isLt; omega⟩) := by
        funext j
        have h_lt : n - k + j.val < n := by have := j.isLt; omega
        have h_eq : (⟨n - k + j.val,
              (by have := j.isLt; omega : n - k + j.val < n + 1)⟩ : Fin (n + 1))
            = Fin.castSucc ⟨n - k + j.val, h_lt⟩ := by
          apply Fin.ext; simp [Fin.castSucc]
        rw [h_eq]
        show (Fin.snoc z a : Fin (n + 1) → α) (Fin.castSucc ⟨n - k + j.val, h_lt⟩)
            = z ⟨n - k + j.val, h_lt⟩
        exact Fin.snoc_castSucc _ _ _
      have h_last : sa (Fin.last n) = a := Fin.snoc_last _ _
      rw [h_arg, h_last]
    simp_rw [h_unfold]
    haveI : IsMarkovKernel (condDistrib (p.obs k) (p.blockRV k) μ) := inferInstance
    set kern := condDistrib (p.obs k) (p.blockRV k) μ
        (fun j : Fin k => z ⟨n - k + j.val, by have := j.isLt; omega⟩) with hkern_def
    have h_sum : ∑ a : α, kern {a} = kern Set.univ := by
      rw [show (Set.univ : Set α) = (Finset.univ : Finset α) from
        (Finset.coe_univ).symm]
      exact sum_measure_singleton
    rw [h_sum, measure_univ]

/-- The `k`-Markov conditional mass of a length-`ℓ` continuation `w : Fin ℓ → α`
extending a fixed prefix `z : Fin start → α`, defined as the product of
`markovFactor`s at the absolute positions `start, start+1, …, start+ℓ-1`. The tuple
fed to each `markovFactor (start+m)` is the combined prefix `Fin.append z (init…w)`
recast to `Fin ((start+m)+1) → α`. At `ℓ = 0` this is `1`; the recursion peels the
last symbol of `w` via `Fin.init`, matching `qkSingleton`'s chain-rule structure so
the product telescopes to `qkSingleton (start+ℓ) / qkSingleton start`. -/
noncomputable def condQk
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k start : ℕ)
    (z : Fin start → α) :
    (ℓ : ℕ) → (Fin ℓ → α) → ℝ≥0∞
  | 0, _ => 1
  | ℓ + 1, w =>
      condQk μ p k start z ℓ (Fin.init w)
        * markovFactor μ p k (start + ℓ)
            (Fin.append z w ∘ Fin.cast (by omega))

omit [DecidableEq α] in
/-- **Conditional product sub-distribution from a fixed prefix**: for any prefix
`z : Fin start → α`, the `k`-Markov conditional masses of all length-`ℓ`
continuations sum to at most `1`. The non-empty-start generalization of
`sum_qkSingleton_le_one` (which is the `start = 0` case): same induction on `ℓ`,
each step reindexing via `Fin.snocEquiv` and collapsing the inner symbol sum with
`markovFactor_sum_eq_one` (which holds for an arbitrary prefix, hence works from a
non-empty start). This is the per-fixed-context sub-distribution the conditional Ziv
`(k-state, length)` grouping instantiates. -/
lemma condQk_sum_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (k start : ℕ) (z : Fin start → α) (ℓ : ℕ) :
    ∑ w : Fin ℓ → α, condQk μ p k start z ℓ w ≤ 1 := by
  induction ℓ with
  | zero =>
    -- `Fin 0 → α` has a unique element; condQk = 1.
    simp [condQk]
  | succ ℓ ih =>
    -- Same shape as `sum_qkSingleton_le_one`: reindex via snocEquiv, the inner
    -- symbol sum collapses by `markovFactor_sum_eq_one`.
    have h_eq : ∀ w : Fin (ℓ + 1) → α,
        condQk μ p k start z (ℓ + 1) w
          = condQk μ p k start z ℓ (Fin.init w)
              * markovFactor μ p k (start + ℓ)
                  (Fin.append z w ∘ Fin.cast (by omega)) := fun w => rfl
    rw [show (∑ w : Fin (ℓ + 1) → α, condQk μ p k start z (ℓ + 1) w)
          = ∑ w : Fin (ℓ + 1) → α,
              condQk μ p k start z ℓ (Fin.init w)
                * markovFactor μ p k (start + ℓ)
                    (Fin.append z w ∘ Fin.cast (by omega))
        from Finset.sum_congr rfl (fun w _ => h_eq w)]
    -- Reindex via snocEquiv: w ↔ (a, w') with w' = init w, a = w (last ℓ).
    let e : α × (Fin ℓ → α) ≃ (Fin (ℓ + 1) → α) :=
      (Fin.snocEquiv (fun _ : Fin (ℓ + 1) => α))
    have h_reindex : ∑ w : Fin (ℓ + 1) → α,
          condQk μ p k start z ℓ (Fin.init w)
            * markovFactor μ p k (start + ℓ) (Fin.append z w ∘ Fin.cast (by omega))
        = ∑ q : α × (Fin ℓ → α),
            condQk μ p k start z ℓ (Fin.init (e q))
              * markovFactor μ p k (start + ℓ)
                  (Fin.append z (e q) ∘ Fin.cast (by omega)) := by
      symm
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [h_reindex]
    have h_apply : ∀ (a : α) (w' : Fin ℓ → α),
        e (a, w') = Fin.snoc w' a := fun a w' => by
      funext i; simp [e, Fin.snocEquiv]
    -- Convert ∑_{(a, w')} to ∑_{w'} ∑_a and rewrite the kernel arg into snoc form
    -- (so markovFactor only sees `a` at the last position, prefix depends on w' only).
    have h_split :
        ∑ q : α × (Fin ℓ → α),
            condQk μ p k start z ℓ (Fin.init (e q))
              * markovFactor μ p k (start + ℓ) (Fin.append z (e q) ∘ Fin.cast (by omega))
          = ∑ w' : Fin ℓ → α, ∑ a : α,
              condQk μ p k start z ℓ w'
                * markovFactor μ p k (start + ℓ)
                    (Fin.snoc (Fin.append z w' ∘ Fin.cast (by omega)) a) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro w' _
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [h_apply, Fin.init_snoc]
      -- Identify the combined tuple `append z (snoc w' a) ∘ cast` with
      -- `snoc (append z w' ∘ cast) a`, then markovFactor agrees. The core is
      -- `Fin.append_snoc : append z (snoc w' a) = snoc (append z w') a` (the two
      -- sides have defeq lengths `start+(ℓ+1)` vs `(start+ℓ)+1`).
      have htuple : (Fin.append z (Fin.snoc w' a)
              ∘ Fin.cast (by omega : start + (ℓ + 1) = start + ℓ + 1))
          = Fin.snoc (Fin.append z w'
              ∘ Fin.cast (by omega : start + ℓ = start + ℓ)) a := by
        rw [Fin.cast_refl, Function.comp_id, Fin.append_snoc, Fin.cast_refl,
          Function.comp_id]
      rw [htuple]
    rw [h_split]
    have h_pull : ∀ w' : Fin ℓ → α,
        (∑ a : α, condQk μ p k start z ℓ w'
            * markovFactor μ p k (start + ℓ)
                (Fin.snoc (Fin.append z w' ∘ Fin.cast (by omega)) a))
          = condQk μ p k start z ℓ w'
              * ∑ a : α, markovFactor μ p k (start + ℓ)
                  (Fin.snoc (Fin.append z w' ∘ Fin.cast (by omega)) a) := by
      intro w'; rw [Finset.mul_sum]
    simp_rw [h_pull, markovFactor_sum_eq_one, mul_one]
    exact ih

omit [DecidableEq α] in
/-- Per-state sub-distribution: summing `markovFactor μ p k n` over any finite subset
`T` of continuations is at most `1` (subset sum ≤ full sum = `1`). This is the
building block that the conditional Ziv grouping instantiates: a restricted set of
continuations carries at most the full conditional probability mass. -/
lemma markovFactor_sum_subset_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ)
    (z : Fin n → α) (T : Finset α) :
    ∑ a ∈ T, markovFactor μ p k n (Fin.snoc z a) ≤ 1 := by
  calc ∑ a ∈ T, markovFactor μ p k n (Fin.snoc z a)
      ≤ ∑ a : α, markovFactor μ p k n (Fin.snoc z a) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    _ = 1 := markovFactor_sum_eq_one μ p k n z

omit [DecidableEq α] in
/-- **Position invariance of `markovFactor` (the `n > k` branch).** For `n₁, n₂ > k`,
`markovFactor μ p k n` depends only on the last `k + 1` symbols of its argument (the
`k`-symbol window plus the last symbol), not on the absolute position `n`. This is the
foundation of the conditional Ziv `(k-state, length)` grouping: the conditional mass of
a phrase depends only on its trailing `k`-state, so phrases sharing a `k`-state may be
grouped regardless of where they occur. The `n > k` branch of `markovFactor` uses the
fixed kernel `condDistrib (obs k) (blockRV k) μ`, whose argument is the window and whose
singleton set is the last symbol; both agree across `n₁, n₂` under the window/last
hypotheses, so the two factors are equal. -/
lemma markovFactor_eq_of_window_eq
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k : ℕ)
    {n₁ n₂ : ℕ} (h₁ : k < n₁) (h₂ : k < n₂)
    (y₁ : Fin (n₁ + 1) → α) (y₂ : Fin (n₂ + 1) → α)
    (hwin : ∀ j : Fin k, y₁ ⟨n₁ - k + j.val, by have := j.isLt; omega⟩
                       = y₂ ⟨n₂ - k + j.val, by have := j.isLt; omega⟩)
    (hlast : y₁ (Fin.last n₁) = y₂ (Fin.last n₂)) :
    markovFactor μ p k n₁ y₁ = markovFactor μ p k n₂ y₂ := by
  -- Both `n₁, n₂ > k`, so both unfold to the `n > k` (else) branch with the same
  -- fixed kernel `condDistrib (obs k) (blockRV k) μ`. The window argument agrees by
  -- `hwin` (pointwise) and the singleton set agrees by `hlast`.
  have hnk₁ : ¬ n₁ ≤ k := Nat.not_le.mpr h₁
  have hnk₂ : ¬ n₂ ≤ k := Nat.not_le.mpr h₂
  unfold markovFactor
  rw [dif_neg hnk₁, dif_neg hnk₂]
  -- The window-functions are equal:
  have h_arg : (fun j : Fin k => y₁ ⟨n₁ - k + j.val, by have := j.isLt; omega⟩)
      = (fun j : Fin k => y₂ ⟨n₂ - k + j.val, by have := j.isLt; omega⟩) := by
    funext j
    exact hwin j
  rw [h_arg, hlast]

/-- The `k`-Markov conditional masses started from a fixed `k`-state `s : Fin k → α`.
This is `condQk` specialized to `start = k`: the per-`k`-state conditional product
sub-distribution that the `(k-state, length)` Ziv grouping instantiates. -/
noncomputable def condQkState
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k : ℕ)
    (s : Fin k → α) : (ℓ : ℕ) → (Fin ℓ → α) → ℝ≥0∞ :=
  condQk μ p k k s

omit [DecidableEq α] in
/-- The per-`k`-state conditional masses sum to at most `1`: the `start = k`
specialization of `condQk_sum_le_one`. -/
lemma condQkState_sum_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (k : ℕ) (s : Fin k → α) (ℓ : ℕ) :
    ∑ w : Fin ℓ → α, condQkState μ p k s ℓ w ≤ 1 := by
  unfold condQkState
  exact condQk_sum_le_one μ p k k s ℓ

omit [DecidableEq α] in
/-- `∑_y qkSingleton k n y ≤ 1`: the inductive product is bounded by 1 because each
inner sum `∑_a (condDistrib ...){a} = 1` by `IsMarkovKernel`. -/
lemma sum_qkSingleton_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    ∑ y : Fin n → α, qkSingleton μ p k n y ≤ 1 := by
  induction n with
  | zero =>
    -- `Fin 0 → α` has a unique element; qkSingleton = 1.
    simp [qkSingleton]
  | succ n ih =>
    -- Rewrite sum over `Fin (n+1) → α` via `Fin.snocEquiv`:
    -- `∑_y q (n+1) y = ∑_(z,a), q n z * markovFactor n (snoc z a)`
    -- `= ∑_z q n z * (∑_a markovFactor n (snoc z a))`
    -- and the inner sum is 1 by `IsMarkovKernel`.
    have h_eq : ∀ y : Fin (n + 1) → α,
        qkSingleton μ p k (n + 1) y
          = qkSingleton μ p k n (Fin.init y) * markovFactor μ p k n y := by
      intro y; rfl
    rw [show (∑ y : Fin (n + 1) → α, qkSingleton μ p k (n + 1) y)
          = ∑ y : Fin (n + 1) → α,
              qkSingleton μ p k n (Fin.init y) * markovFactor μ p k n y
        from Finset.sum_congr rfl (fun y _ => h_eq y)]
    -- Reindex via snocEquiv: y ↔ (z, a) with z = init y, a = y (last n).
    let e : α × (Fin n → α) ≃ (Fin (n + 1) → α) :=
      (Fin.snocEquiv (fun _ : Fin (n + 1) => α))
    have h_reindex : ∑ y : Fin (n + 1) → α,
          qkSingleton μ p k n (Fin.init y) * markovFactor μ p k n y
        = ∑ p' : α × (Fin n → α),
            qkSingleton μ p k n (Fin.init (e p')) * markovFactor μ p k n (e p') := by
      symm
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [h_reindex]
    -- `e (a, z) = Fin.snoc z a`, so `init (e (a, z)) = z`. The markovFactor part
    -- depends on (a, z) via `snoc z a`.
    have h_apply : ∀ (a : α) (z : Fin n → α),
        e (a, z) = Fin.snoc z a := fun a z => by
      funext i; simp [e, Fin.snocEquiv]
    -- Convert ∑_{(a, z)} f (a, z) to ∑_z ∑_a f (a, z) via Finset.sum_product'.
    have h_split :
        ∑ p' : α × (Fin n → α),
            qkSingleton μ p k n (Fin.init (e p')) * markovFactor μ p k n (e p')
          = ∑ z : Fin n → α, ∑ a : α,
              qkSingleton μ p k n z * markovFactor μ p k n (Fin.snoc z a) := by
      -- LHS in (a, z) ordering: use Fintype.sum_prod_type to get ∑ a ∑ z, then swap.
      rw [Fintype.sum_prod_type]
      -- Goal: ∑ a, ∑ z, ... (with arg (a, z)) = ∑ z, ∑ a, ... (with arg (snoc z a)).
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro z _
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [h_apply, Fin.init_snoc]
    rw [h_split]
    -- Pull out qkSingleton n z and use IsMarkovKernel to compute the inner sum.
    have h_pull : ∀ z : Fin n → α,
        (∑ a : α, qkSingleton μ p k n z * markovFactor μ p k n (Fin.snoc z a))
          = qkSingleton μ p k n z * ∑ a : α, markovFactor μ p k n (Fin.snoc z a) := by
      intro z; rw [Finset.mul_sum]
    simp_rw [h_pull]
    -- Inner sum over a: equals 1 by `markovFactor_sum_eq_one` (per-state probability
    -- distribution over the next symbol, via `IsMarkovKernel`).
    simp_rw [markovFactor_sum_eq_one, mul_one]
    exact ih

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `Fin.init` of `blockRV (n+1) ω` is `blockRV n ω`. -/
private lemma init_blockRV
    (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    Fin.init (p.blockRV (n + 1) ω) = p.blockRV n ω := by
  funext i; rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The last coordinate of `blockRV (n+1) ω` is `obs n ω`. -/
private lemma blockRV_last
    (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    p.blockRV (n + 1) ω (Fin.last n) = p.obs n ω := rfl

omit [DecidableEq α] in
/-- For `n ≤ k`, the `markovFactor` evaluated at `blockRV (n+1) ω` equals the
conditional kernel singleton mass entering `pmfLogCond μ p n ω`. -/
private lemma markovFactor_blockRV_le
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) {k n : ℕ}
    (hnk : n ≤ k) (ω : Ω) :
    markovFactor μ p k n (p.blockRV (n + 1) ω)
      = (condDistrib (p.obs n) (p.blockRV n) μ (p.blockRV n ω)) {p.obs n ω} := by
  unfold markovFactor
  simp only [hnk, dif_pos, init_blockRV, blockRV_last]

omit [DecidableEq α] in
/-- For `k ≤ n`, the `markovFactor` evaluated at `blockRV (n+1) ω` equals the
conditional kernel singleton mass at the shifted point `T^[n-k] ω`. -/
private lemma markovFactor_blockRV_gt
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) {k n : ℕ}
    (hkn : k ≤ n) (ω : Ω) :
    markovFactor μ p k n (p.blockRV (n + 1) ω)
      = (condDistrib (p.obs k) (p.blockRV k) μ
          (p.blockRV k (p.T^[n - k] ω))) {p.obs k (p.T^[n - k] ω)} := by
  unfold markovFactor
  by_cases hnk : n ≤ k
  · -- n ≤ k and k ≤ n ⇒ n = k.
    have hnk_eq : n = k := le_antisymm hnk hkn
    subst hnk_eq
    simp only [le_refl, dif_pos, init_blockRV, blockRV_last,
      Nat.sub_self]
    rfl
  · simp only [hnk, dif_neg, not_false_iff]
    -- Window prefix: `fun j : Fin k => blockRV (n+1) ω ⟨n-k+j, _⟩
    --              = blockRV k (T^[n-k] ω)`.
    have h_arg : (fun j : Fin k => p.blockRV (n + 1) ω
          ⟨n - k + j.val, by have := j.isLt; omega⟩)
        = p.blockRV k (p.T^[n - k] ω) := by
      funext j
      -- LHS: obs (n-k+j.val) ω = X (T^[n-k+j.val] ω) = X (T^[j.val] (T^[n-k] ω))
      -- RHS: obs j.val (T^[n-k] ω) = X (T^[j.val] (T^[n-k] ω)).
      show p.obs (n - k + j.val) ω = p.obs j.val (p.T^[n - k] ω)
      unfold StationaryProcess.obs
      show p.X (p.T^[n - k + j.val] ω) = p.X (p.T^[j.val] (p.T^[n - k] ω))
      rw [← Function.iterate_add_apply p.T j.val (n - k) ω, Nat.add_comm j.val (n - k)]
    -- Last coordinate: `blockRV (n+1) ω (Fin.last n) = obs n ω = obs k (T^[n-k] ω)`.
    have h_last : p.blockRV (n + 1) ω (Fin.last n) = p.obs k (p.T^[n - k] ω) := by
      show p.obs n ω = p.obs k (p.T^[n - k] ω)
      unfold StationaryProcess.obs
      show p.X (p.T^[n] ω) = p.X (p.T^[k] (p.T^[n - k] ω))
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    rw [h_arg, h_last]

omit [DecidableEq α] in
/-- **M1 (bridge for L1)**: a.s., `qkSingleton μ p k n (blockRV n ω)` equals
`ofReal (exp (-negLogQk μ p k n ω))`. -/
lemma qkSingleton_blockRV_eq_ofReal_exp_negLogQk
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    ∀ᵐ ω ∂μ,
      qkSingleton μ p k n (p.blockRV n ω)
        = ENNReal.ofReal (Real.exp (-negLogQk μ p k n ω)) := by
  induction n with
  | zero =>
    refine Filter.Eventually.of_forall (fun ω => ?_)
    -- LHS: qkSingleton k 0 _ = 1; RHS: ofReal (exp(-0)) = ofReal 1 = 1.
    show qkSingleton μ p k 0 (p.blockRV 0 ω)
        = ENNReal.ofReal (Real.exp (-negLogQk μ p k 0 ω))
    unfold negLogQk
    simp [qkSingleton]
  | succ n ih =>
    -- Branch on n ≤ k vs n > k for the new markovFactor.
    by_cases hnk : n ≤ k
    · -- Case n ≤ k: use cond_singleton_pos_ae at n.
      filter_upwards [ih, cond_singleton_pos_ae μ p n] with ω h_ih h_pos
      -- qkSingleton (n+1) (blockRV (n+1) ω)
      --   = qkSingleton n (init (blockRV (n+1) ω)) * markovFactor n (blockRV (n+1) ω)
      --   = qkSingleton n (blockRV n ω) * (cd ...) {obs n ω}                [via M1 helpers]
      --   = ofReal(exp(-negLogQk n ω)) * ofReal(exp(-pmfLogCond μ p n ω))   [by IH and positivity]
      --   = ofReal(exp(-negLogQk n ω - pmfLogCond μ p n ω))
      --   = ofReal(exp(-(negLogQk n ω + pmfLogCond μ p n ω)))
      --   = ofReal(exp(-negLogQk (n+1) ω))                                  [unfolding range_succ]
      have h_qk_succ : qkSingleton μ p k (n + 1) (p.blockRV (n + 1) ω)
          = qkSingleton μ p k n (Fin.init (p.blockRV (n + 1) ω))
            * markovFactor μ p k n (p.blockRV (n + 1) ω) := rfl
      rw [h_qk_succ, init_blockRV, markovFactor_blockRV_le μ p hnk, h_ih]
      -- Now: ofReal(exp(-negLogQk n ω)) * (cd ...){obs n ω} = ofReal(exp(-negLogQk (n+1) ω)).
      set m : ℝ≥0∞ := (condDistrib (p.obs n) (p.blockRV n) μ (p.blockRV n ω)) {p.obs n ω}
        with hm_def
      have h_m_real_pos : 0 < m.toReal := h_pos
      have h_m_ne_zero : m ≠ 0 := by
        intro h
        rw [h] at h_m_real_pos
        simp at h_m_real_pos
      have h_m_ne_top : m ≠ ∞ := by
        -- m ≤ 1 since condDistrib is a Markov kernel.
        have : m ≤ 1 := by
          rw [hm_def]
          exact prob_le_one
        exact ne_top_of_le_ne_top ENNReal.one_ne_top this
      have h_m_eq : m = ENNReal.ofReal m.toReal := (ENNReal.ofReal_toReal h_m_ne_top).symm
      rw [h_m_eq]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      -- exp(-negLogQk n ω) * m.toReal = exp(-negLogQk (n+1) ω).
      -- m.toReal = exp(log m.toReal) = exp(-pmfLogCond μ p n ω) since pmfLogCond n ω = -log m.toReal.
      have h_pmf : pmfLogCond μ p n ω = -Real.log m.toReal := by
        show -Real.log m.toReal = -Real.log m.toReal
        rfl
      have h_exp_pmf : Real.exp (-pmfLogCond μ p n ω) = m.toReal := by
        rw [h_pmf, neg_neg]
        exact Real.exp_log h_m_real_pos
      have h_markov_eq : pmfLogCondMarkov μ p k n ω = pmfLogCond μ p n ω := by
        unfold pmfLogCondMarkov
        simp [hnk]
      have h_negLogQk_succ : negLogQk μ p k (n + 1) ω
          = negLogQk μ p k n ω + pmfLogCondMarkov μ p k n ω := by
        unfold negLogQk
        rw [Finset.sum_range_succ]
      rw [h_negLogQk_succ, h_markov_eq, ← h_exp_pmf]
      rw [neg_add, Real.exp_add]
    · -- Case k < n (n > k). Use shifted cond_singleton_pos_ae.
      have hkn : k ≤ n := (not_le.mp hnk).le
      -- Shifted positivity at T^[n-k] ω.
      have h_shifted_pos : ∀ᵐ ω ∂μ, 0 < (condDistrib (p.obs k) (p.blockRV k) μ
          (p.blockRV k (p.T^[n - k] ω))).real {p.obs k (p.T^[n - k] ω)} :=
        (p.measurePreserving.iterate (n - k)).quasiMeasurePreserving.ae
          (cond_singleton_pos_ae μ p k)
      filter_upwards [ih, h_shifted_pos] with ω h_ih h_pos
      have h_qk_succ : qkSingleton μ p k (n + 1) (p.blockRV (n + 1) ω)
          = qkSingleton μ p k n (Fin.init (p.blockRV (n + 1) ω))
            * markovFactor μ p k n (p.blockRV (n + 1) ω) := rfl
      rw [h_qk_succ, init_blockRV, markovFactor_blockRV_gt μ p hkn, h_ih]
      set m : ℝ≥0∞ := (condDistrib (p.obs k) (p.blockRV k) μ
          (p.blockRV k (p.T^[n - k] ω))) {p.obs k (p.T^[n - k] ω)} with hm_def
      have h_m_real_pos : 0 < m.toReal := h_pos
      have h_m_ne_zero : m ≠ 0 := by
        intro h
        rw [h] at h_m_real_pos
        simp at h_m_real_pos
      have h_m_ne_top : m ≠ ∞ := by
        have : m ≤ 1 := by rw [hm_def]; exact prob_le_one
        exact ne_top_of_le_ne_top ENNReal.one_ne_top this
      have h_m_eq : m = ENNReal.ofReal m.toReal := (ENNReal.ofReal_toReal h_m_ne_top).symm
      rw [h_m_eq]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      have h_pmf_shift : pmfLogCond μ p k (p.T^[n - k] ω) = -Real.log m.toReal := rfl
      have h_exp_pmf : Real.exp (-pmfLogCond μ p k (p.T^[n - k] ω)) = m.toReal := by
        rw [h_pmf_shift, neg_neg]
        exact Real.exp_log h_m_real_pos
      have h_markov_eq : pmfLogCondMarkov μ p k n ω
          = pmfLogCond μ p k (p.T^[n - k] ω) := by
        unfold pmfLogCondMarkov
        simp [hnk]
      have h_negLogQk_succ : negLogQk μ p k (n + 1) ω
          = negLogQk μ p k n ω + pmfLogCondMarkov μ p k n ω := by
        unfold negLogQk
        rw [Finset.sum_range_succ]
      rw [h_negLogQk_succ, h_markov_eq, ← h_exp_pmf]
      rw [neg_add, Real.exp_add]

omit [DecidableEq α] in
/-- A.s. equivalence between the new `MRatioUp` ratio form and the old
exp-of-difference form used by downstream lemmas (`MRatioUp_le_sq_eventually`,
`blockLogAvg_le_negLogQk_plus_error`). -/
lemma MRatioUp_eq_ofReal_exp_old
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    ∀ᵐ ω ∂μ,
      qkSingleton μ p k n (p.blockRV n ω) / (μ.map (p.blockRV n)) {p.blockRV n ω}
        = ENNReal.ofReal (Real.exp (
            (n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω)) := by
  -- M1 handles the numerator; block_singleton_pos_ae_at handles the denominator.
  filter_upwards [qkSingleton_blockRV_eq_ofReal_exp_negLogQk μ p k n,
                  block_singleton_pos_ae_at μ p n] with ω h_qk h_pos
  set P : ℝ≥0∞ := (μ.map (p.blockRV n)) {p.blockRV n ω} with hP_def
  have h_P_real_pos : 0 < P.toReal := h_pos
  have h_P_ne_zero : P ≠ 0 := by
    intro h; rw [h] at h_P_real_pos; simp at h_P_real_pos
  have h_P_ne_top : P ≠ ∞ := by
    have h_prob : IsProbabilityMeasure (μ.map (p.blockRV n)) :=
      Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
    have : P ≤ 1 := by rw [hP_def]; exact prob_le_one
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have h_P_eq : P = ENNReal.ofReal P.toReal := (ENNReal.ofReal_toReal h_P_ne_top).symm
  rw [h_qk]
  -- Goal: ofReal(exp(-negLogQk)) / P = ofReal(exp(n*blockLogAvg - negLogQk)).
  -- Rewrite n*blockLogAvg via the definition: when n ≥ 1, n*blockLogAvg = -log P.toReal,
  -- so exp(n*blockLogAvg - negLogQk) = exp(-log P.toReal) * exp(-negLogQk)
  --                                  = (1/P.toReal) * exp(-negLogQk)
  --                                  = exp(-negLogQk) / P.toReal.
  -- For n = 0: blockLogAvg = -(1/0) * log P = 0 and P.toReal = 1 (block 0 has mass 1).
  by_cases hn : n = 0
  · subst hn
    -- n = 0: negLogQk = 0; P = 1 (empty product); LHS = 1/1 = 1; RHS = ofReal(exp 0) = 1.
    have h_P_one : P = 1 := by
      rw [hP_def]
      have h_meas : Measurable (p.blockRV 0) := p.measurable_blockRV 0
      rw [Measure.map_apply h_meas (measurableSet_singleton _)]
      have h_univ : (p.blockRV 0) ⁻¹' {p.blockRV 0 ω} = Set.univ := by
        ext ω'
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        funext i; exact i.elim0
      rw [h_univ]; exact measure_univ
    rw [h_P_one]
    have h_negLogQk_zero : negLogQk μ p k 0 ω = 0 := by
      unfold negLogQk; simp
    rw [h_negLogQk_zero]
    have h_blockLogAvg_zero : (0 : ℕ) * blockLogAvg μ p 0 ω - (0 : ℝ) = 0 := by
      simp
    rw [show ((0 : ℕ) : ℝ) * blockLogAvg μ p 0 ω - (0 : ℝ) = 0 by simp]
    simp [Real.exp_zero]
  · -- n ≥ 1.
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
    -- n * blockLogAvg μ p n ω = -log P.toReal.
    have h_blockLogAvg_real : ((n : ℝ)) * blockLogAvg μ p n ω = -Real.log P.toReal := by
      unfold blockLogAvg
      show ((n : ℝ)) * (-(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}))
          = -Real.log P.toReal
      have h_P_real_eq : (μ.map (p.blockRV n)).real {p.blockRV n ω} = P.toReal := rfl
      rw [h_P_real_eq]
      field_simp
    rw [h_blockLogAvg_real]
    -- exp(-log P.toReal - negLogQk) = exp(-negLogQk) / P.toReal (in ℝ, P.toReal > 0).
    have h_split : Real.exp (-Real.log P.toReal - negLogQk μ p k n ω)
        = Real.exp (-negLogQk μ p k n ω) / P.toReal := by
      have h_rearr : -Real.log P.toReal - negLogQk μ p k n ω
            = -negLogQk μ p k n ω + -Real.log P.toReal := by ring
      rw [h_rearr, Real.exp_add]
      rw [show Real.exp (-Real.log P.toReal) = (P.toReal)⁻¹ by
        rw [Real.exp_neg, Real.exp_log h_P_real_pos]]
      rw [div_eq_mul_inv]
    rw [h_split]
    -- ofReal (exp(-negLogQk) / P.toReal) = ofReal(exp(-negLogQk)) / ofReal(P.toReal) = ofReal(exp(-negLogQk)) / P.
    rw [ENNReal.ofReal_div_of_pos h_P_real_pos, ← h_P_eq]

/-- Upward likelihood ratio: `exp(n · blockLogAvg - negLogQk)` lifted to ENNReal. -/
noncomputable def MRatioUp
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    Ω → ℝ≥0∞ :=
  fun ω => ENNReal.ofReal (Real.exp (
    (n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω))

omit [DecidableEq α] in
/-- Markov inequality input: the upward ratio integrates to at most `1`.

**Proof**:
1. Bridge `MRatioUp` to the ratio form `qkSingleton k n (blockRV n ω) / P_n {blockRV n ω}`
   a.s. via `MRatioUp_eq_ofReal_exp_old`.
2. Push forward through `blockRV n` using `lintegral_map`, then
   `lintegral_fintype` over the finite alphabet:
   `∑_y qkSingleton k n y / P_n {y} * P_n {y}`.
3. `(a / b) * b ≤ a` (unconditional in ENNReal): bound the sum by `∑_y qkSingleton k n y`.
4. Apply `sum_qkSingleton_le_one`. -/
theorem integral_MRatioUp_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    ∫⁻ ω, MRatioUp μ p k n ω ∂μ ≤ 1 := by
  classical
  -- Step 1: rewrite MRatioUp as qkSingleton/Pn{block_n ω} (a.s.) via L1.
  -- Step 2: push forward via blockRV n; get ∑ y, qk{y}/Pn{y} * Pn{y} ≤ ∑ y, qk{y}.
  -- Step 3: apply sum_qkSingleton_le_one.
  have h_block_meas : Measurable (p.blockRV n) := p.measurable_blockRV n
  have h_Pn_meas : Measurable (fun y : Fin n → α =>
      qkSingleton μ p k n y / (μ.map (p.blockRV n)) {y}) := measurable_of_finite _
  have h_eq_ae := MRatioUp_eq_ofReal_exp_old μ p k n
  -- rewrite goal via a.s. equality:
  -- ∫⁻ ω, MRatioUp ∂μ = ∫⁻ ω, qkSingleton k n (blockRV n ω) / Pn {blockRV n ω} ∂μ
  have h_lintegral_eq :
      ∫⁻ ω, MRatioUp μ p k n ω ∂μ
        = ∫⁻ ω, qkSingleton μ p k n (p.blockRV n ω)
            / (μ.map (p.blockRV n)) {p.blockRV n ω} ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [h_eq_ae] with ω hω
    show MRatioUp μ p k n ω = _
    unfold MRatioUp
    exact hω.symm
  rw [h_lintegral_eq]
  -- Push forward through blockRV n. Use lintegral_map with the composition form.
  have h_push : ∫⁻ ω, qkSingleton μ p k n (p.blockRV n ω)
        / (μ.map (p.blockRV n)) {p.blockRV n ω} ∂μ
      = ∫⁻ y, qkSingleton μ p k n y / (μ.map (p.blockRV n)) {y}
          ∂(μ.map (p.blockRV n)) :=
    (lintegral_map h_Pn_meas h_block_meas).symm
  rw [h_push]
  -- Now: ∫⁻ y, qk{y}/Pn{y} ∂Pn ≤ ∑ y, qk{y}.
  rw [lintegral_fintype]
  -- ∑ y, (qk{y}/Pn{y}) * Pn{y} ≤ ∑ y, qk{y}, then ≤ 1.
  refine le_trans ?_ (sum_qkSingleton_le_one μ p k n)
  refine Finset.sum_le_sum (fun y _ => ?_)
  -- (a / b) * b ≤ a: holds unconditionally in ENNReal via div_mul_cancel' edge cases.
  by_cases hb_zero : (μ.map (p.blockRV n)) {y} = 0
  · simp [hb_zero]
  · by_cases hb_top : (μ.map (p.blockRV n)) {y} = ∞
    · simp [hb_top, ENNReal.div_top]
    · rw [ENNReal.div_mul_cancel hb_zero hb_top]

omit [DecidableEq α] in
/-- Borel–Cantelli consequence: the upward ratio is eventually bounded by `n²` a.s. -/
theorem MRatioUp_le_sq_eventually
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      MRatioUp μ p k n ω ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := by
  -- "Bad" event at index n: `s n = {ω | ofReal n² < MRatioUp k n ω}`.
  -- Markov inequality + integral_MRatioUp_le_one gives μ(s n) ≤ 1/(n^2)
  -- as an ENNReal bound for n ≥ 1. The sum ∑' n, 1/n² is finite (p-series),
  -- so the first Borel-Cantelli (`ae_eventually_notMem`) gives the conclusion.
  set s : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal ((n : ℝ) ^ 2) < MRatioUp μ p k n ω}
    with hs_def
  -- Measurability of MRatioUp.
  have h_MR_meas : ∀ n, Measurable (MRatioUp μ p k n) := by
    intro n
    unfold MRatioUp
    refine ENNReal.measurable_ofReal.comp ?_
    refine Real.measurable_exp.comp ?_
    refine Measurable.sub ?_ ?_
    · exact (measurable_const.mul (measurable_blockLogAvg μ p n))
    · unfold negLogQk
      exact Finset.measurable_sum _
        (fun i _ => measurable_pmfLogCondMarkov μ p k i)
  -- Per-n measure bound: for n ≥ 1, μ(s n) ≤ 1 / (n^2 : ℝ≥0∞).
  have h_bound : ∀ n, 1 ≤ n → μ (s n) ≤ (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2) := by
    intro n hn
    have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h_eps_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h_eps : ENNReal.ofReal ((n : ℝ) ^ 2) = (n : ℝ≥0∞) ^ 2 := by
      rw [show ((n : ℝ) ^ 2) = ((n^2 : ℕ) : ℝ) by push_cast; ring]
      rw [ENNReal.ofReal_natCast]
      push_cast; ring
    have h_eps_ne_zero : ENNReal.ofReal ((n : ℝ) ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr h_eps_pos).ne'
    have h_eps_ne_top : ENNReal.ofReal ((n : ℝ) ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
    -- s n ⊆ {ω | ofReal n² ≤ MRatioUp k n ω} (from `<` to `≤`).
    have h_sub : s n ⊆ {ω | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioUp μ p k n ω} := by
      intro ω hω
      have : ENNReal.ofReal ((n : ℝ) ^ 2) < MRatioUp μ p k n ω := hω
      exact le_of_lt this
    have h_markov : μ {ω | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioUp μ p k n ω}
        ≤ (∫⁻ ω, MRatioUp μ p k n ω ∂μ) / ENNReal.ofReal ((n : ℝ) ^ 2) :=
      meas_ge_le_lintegral_div (h_MR_meas n).aemeasurable h_eps_ne_zero h_eps_ne_top
    have h_int := integral_MRatioUp_le_one μ p k n
    calc μ (s n) ≤ μ {ω | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioUp μ p k n ω} :=
          measure_mono h_sub
      _ ≤ (∫⁻ ω, MRatioUp μ p k n ω ∂μ) / ENNReal.ofReal ((n : ℝ) ^ 2) := h_markov
      _ ≤ 1 / ENNReal.ofReal ((n : ℝ) ^ 2) := by
          exact ENNReal.div_le_div_right h_int _
      _ = 1 / ((n : ℝ≥0∞) ^ 2) := by rw [h_eps]
  -- Sum: ∑' n, μ (s n) ≠ ∞.
  -- For n = 0, the upper bound 1/0 = ∞ in ENNReal is not directly usable,
  -- but μ (s 0) ≤ μ univ ≤ 1, finite. So drop n = 0 via tsum splitting.
  have h_tsum : ∑' n, μ (s n) ≠ ∞ := by
    -- Shift: ∑' n, μ (s n) = μ (s 0) + ∑' n, μ (s (n + 1)), with both finite.
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, ?_⟩
    -- ∑' n, μ (s (n+1)) ≤ ∑' n, 1/((n+1)^2 : ℝ≥0∞) which is finite.
    have h_le : (∑' n : ℕ, μ (s (n + 1))) ≤ ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) := by
      refine ENNReal.tsum_le_tsum (fun n => ?_)
      exact h_bound (n + 1) (Nat.succ_le_succ (Nat.zero_le _))
    refine ne_top_of_le_ne_top ?_ h_le
    -- ∑' n, 1/((n+1)^2 : ℝ≥0∞) < ∞: convert via ofReal of a real summable.
    have h_summable_real : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      exact (summable_nat_add_iff 1).mpr h
    have h_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := fun n => by positivity
    have h_ennreal_tsum : ∑' n : ℕ,
        ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable_real]
      exact ENNReal.ofReal_ne_top
    -- pointwise equal: 1/((n+1)^2 : ℝ≥0∞) = ENNReal.ofReal (1/(n+1)^2).
    have h_pointwise : ∀ n : ℕ,
        (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) =
          ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro n
      have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_one,
        show ((n + 1 : ℕ) : ℝ) ^ 2 = (((n + 1)^2 : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
      push_cast
      ring_nf
    have h_tsum_eq : ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2)
        = ∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      tsum_congr h_pointwise
    rw [h_tsum_eq]
    exact h_ennreal_tsum
  -- Apply first Borel-Cantelli.
  have h_BC := MeasureTheory.ae_eventually_notMem h_tsum
  filter_upwards [h_BC] with ω hω
  -- `ω ∉ s n` means `¬ (n² < MRatioUp k n ω)`, i.e. `MRatioUp k n ω ≤ n²`.
  filter_upwards [hω] with n hn
  exact not_lt.mp hn

-- The downward direction is handled in §D.5 via the 2-sided extension
-- `(ℤ → α, μZ, shiftZ)` and the infinite-past conditional `condProbInfty`. The
-- naive k-Markov downward ratio `exp(negLogQk - n·blockLogAvg) = P_n/q_k`
-- fails to integrate to `≤ 1` (chi-squared blow-up). The correct ratio uses
-- the infinite-past conditional `q_∞`, defined via `pmfLogCondInfty` on the
-- 2-sided side, where `E_μZ[P_n/q_∞] = 1` by the tower property.


/-! ## D.4 — limsup direction -/

omit [DecidableEq α] in
/-- Logarithmic form of `MRatioUp_le_sq_eventually`: pointwise `blockLogAvg`
upper bound by the `k`-Markov approximation plus a `2 log n / n` error. -/
theorem blockLogAvg_le_negLogQk_plus_error
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg μ p n ω ≤ negLogQk μ p k n ω / n + 2 * Real.log n / n := by
  filter_upwards [MRatioUp_le_sq_eventually μ p k] with ω hω
  -- From eventual n ≥ 1 and the ENNReal bound, take log on the real side.
  filter_upwards [hω, Filter.eventually_ge_atTop 1] with n h_MR hn
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_n_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  -- ENNReal.ofReal (exp X) ≤ ENNReal.ofReal (n^2) ⇒ exp X ≤ n^2.
  have h_exp_nn : (0 : ℝ) ≤ Real.exp ((n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω) :=
    (Real.exp_pos _).le
  have h_real_le : Real.exp ((n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω)
      ≤ (n : ℝ) ^ 2 := by
    have : ENNReal.ofReal (Real.exp ((n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω))
        ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := h_MR
    exact (ENNReal.ofReal_le_ofReal_iff h_n_sq_pos.le).mp this
  -- log monotone: X ≤ log (n^2) = 2 log n.
  have h_log : (n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω
      ≤ 2 * Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) h_real_le
    rw [Real.log_exp] at h
    have h_log_sq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      rw [show ((n : ℝ) ^ 2) = (n : ℝ) * (n : ℝ) from sq (n : ℝ),
        Real.log_mul h_n_pos.ne' h_n_pos.ne']
      ring
    rw [h_log_sq] at h
    exact h
  -- Divide by n > 0.
  have h_div : blockLogAvg μ p n ω - negLogQk μ p k n ω / (n : ℝ) ≤
      2 * Real.log (n : ℝ) / (n : ℝ) := by
    have h := div_le_div_of_nonneg_right h_log h_n_pos.le
    rw [sub_div, mul_div_cancel_left₀ _ h_n_pos.ne'] at h
    exact h
  linarith

omit [DecidableEq α] in
/-- Taking `limsup` in `blockLogAvg_le_negLogQk_plus_error` and using
Birkhoff for the `k`-Markov approximation gives the per-`k` limsup bound. -/
@[entry_point]
theorem limsup_blockLogAvg_le_condEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ conditionalEntropyTail μ p.toStationaryProcess k := by
  filter_upwards [blockLogAvg_le_negLogQk_plus_error μ p.toStationaryProcess k,
                  negLogQk_div_tendsto_condEntropyTail μ p k] with ω h_bound h_neg
  -- RHS tendsto: negLogQk / n + 2 log n / n → H_k + 0 = H_k.
  have h_log_div : Filter.Tendsto (fun n : ℕ => 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    -- log n / n → 0 then multiply by 2.
    have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have h_real : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h_comp := h_real.comp tendsto_natCast_atTop_atTop
      refine h_comp.congr (fun n => ?_)
      simp
    have h_mul := h_log.const_mul (2 : ℝ)
    simp only [mul_zero] at h_mul
    refine h_mul.congr (fun n => ?_)
    rw [mul_div_assoc]
  have h_rhs : Filter.Tendsto
      (fun n : ℕ => negLogQk μ p.toStationaryProcess k n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k)) := by
    have := h_neg.add h_log_div
    simpa using this
  -- Use limsup_le_of_le with the eventual bound + tendsto.
  -- We need IsCoboundedUnder for blockLogAvg.
  -- Strategy: limsup ≤ limsup of bound = lim of bound = H_k.
  have h_limsup_bound : Filter.limsup
      (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ => negLogQk μ p.toStationaryProcess k n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ)) Filter.atTop := by
    refine Filter.limsup_le_limsup h_bound ?_ ?_
    · -- IsCoboundedUnder (· ≤ ·) of blockLogAvg: from boundedness below by 0.
      refine (Filter.isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.Eventually.of_forall (fun n => ?_))).isCoboundedUnder_le
      -- Reuse the same nonneg proof from blockLogAvg_bddBelow_ae body.
      have hPn : IsProbabilityMeasure (μ.map (p.toStationaryProcess.blockRV n)) :=
        Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
      have h_le_one : (μ.map (p.toStationaryProcess.blockRV n)).real
          {p.toStationaryProcess.blockRV n ω} ≤ 1 := measureReal_le_one
      have h_nn : 0 ≤ (μ.map (p.toStationaryProcess.blockRV n)).real
          {p.toStationaryProcess.blockRV n ω} := measureReal_nonneg
      have h_log_nonpos : Real.log ((μ.map (p.toStationaryProcess.blockRV n)).real
          {p.toStationaryProcess.blockRV n ω}) ≤ 0 := Real.log_nonpos h_nn h_le_one
      have h_inv_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      have h_neg_inv_nonpos : -(1 / (n : ℝ)) ≤ 0 := neg_nonpos_of_nonneg h_inv_nn
      unfold blockLogAvg
      exact mul_nonneg_of_nonpos_of_nonpos h_neg_inv_nonpos h_log_nonpos
    · exact h_rhs.isBoundedUnder_le
  exact h_limsup_bound.trans h_rhs.limsup_eq.le

omit [DecidableEq α] in
/-- Letting `k → ∞` in the per-`k` bound and using
`entropyRate_eq_lim_condEntropy` discharges the `limsup` hypothesis of
`shannon_mcmillan_breiman_of_sandwich`. -/
@[entry_point]
theorem algoet_cover_limsup_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess := by
  classical
  -- Per-k bound (a.s.): limsup ≤ H_k.
  have h_all : ∀ᵐ ω ∂μ, ∀ k : ℕ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ conditionalEntropyTail μ p.toStationaryProcess k := by
    rw [ae_all_iff]
    intro k
    exact limsup_blockLogAvg_le_condEntropyTail μ p k
  filter_upwards [h_all] with ω hω
  -- `H_k → entropyRate` as k → ∞.
  have h_tail := entropyRate_eq_lim_condEntropy μ p.toStationaryProcess
  exact ge_of_tendsto' h_tail hω

/-! ## D.6 — Boundedness (hoisted before D.5 because the liminf transfer uses
`blockLogAvg_bddAbove_ae` to establish μZ-a.s. upper boundedness of `blockLogAvgZ`). -/

omit [DecidableEq α] in
/-- A.s. boundedness above for `blockLogAvg`.

A.s., `blockLogAvg ≤ negLogQk(k=0)/n + 2·log n / n` (from
`blockLogAvg_le_negLogQk_plus_error`), and the RHS converges a.s. to
`conditionalEntropyTail μ p 0` (finite), hence the RHS is eventually bounded
above and so is `blockLogAvg`. -/
@[entry_point]
theorem blockLogAvg_bddAbove_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => blockLogAvg μ p.toStationaryProcess n ω) := by
  -- log n / n → 0.
  have h_log_div : Filter.Tendsto (fun n : ℕ => 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have h_real : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h_comp := h_real.comp tendsto_natCast_atTop_atTop
      refine h_comp.congr (fun n => ?_)
      simp
    have h_mul := h_log.const_mul (2 : ℝ)
    simp only [mul_zero] at h_mul
    refine h_mul.congr (fun n => ?_)
    rw [mul_div_assoc]
  filter_upwards [blockLogAvg_le_negLogQk_plus_error μ p.toStationaryProcess 0,
                  negLogQk_div_tendsto_condEntropyTail μ p 0] with ω h_bound h_neg
  have h_rhs : Filter.Tendsto
      (fun n : ℕ => negLogQk μ p.toStationaryProcess 0 n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess 0)) := by
    have := h_neg.add h_log_div
    simpa using this
  have h_rhs_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ => negLogQk μ p.toStationaryProcess 0 n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ)) := h_rhs.isBoundedUnder_le
  exact h_rhs_bdd.mono_le h_bound

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- A.s. boundedness below for `blockLogAvg`. -/
@[entry_point]
theorem blockLogAvg_bddBelow_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => blockLogAvg μ p.toStationaryProcess n ω) := by
  -- `blockLogAvg μ p n ω ≥ 0` for every `n` and every `ω`.
  refine Filter.Eventually.of_forall (fun ω => ?_)
  refine Filter.isBoundedUnder_of_eventually_ge (a := 0)
    (Filter.Eventually.of_forall (fun n => ?_))
  have hPn : IsProbabilityMeasure (μ.map (p.blockRV n)) :=
    Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
  have h_le_one : (μ.map (p.blockRV n)).real {p.blockRV n ω} ≤ 1 :=
    measureReal_le_one
  have h_nn : 0 ≤ (μ.map (p.blockRV n)).real {p.blockRV n ω} := measureReal_nonneg
  have h_log_nonpos : Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}) ≤ 0 :=
    Real.log_nonpos h_nn h_le_one
  have h_inv_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have h_neg_inv_nonpos : -(1 / (n : ℝ)) ≤ 0 := neg_nonpos_of_nonneg h_inv_nn
  unfold blockLogAvg
  exact mul_nonneg_of_nonpos_of_nonpos h_neg_inv_nonpos h_log_nonpos

end InformationTheory.Shannon
