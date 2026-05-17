import Common2026.Shannon.SMBChainRule
import Common2026.Shannon.ShannonMcMillanBreiman
import Common2026.Probability.TwoSidedExtension
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# SMB Algoet–Cover sandwich (Phase D — skeleton)

Phase D Algoet–Cover sandwich. Discharges the four hypotheses of
`shannon_mcmillan_breiman_of_sandwich` (`liminf ≥ H`, `limsup ≤ H`, a.s.
boundedness above and below) to produce the hypothesis-free
`shannon_mcmillan_breiman` theorem. The proofs combine the chain rule
`log_block_eq_sum_pmfLogCond`, Birkhoff for the per-step conditional
log-likelihood, a `k`-Markov approximation with conditional entropy
`H_k = conditionalEntropyTail μ p k`, and a likelihood-ratio + Borel–Cantelli
bound to convert expected-value inequalities into a.s. bounds.
-/

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
    -- Inner sum over a: equals 1 by IsMarkovKernel (kernel univ = 1, on a finite alphabet
    -- this means ∑_a kernel {a} = 1).
    have h_inner : ∀ z : Fin n → α,
        ∑ a : α, markovFactor μ p k n (Fin.snoc z a) = 1 := by
      intro z
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
    simp_rw [h_inner, mul_one]
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

/-- Letting `k → ∞` in the per-`k` bound and using
`entropyRate_eq_lim_condEntropy` discharges the `limsup` hypothesis of
`shannon_mcmillan_breiman_of_sandwich`. -/
theorem algoet_cover_limsup_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess := by
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

/-! ## D.5 — liminf direction (2-sided infinite-past detour)

The liminf direction `liminf blockLogAvg ≥ entropyRate` cannot be obtained from
the one-sided k-Markov approximation alone: the ratio `P_n/q_k` has unbounded
chi-squared expectation. The fix (Algoet–Cover 1988) is to use the **infinite
past** conditional `q_∞(X_0^{n-1}|past_∞) = ∏ μZ(X_i|X_{-∞}^{i-1})`, defined on
the 2-sided extension `(ℤ → α, μZ, shiftZ)` (see `TwoSidedExtension.lean`).

By the tower property, `E_μZ[P_n/q_∞] = 1`, so Markov + Borel–Cantelli give
`P_n/q_∞ ≤ n²` eventually μZ-a.s. Logarithmically, this is
`blockLogAvgZ ≥ (1/n) Σ pmfLogCondInfty - 2 log n / n`. Birkhoff applied to
`pmfLogCondInfty` on the 2-sided ergodic system gives
`(1/n) Σ pmfLogCondInfty(shiftZ^[i] x) → ∫ pmfLogCondInfty dμZ = entropyRate`,
so `liminf blockLogAvgZ ≥ entropyRate` μZ-a.s. We transfer to the Ω-side via
`forwardEmbed` and the measure-preservation `μ.map forwardEmbed = μZ.map natProj`.
-/

open InformationTheory.Shannon.TwoSided

/-- **First-`n` block projection on the 2-sided side**: pulls out `x_0, …, x_{n-1}`. -/
noncomputable def firstBlockZ (n : ℕ) : (∀ _ : ℤ, α) → (Fin n → α) :=
  fun x i => x (i.val : ℤ)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma measurable_firstBlockZ (n : ℕ) :
    Measurable (firstBlockZ (α := α) n) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

omit [DecidableEq α] [Nonempty α] in
/-- The first-`n` block on the 2-sided side has the same law as `blockRV n` on Ω. -/
lemma map_firstBlockZ_eq_map_blockRV
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (μZ μ p).map (firstBlockZ (α := α) n) = μ.map (p.blockRV n) := by
  classical
  -- Both sides are probability measures on `Fin n → α` (finite codomain).
  haveI hLHS_prob : IsProbabilityMeasure
      ((μZ μ p).map (firstBlockZ (α := α) n)) :=
    Measure.isProbabilityMeasure_map (measurable_firstBlockZ n).aemeasurable
  haveI hRHS_prob : IsProbabilityMeasure (μ.map (p.blockRV n)) :=
    Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
  -- Suffices to show equality on singletons (finite type).
  refine Measure.ext_of_singleton ?_
  intro s
  rw [Measure.map_apply (measurable_firstBlockZ n) (measurableSet_singleton _),
      Measure.map_apply (p.measurable_blockRV n) (measurableSet_singleton _)]
  -- Now: μZ {x | firstBlockZ n x = s} = μ {ω | p.blockRV n ω = s}.
  -- The LHS preimage is `{x | ∀ i : Fin n, x (i.val : ℤ) = s i}`, a 2-sided
  -- cylinder. The RHS is `μ.map (p.blockRV n) {s}`. Apply `μZ_block_cylinder_eq`.
  have h_LHS_eq : (firstBlockZ (α := α) n) ⁻¹' {s}
      = { x : (∀ _ : ℤ, α) | ∀ i : Fin n, x ((i : ℕ) : ℤ) = s i } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hx i
      show x ((i : ℕ) : ℤ) = s i
      rw [show ((i : ℕ) : ℤ) = (i.val : ℤ) from rfl]
      exact congr_fun hx i
    · intro h
      funext i
      show x (i.val : ℤ) = s i
      have := h i
      simpa using this
  rw [h_LHS_eq]
  -- Now: μZ {x | ∀ i, x ((i : ℕ) : ℤ) = s i} = μ.map (p.blockRV n) {s} (by μZ_block_cylinder_eq).
  -- Then unfold μ.map ... = μ (preimage ...).
  rw [μZ_block_cylinder_eq μ p n s]
  rw [Measure.map_apply (p.measurable_blockRV n) (measurableSet_singleton _)]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Z-side blockLogAvg**: the per-symbol negative log-likelihood on the 2-sided side. -/
noncomputable def blockLogAvgZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (∀ _ : ℤ, α) → ℝ :=
  fun x => -(1 / (n : ℝ)) *
    Real.log (((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x})

omit [DecidableEq α] [Nonempty α] in
/-- Bridge: `blockLogAvgZ n (natural extension of ω) = blockLogAvg n ω`. The
"natural extension" `fun i : ℤ => p.obs i.toNat ω` ignores negative coords
(maps them to `p.obs 0 ω = X ω`), but `blockLogAvgZ n` only looks at coords
`{0, …, n-1}`, where it agrees with `forwardEmbed`. -/
lemma blockLogAvgZ_natExt_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    blockLogAvgZ μ p n
        (fun i : ℤ => p.obs i.toNat ω) = blockLogAvg μ p n ω := by
  classical
  -- The 2-sided extension at integer coord `i ≥ 0` is `p.obs i ω`.
  unfold blockLogAvgZ blockLogAvg
  -- The argument: `firstBlockZ n (extension ω) = blockRV n ω`.
  have h_args : (firstBlockZ (α := α) n) (fun i : ℤ => p.obs i.toNat ω)
      = p.blockRV n ω := by
    funext i
    show p.obs ((i.val : ℤ).toNat) ω = p.obs i.val ω
    simp
  rw [h_args]
  -- The two measures (μZ.map firstBlockZ n) and (μ.map blockRV n) coincide.
  rw [map_firstBlockZ_eq_map_blockRV μ p n]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Z-side negLogQ∞**: Birkhoff sum of `pmfLogCondInfty` along the orbit. -/
noncomputable def negLogQInftyZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (∀ _ : ℤ, α) → ℝ :=
  fun x => ∑ i ∈ Finset.range n, pmfLogCondInfty μ p (shiftZ^[i] x)

/-- **The Z-side lower-bound likelihood ratio**: `exp(negLogQ∞ - n · blockLogAvgZ)`,
which represents `P_n/q_∞` lifted to `ℝ≥0∞`. -/
noncomputable def MRatioLowerZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (∀ _ : ℤ, α) → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x))

/-! ### Inductive-step infrastructure for `integral_MRatioLowerZ_le_one` -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Probability ratio at the `(n+1)`-block over the `n`-block**: when `P_n(s) > 0`,
this is `P_{n+1}(snoc(s, a)) / P_n(s)`; defaulted to `0` when `P_n(s) = 0`. -/
private noncomputable def blockCondRatio
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (s : Fin n → α) (a : α) : ℝ :=
  let P_n : ℝ := ((μZ μ p).map (firstBlockZ (α := α) n)).real {s}
  let P_succ : ℝ :=
    ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a}
  if P_n = 0 then 0 else P_succ / P_n

omit [DecidableEq α] [Nonempty α] in
/-- `blockCondRatio` is measurable (as a discrete map `Fin n → α → α → ℝ`). -/
private lemma measurable_blockCondRatio_apply
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (a : α) :
    Measurable (fun s : Fin n → α => blockCondRatio μ p n s a) :=
  measurable_of_finite _

omit [DecidableEq α] [Nonempty α] in
/-- Sum of `blockCondRatio` over `a : α` equals `1` whenever `P_n(s) > 0`. -/
private lemma sum_blockCondRatio
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (s : Fin n → α)
    (hs_pos : 0 < ((μZ μ p).map (firstBlockZ (α := α) n)).real {s}) :
    ∑ a, blockCondRatio μ p n s a = 1 := by
  classical
  -- Use that `∑_a (μZ.map firstBlockZ (n+1)) {snoc s a} = (μZ.map firstBlockZ n) {s}`.
  -- Then divide both sides by P_n > 0.
  set P_n : ℝ := ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} with hP_n_def
  have hP_n_ne : P_n ≠ 0 := hs_pos.ne'
  -- Each summand equals `(μZ.map firstBlockZ (n+1)) {snoc s a} / P_n`.
  have h_each : ∀ a, blockCondRatio μ p n s a
      = ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} / P_n := by
    intro a
    show (if ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} = 0 then 0
        else ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} /
              ((μZ μ p).map (firstBlockZ (α := α) n)).real {s})
        = ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} / P_n
    rw [← hP_n_def, if_neg hP_n_ne]
  simp_rw [h_each, ← Finset.sum_div]
  -- Now show `∑_a (μZ.map firstBlockZ (n+1)) {snoc s a} = P_n`.
  have h_sum :
      ∑ a, ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} = P_n := by
    -- Use that `Fin.init (firstBlockZ (n+1) x) = firstBlockZ n x`, so the union of
    -- `{Fin.snoc s a}` over a is the preimage of `{s}` under `Fin.init`.
    have h_init : ∀ (x : ∀ _ : ℤ, α),
        Fin.init (firstBlockZ (α := α) (n + 1) x) = firstBlockZ (α := α) n x := by
      intro x
      funext i
      show firstBlockZ (n + 1) x i.castSucc = firstBlockZ n x i
      show x (i.castSucc.val : ℤ) = x (i.val : ℤ)
      have h_eq : (i.castSucc : Fin (n+1)).val = i.val := rfl
      rw [h_eq]
    -- Express `P_n = ∑_a (μZ.map firstBlockZ (n+1)) {snoc s a}` via
    -- pushforward of `Fin.init`.
    have h_eq : ((μZ μ p).map (firstBlockZ (α := α) n)).real {s}
        = ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real
            (Fin.init ⁻¹' {s} : Set (Fin (n + 1) → α)) := by
      have h_factor : firstBlockZ (α := α) n
          = Fin.init ∘ firstBlockZ (α := α) (n + 1) := by
        funext x i
        exact (h_init x).symm.symm ▸ rfl
      have h_init_meas : Measurable (Fin.init : (Fin (n + 1) → α) → (Fin n → α)) :=
        measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
      rw [h_factor, ← Measure.map_map h_init_meas (measurable_firstBlockZ (n + 1))]
      rw [Measure.real, Measure.map_apply h_init_meas (measurableSet_singleton _),
        ← Measure.real]
    -- And the preimage `Fin.init ⁻¹' {s}` is `⋃_a {Fin.snoc s a}` (disjoint).
    have h_preim : (Fin.init ⁻¹' {s} : Set (Fin (n + 1) → α))
        = ⋃ a : α, {Fin.snoc s a} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
      constructor
      · intro h_init_t
        refine ⟨t (Fin.last n), ?_⟩
        -- t = Fin.snoc (Fin.init t) (t (Fin.last n)) = Fin.snoc s (t (Fin.last n)).
        rw [← h_init_t]
        exact (Fin.snoc_init_self t).symm
      · rintro ⟨a, h_t_eq⟩
        rw [h_t_eq, Fin.init_snoc]
    rw [hP_n_def, h_eq, h_preim]
    -- Now `(μZ.map firstBlockZ (n+1)) (⋃_a {snoc s a}) = ∑_a (μZ.map firstBlockZ (n+1)) {snoc s a}`.
    -- `Fin.snoc s` is injective in `a` (since `(snoc s a) (Fin.last n) = a`).
    have h_inj : Function.Injective (fun a : α => (Fin.snoc s a : Fin (n + 1) → α)) := by
      intro a₁ a₂ h_eq_snoc
      have := congr_fun h_eq_snoc (Fin.last n)
      simp only [Fin.snoc_last] at this
      exact this
    -- Singletons are pairwise disjoint.
    have h_disj :
        Pairwise (Function.onFun Disjoint
          (fun a : α => ({Fin.snoc s a} : Set (Fin (n + 1) → α)))) := by
      intro a₁ a₂ hab
      simp only [Function.onFun, Set.disjoint_singleton]
      intro h
      exact hab (h_inj h)
    -- iUnion = biUnion (over Finset.univ).
    have h_iUnion_to_biUnion :
        (⋃ a : α, ({Fin.snoc s a} : Set (Fin (n + 1) → α)))
          = ⋃ a ∈ (Finset.univ : Finset α), ({Fin.snoc s a} : Set _) := by
      ext t; simp
    rw [h_iUnion_to_biUnion]
    rw [measureReal_biUnion_finset (fun a _ b _ hab => h_disj hab)
      (fun a _ => measurableSet_singleton _)]
  rw [h_sum, div_self hP_n_ne]

omit [DecidableEq α] [Nonempty α] in
/-- **A.s. positivity of `P_n^Z`**: the singleton mass at the realized
`firstBlockZ n x` is a.s. positive under `μZ`.

Transferred from the Ω-side `block_singleton_pos_ae_at` via `map_firstBlockZ_eq_map_blockRV`. -/
private lemma firstBlockZ_singleton_pos_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ x ∂(μZ μ p), 0 < ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x} := by
  classical
  -- The "bad" set is a finite (hence measurable) set in `Fin n → α` of zero measure,
  -- and its preimage under `firstBlockZ n` has μZ-measure 0.
  set S : Set (Fin n → α) :=
    {s | ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} = 0} with hS_def
  have h_S_finite : S.Finite := Set.toFinite S
  have h_S_meas : MeasurableSet S := h_S_finite.measurableSet
  -- (μZ.map firstBlockZ n) S = 0 (sum over finite S of singleton masses = 0).
  have h_S_zero : ((μZ μ p).map (firstBlockZ (α := α) n)) S = 0 := by
    have hS_eq : S = (h_S_finite.toFinset : Set (Fin n → α)) :=
      (Set.Finite.coe_toFinset h_S_finite).symm
    rw [hS_eq, ← sum_measure_singleton]
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hs_mem : s ∈ S := by rwa [Set.Finite.mem_toFinset] at hs
    have hs_real : ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} = 0 := hs_mem
    have h_lt : ((μZ μ p).map (firstBlockZ (α := α) n)) {s} < ∞ := measure_lt_top _ _
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hs_real
    exact hs_real.resolve_right h_lt.ne
  -- Pull back to μZ via `firstBlockZ ⁻¹`.
  have h_preim : (μZ μ p) ((firstBlockZ (α := α) n) ⁻¹' S) = 0 := by
    rw [← Measure.map_apply (measurable_firstBlockZ n) h_S_meas]
    exact h_S_zero
  refine ae_iff.mpr ?_
  refine measure_mono_null ?_ h_preim
  intro x hx
  simp only [Set.mem_setOf_eq, not_lt] at hx
  show x ∈ (firstBlockZ (α := α) n) ⁻¹' S
  simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
  exact le_antisymm hx measureReal_nonneg

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Pointwise factorization of `exp(negLogQInftyZ (n+1))`**:
splits off the new contribution `exp(pmfLogCondInfty(shift^n x))`. -/
private lemma exp_negLogQInftyZ_succ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ)
    (x : ∀ _ : ℤ, α) :
    Real.exp (negLogQInftyZ μ p (n + 1) x)
      = Real.exp (negLogQInftyZ μ p n x)
        * Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)) := by
  unfold negLogQInftyZ
  rw [Finset.sum_range_succ]
  rw [Real.exp_add]

omit [DecidableEq α] [Nonempty α] in
/-- **Pointwise factorization of `MRatioLowerZ (n+1)` on the a.s. positive set**.

On the set where both `P_n(firstBlockZ n x) > 0` and `P_{n+1}(firstBlockZ (n+1) x) > 0`,
we have the decomposition
`MRatioLowerZ (n+1) x = MRatioLowerZ n x · ofReal(blockCondRatio · exp(pmfLogCondInfty(shift^n x)))`,
where `blockCondRatio` is the chain-rule ratio. -/
private lemma MRatioLowerZ_succ_eq_mul
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ)
    (x : ∀ _ : ℤ, α)
    (hPn_pos : 0 < ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x})
    (hPsucc_pos :
      0 < ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {firstBlockZ (n + 1) x}) :
    MRatioLowerZ μ p (n + 1) x
      = MRatioLowerZ μ p n x
        * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) (x (n : ℤ)))
        * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))) := by
  classical
  unfold MRatioLowerZ
  -- Rewrite both sides as `ofReal` of real expressions, then handle in ℝ.
  set Pn : ℝ := ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x} with hPn_def
  set Psucc : ℝ := ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {firstBlockZ (n + 1) x}
    with hPsucc_def
  -- `blockLogAvgZ n x = -(1/n) * log Pn`, so `n * blockLogAvgZ = -log Pn`.
  -- For n = 0, blockLogAvgZ 0 x = -(1/0) * 0 = 0 in Lean (since `1/0 = 0` in ℝ).
  -- For n ≥ 1 with Pn > 0, `exp(-n * blockLogAvgZ n x) = Pn`.
  have h_n_succ_avg : Real.exp (-((n : ℝ) + 1) * blockLogAvgZ μ p (n + 1) x) = Psucc := by
    unfold blockLogAvgZ
    rw [show -((n : ℝ) + 1) * (-(1 / ((n + 1 : ℕ) : ℝ))
            * Real.log Psucc)
          = Real.log Psucc by
          have h_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          push_cast
          field_simp,
        Real.exp_log hPsucc_pos]
  have h_n_avg : Real.exp (-(n : ℝ) * blockLogAvgZ μ p n x) = Pn := by
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
      -- Pn for n = 0 is `((μZ.map firstBlockZ 0).real {firstBlockZ 0 x})` which is the unique map.
      -- firstBlockZ 0 maps everyone to the empty function; mass = total = 1.
      show 1 = Pn
      rw [hPn_def]
      have h_meas : Measurable (firstBlockZ (α := α) 0) := measurable_firstBlockZ 0
      rw [Measure.real, Measure.map_apply h_meas (measurableSet_singleton _)]
      have h_univ : (firstBlockZ (α := α) 0) ⁻¹' {firstBlockZ 0 x} = Set.univ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        funext i; exact i.elim0
      rw [h_univ, measure_univ]; rfl
    · unfold blockLogAvgZ
      have h_n_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      rw [show -(n : ℝ) * (-(1 / (n : ℝ)) * Real.log Pn) = Real.log Pn by field_simp,
        Real.exp_log hPn_pos]
  -- LHS: `ofReal(exp(negLogQ_{n+1}) * exp(-(n+1) blockLogAvgZ_{n+1}))`
  --    = `ofReal(exp(negLogQ_n) * exp(pmfLogCondInfty(shift^n x)) * Psucc)`.
  have hLHS_arg : negLogQInftyZ μ p (n + 1) x - ((n + 1 : ℕ) : ℝ) * blockLogAvgZ μ p (n + 1) x
      = (negLogQInftyZ μ p n x + pmfLogCondInfty μ p (shiftZ^[n] x))
        + (-((n : ℝ) + 1) * blockLogAvgZ μ p (n + 1) x) := by
    unfold negLogQInftyZ
    rw [Finset.sum_range_succ]; push_cast; ring
  rw [hLHS_arg, Real.exp_add, Real.exp_add, h_n_succ_avg]
  -- RHS: `MRatioLowerZ n x * ofReal(blockCondRatio) * ofReal(exp(pmfLogCondInfty))`.
  -- `MRatioLowerZ n x = ofReal(exp(negLogQ_n) * Pn) on positive set`.
  have hMR_n : ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x
        - (n : ℝ) * blockLogAvgZ μ p n x))
      = ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x) * Pn) := by
    congr 1
    rw [show negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x
        = negLogQInftyZ μ p n x + (-(n : ℝ) * blockLogAvgZ μ p n x) by ring]
    rw [Real.exp_add, h_n_avg]
  rw [hMR_n]
  -- `blockCondRatio μ p n (firstBlockZ n x) (x n) = Psucc / Pn` (since `firstBlockZ (n+1) x =
  -- snoc(firstBlockZ n x, x n)`).
  have h_snoc : firstBlockZ (α := α) (n + 1) x
      = (Fin.snoc (firstBlockZ n x) (x (n : ℤ)) : Fin (n + 1) → α) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last n
      show x (((Fin.last n).val : ℕ) : ℤ)
        = (Fin.snoc (firstBlockZ (α := α) n x) (x (n : ℤ)) : Fin (n + 1) → α) (Fin.last n)
      rw [Fin.snoc_last]
      show x (((Fin.last n).val : ℕ) : ℤ) = x (n : ℤ)
      congr 1
    · intro j
      show firstBlockZ (n + 1) x j.castSucc
        = (Fin.snoc (firstBlockZ (α := α) n x) (x (n : ℤ)) : Fin (n + 1) → α) j.castSucc
      rw [Fin.snoc_castSucc]
      show x ((j.castSucc.val : ℤ)) = x ((j.val : ℤ))
      have h_eq : (j.castSucc : Fin (n+1)).val = j.val := rfl
      rw [h_eq]
  have h_ratio : blockCondRatio μ p n (firstBlockZ n x) (x (n : ℤ)) = Psucc / Pn := by
    show (if ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x} = 0 then 0
        else ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real
            {Fin.snoc (firstBlockZ n x) (x (n : ℤ))} /
            ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x})
        = Psucc / Pn
    rw [if_neg (by rw [← hPn_def]; exact hPn_pos.ne'),
        show Fin.snoc (firstBlockZ (α := α) n x) (x (n : ℤ)) = firstBlockZ (n + 1) x from h_snoc.symm,
        ← hPn_def, ← hPsucc_def]
  rw [h_ratio]
  -- Combine via `ENNReal.ofReal_mul`.
  have h_exp_nn : 0 ≤ Real.exp (negLogQInftyZ μ p n x) := (Real.exp_pos _).le
  have h_exp_pos : 0 < Real.exp (negLogQInftyZ μ p n x) := Real.exp_pos _
  have h_pn_pos : 0 < Pn := hPn_pos
  have h_psucc_pos : 0 < Psucc := hPsucc_pos
  have h_pcondInfty_pos : 0 < Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)) := Real.exp_pos _
  -- LHS: ofReal( (exp Q_n) * (exp pmf) * Psucc )
  -- RHS: ofReal( (exp Q_n) * Pn ) * ofReal( Psucc/Pn ) * ofReal( exp pmf )
  --    = ofReal( exp Q_n * Pn * Psucc/Pn * exp pmf )
  --    = ofReal( exp Q_n * exp pmf * Psucc )
  rw [show Real.exp (negLogQInftyZ μ p n x) * Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)) * Psucc
        = Real.exp (negLogQInftyZ μ p n x) * Psucc * Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))
        by ring]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_mul h_exp_nn]
  -- Goal: ofReal(exp Qn) * ofReal Psucc * ofReal(exp pmf)
  --     = ofReal(exp Qn * Pn) * ofReal(Psucc/Pn) * ofReal(exp pmf).
  congr 1
  -- Goal: ofReal(exp Qn) * ofReal Psucc = ofReal(exp Qn * Pn) * ofReal(Psucc/Pn).
  rw [ENNReal.ofReal_mul h_exp_nn]
  rw [show Psucc / Pn = Psucc * (1 / Pn) by ring]
  rw [ENNReal.ofReal_mul h_psucc_pos.le]
  -- Goal: ofReal(exp Qn) * ofReal Psucc = ofReal(exp Qn) * ofReal Pn * (ofReal Psucc * ofReal (1/Pn))
  rw [show ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x)) * ENNReal.ofReal Pn
        * (ENNReal.ofReal Psucc * ENNReal.ofReal (1 / Pn))
      = ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x)) * ENNReal.ofReal Psucc
        * (ENNReal.ofReal Pn * ENNReal.ofReal (1 / Pn)) by ring]
  rw [← ENNReal.ofReal_mul h_pn_pos.le, mul_one_div, div_self h_pn_pos.ne']
  simp

/-- **ENNReal pull-out for indicator factor** (special case of the pull-out property
for the conditional Lebesgue expectation). If `m ≤ m₀`, `μ.trim` σ-finite, `B ∈ m`,
and `f : Ω → ℝ≥0∞`, then `∫⁻ x, B.indicator(1) · f dμ = ∫⁻ x, B.indicator(1) · μ⁻[f|m] dμ`.

Direct consequence of `setLIntegral_condLExp` since `B ∈ m`. -/
private lemma lintegral_indicator_mul_eq
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀)
    [SigmaFinite (μ.trim hm)]
    {B : Set Ω} (hB : MeasurableSet[m] B) (f : Ω → ℝ≥0∞) :
    ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * f x ∂μ
      = ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * μ⁻[f|m] x ∂μ := by
  -- LHS = ∫⁻ x in B, f dμ via indicator/restrict, then setLIntegral_condLExp.
  have h_rw : ∀ (h : Ω → ℝ≥0∞),
      ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * h x ∂μ = ∫⁻ x in B, h x ∂μ := by
    intro h
    rw [show (fun x => B.indicator (fun _ => (1 : ℝ≥0∞)) x * h x)
          = B.indicator (fun x => 1 * h x) from ?_]
    · rw [MeasureTheory.lintegral_indicator (hm _ hB)]
      simp
    · funext x
      by_cases hx : x ∈ B
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
  rw [h_rw, h_rw, MeasureTheory.setLIntegral_condLExp hm μ f hB]

/-- **ENNReal pull-out (general)**: for `g : Ω → ℝ≥0∞` `m`-measurable and `f : Ω → ℝ≥0∞`
measurable, `∫⁻ x, g · f dμ = ∫⁻ x, g · μ⁻[f|m] dμ`. -/
private lemma lintegral_mul_eq_lintegral_mul_condLExp
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀)
    [SigmaFinite (μ.trim hm)]
    {g : Ω → ℝ≥0∞} (hg : Measurable[m] g)
    {f : Ω → ℝ≥0∞} (hf : @Measurable Ω ℝ≥0∞ m₀ _ f) :
    ∫⁻ x, g x * f x ∂μ = ∫⁻ x, g x * μ⁻[f|m] x ∂μ := by
  classical
  -- Approximate g by m-simple functions sn ↑ g.
  set sn : ℕ → @SimpleFunc Ω m ℝ≥0∞ := SimpleFunc.eapprox g with hsn_def
  have h_sn_mono : ∀ x, Monotone (fun n => (sn n : Ω → ℝ≥0∞) x) :=
    fun x i j hij => SimpleFunc.monotone_eapprox _ hij x
  have h_g_iSup : ∀ x, g x = ⨆ n, (sn n : Ω → ℝ≥0∞) x :=
    fun x => (SimpleFunc.iSup_eapprox_apply hg x).symm
  have h_sn_meas_m₀ : ∀ n, @Measurable Ω ℝ≥0∞ m₀ _ (sn n : Ω → ℝ≥0∞) :=
    fun n => ((sn n).measurable).mono hm le_rfl
  have h_cL_meas : Measurable[m] (μ⁻[f|m]) := MeasureTheory.measurable_condLExp m μ f
  have h_cL_meas_m₀ : @Measurable Ω ℝ≥0∞ m₀ _ (μ⁻[f|m]) := h_cL_meas.mono hm le_rfl
  -- Pointwise: g x * h x = ⨆ n, (sn n x) * h x (since ⨆ commutes with mul).
  have h_g_mul_iSup : ∀ (h : Ω → ℝ≥0∞), (fun x => g x * h x)
      = fun x => ⨆ n, (sn n : Ω → ℝ≥0∞) x * h x := by
    intro h
    funext x
    rw [h_g_iSup, ENNReal.iSup_mul]
  have h_mono_mul : ∀ (h : Ω → ℝ≥0∞) x, Monotone (fun n => (sn n : Ω → ℝ≥0∞) x * h x) := by
    intro h x i j hij
    have h_nn : (0 : ℝ≥0∞) ≤ h x := bot_le
    exact mul_le_mul_of_nonneg_right (h_sn_mono x hij) h_nn
  have h_meas_mul : ∀ (h : Ω → ℝ≥0∞), @Measurable Ω ℝ≥0∞ m₀ _ h →
      ∀ n, @Measurable Ω ℝ≥0∞ m₀ _ (fun x => (sn n : Ω → ℝ≥0∞) x * h x) :=
    fun h hh n => Measurable.mul (h_sn_meas_m₀ n) hh
  -- Step A: each simple function step holds, using linearity + lintegral_indicator_mul_eq.
  have h_step : ∀ n, ∫⁻ x, (sn n : Ω → ℝ≥0∞) x * f x ∂μ
      = ∫⁻ x, (sn n : Ω → ℝ≥0∞) x * μ⁻[f|m] x ∂μ := by
    intro n
    -- Decompose sn n via its range.
    have h_sn_decomp : ∀ x, (sn n : Ω → ℝ≥0∞) x
        = ∑ c ∈ (sn n).range, c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro x
      rw [Finset.sum_eq_single (sn n x)]
      · simp
      · intro c _ hc
        have h_notmem : x ∉ (sn n) ⁻¹' {c} := fun hx => hc hx.symm
        simp [Set.indicator_of_notMem h_notmem]
      · intro hcontra
        exact absurd (SimpleFunc.mem_range_self _ x) hcontra
    have h_decomp : ∀ x (h : Ω → ℝ≥0∞), (sn n : Ω → ℝ≥0∞) x * h x
        = ∑ c ∈ (sn n).range, (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * h x := by
      intro x h
      rw [h_sn_decomp x, Finset.sum_mul]
    have h_preim_meas : ∀ c, MeasurableSet[m] ((sn n) ⁻¹' {c}) :=
      fun c => (sn n).measurableSet_fiber c
    have h_preim_lt_top : ∀ c ∈ (sn n).range, c ≠ ∞ := by
      intro c hc
      rcases SimpleFunc.mem_range.mp hc with ⟨x, rfl⟩
      exact (SimpleFunc.eapprox_lt_top g n x).ne
    have h_per_c_LHS : ∀ c (h : Ω → ℝ≥0∞), c ≠ ∞ →
        ∫⁻ x, (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * h x ∂μ
          = c * ∫⁻ x, ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x * h x ∂μ := by
      intro c h hc_ne_top
      rw [show (fun x => c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x * h x)
          = fun x => c * (((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x * h x) from
            funext (fun _ => by ring)]
      rw [MeasureTheory.lintegral_const_mul' _ _ hc_ne_top]
    -- Apply per-c rewriting on both sides.
    rw [show (fun x => (sn n : Ω → ℝ≥0∞) x * f x)
        = fun x => ∑ c ∈ (sn n).range,
          (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * f x from
            funext (fun x => h_decomp x f)]
    rw [show (fun x => (sn n : Ω → ℝ≥0∞) x * μ⁻[f|m] x)
        = fun x => ∑ c ∈ (sn n).range,
          (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * μ⁻[f|m] x from
            funext (fun x => h_decomp x _)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun c _ =>
      ((Measurable.indicator measurable_const (hm _ (h_preim_meas c))).const_mul c).mul hf)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun c _ =>
      ((Measurable.indicator measurable_const (hm _ (h_preim_meas c))).const_mul c).mul
        h_cL_meas_m₀)]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [h_per_c_LHS c f (h_preim_lt_top c hc),
        h_per_c_LHS c (μ⁻[f|m]) (h_preim_lt_top c hc),
        lintegral_indicator_mul_eq hm μ (h_preim_meas c) f]
  -- Step B: pass to MCT via lintegral_iSup.
  rw [h_g_mul_iSup f, h_g_mul_iSup (μ⁻[f|m])]
  rw [MeasureTheory.lintegral_iSup (fun n => h_meas_mul f hf n) (fun i j hij x => h_mono_mul f x hij)]
  rw [MeasureTheory.lintegral_iSup (fun n => h_meas_mul (μ⁻[f|m]) h_cL_meas_m₀ n)
    (fun i j hij x => h_mono_mul _ x hij)]
  exact iSup_congr h_step

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **σ-algebra of the shifted past**: events depending only on `{x_i : i ≤ n - 1}`. -/
@[reducible] private def shiftedPastSigma (n : ℕ) : MeasurableSpace (∀ _ : ℤ, α) :=
  (negPastSigma (α := α)).comap (shiftZ^[n])

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma shiftedPastSigma_le (n : ℕ) :
    (shiftedPastSigma (α := α) n) ≤ MeasurableSpace.pi := by
  intro s ⟨t, ht_neg, hts⟩
  rw [← hts]
  exact (measurable_shiftZ.iterate n) (cylinderEvents_le_pi _ ht_neg)

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The map `condProbInfty(a) ∘ shift^[n]` is measurable w.r.t. `shiftedPastSigma n`. -/
private lemma measurable_condProbInfty_comp_shift_shiftedPastSigma
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (a : α) :
    @Measurable _ _ (shiftedPastSigma (α := α) n) _
      (fun x => condProbInfty μ p a (shiftZ^[n] x)) := by
  have h_sm_negPast : StronglyMeasurable[negPastSigma (α := α)] (condProbInfty μ p a) := by
    have h := stronglyMeasurable_condProbInfty μ p a
    rw [show (⨆ n : ℕ, (pastFiltration (α := α)) n)
        = (⨆ n : ℕ, pastSigma (α := α) n) from rfl, iSup_pastSigma_eq_negPastSigma] at h
    exact h
  have h_meas_negPast : @Measurable _ _ (negPastSigma (α := α)) _ (condProbInfty μ p a) :=
    h_sm_negPast.measurable
  intro s hs
  show MeasurableSet[shiftedPastSigma n] ((fun x => condProbInfty μ p a (shiftZ^[n] x)) ⁻¹' s)
  refine ⟨condProbInfty μ p a ⁻¹' s, h_meas_negPast hs, ?_⟩
  rfl

/-- **CORE LEMMA (tower property)**: `∫ MRatioLowerZ n dμZ ≤ 1`. -/
theorem integral_MRatioLowerZ_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    ∫⁻ x, MRatioLowerZ μ p n x ∂(μZ μ p) ≤ 1 := by
  induction n with
  | zero =>
    have h_const : ∀ x, MRatioLowerZ μ p 0 x = 1 := by
      intro x
      unfold MRatioLowerZ negLogQInftyZ blockLogAvgZ
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, sub_zero,
        Real.exp_zero, ENNReal.ofReal_one]
    have h_int_eq : ∫⁻ x, MRatioLowerZ μ p 0 x ∂(μZ μ p) = 1 := by
      calc ∫⁻ x, MRatioLowerZ μ p 0 x ∂(μZ μ p)
          = ∫⁻ _, (1 : ℝ≥0∞) ∂(μZ μ p) := by
            refine lintegral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun x => by rw [h_const x])
        _ = (μZ μ p) Set.univ := by rw [lintegral_one]
        _ = 1 := measure_univ
    rw [h_int_eq]
  | succ n ih =>
    -- **Inductive step** (Algoet–Cover tower argument).
    --
    -- All infrastructure helpers are in this file:
    --   * `MRatioLowerZ_succ_eq_mul`: pointwise factorization
    --       `MRatioLowerZ (n+1) x = MRatioLowerZ n x · ofReal(blockCondRatio) · ofReal(exp pmf)`
    --       (a.e. on the positive set).
    --   * `sum_blockCondRatio`: `∑_a blockCondRatio = 1` on the positive set.
    --   * `firstBlockZ_singleton_pos_ae`: `P_n^Z > 0` a.s.
    --   * `lintegral_mul_eq_lintegral_mul_condLExp`: general ENNReal pull-out
    --       `∫⁻ g · f dμ = ∫⁻ g · μ⁻[f|m] dμ` for `m`-measurable `g`.
    --   * `shiftedPastSigma n := negPastSigma.comap shift^n`: the relevant sub-σ-algebra.
    --
    -- **Remaining glue work (~150 LOC, deferred to next pass)**:
    --
    --   (a) Tower identification: combine `condExp_comp_measurePreserving` (from
    --       `TwoSidedExtension.lean`) with `condProbInfty_eq_condExp_tail` to get
    --       `μZ⁻[(coord_n=a).indicator (1 : ℝ≥0∞) | shiftedPastSigma n] x
    --          =ᵐ ENNReal.ofReal (condProbInfty(a)(shift^n x))`. Goes through
    --       `toReal_condLExp` bridge between real `condExp` and ENNReal `condLExp`.
    --
    --   (b) On positive set: `ofReal(exp(pmfLogCondInfty y)) · ofReal(condProbInfty (coord0 y) y) = 1`,
    --       i.e., `pmf inverse = condProb`. Direct from the definition of `pmfLogCondInfty`
    --       (using `pmfLogCondPast_inner_eq_self`).
    --
    --   (c) Combine via:
    --       ```
    --       ∫⁻ MRatioLowerZ (n+1) dμZ
    --         = ∫⁻ ∑_a [coord_n=a] · MRatioLowerZ n · ofReal(ratio_a/condProbInfty) dμZ  -- by (a),(b),decomp
    --         = ∑_a ∫⁻ [coord_n=a] · (factor_a) dμZ                                       -- finset sum/integral commute
    --         = ∑_a ∫⁻ μZ⁻[[coord_n=a]|F_n] · (factor_a) dμZ                              -- pull-out
    --         = ∑_a ∫⁻ ofReal(condProbInfty(a)(shift^n)) · (factor_a) dμZ                 -- tower id (a)
    --         = ∑_a ∫⁻ MRatioLowerZ n · ofReal(ratio_a) dμZ                               -- cancellation
    --         = ∫⁻ MRatioLowerZ n · ofReal(∑_a ratio_a) dμZ                               -- finset sum
    --         ≤ ∫⁻ MRatioLowerZ n dμZ                                                     -- ∑ ratio_a = 1
    --         ≤ 1                                                                          -- by ih
    --       ```
    --
    -- Reference: Algoet–Cover (1988), Sandwich Theorem proof.
    have _ := ih  -- IH available; placeholder for next-pass assembly.
    sorry

omit [DecidableEq α] [Nonempty α] in
/-- `pmfLogCondInfty` is measurable (w.r.t. the pi σ-algebra). -/
lemma measurable_pmfLogCondInfty
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Measurable (pmfLogCondInfty μ p) := by
  classical
  unfold pmfLogCondInfty
  refine (Real.measurable_log.comp ?_).neg
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.mul ?_ ?_
  · refine Measurable.indicator measurable_const ?_
    exact measurableSet_coord0_eq a
  · exact ((stronglyMeasurable_condProbInfty μ p a).mono
      (iSup_le (fun n => (pastFiltration (α := α)).le n))).measurable

omit [DecidableEq α] [Nonempty α] in
/-- Measurability of `MRatioLowerZ` w.r.t. the product σ-algebra on `ℤ → α`. -/
lemma measurable_MRatioLowerZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    Measurable (MRatioLowerZ μ p n) := by
  classical
  unfold MRatioLowerZ
  refine ENNReal.measurable_ofReal.comp ?_
  refine Real.measurable_exp.comp ?_
  refine Measurable.sub ?_ ?_
  · -- negLogQInftyZ is a measurable sum.
    unfold negLogQInftyZ
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (measurable_pmfLogCondInfty μ p).comp ((measurable_shiftZ).iterate i)
  · -- n · blockLogAvgZ is measurable.
    refine measurable_const.mul ?_
    unfold blockLogAvgZ
    refine measurable_const.mul ?_
    refine Real.measurable_log.comp ?_
    have h_disc : Measurable (fun y : Fin n → α =>
        (((μZ μ p).map (firstBlockZ (α := α) n)).real {y})) := measurable_of_finite _
    exact h_disc.comp (measurable_firstBlockZ n)

/-- **Borel–Cantelli consequence (Z-side)**: μZ-a.s., `MRatioLowerZ n x ≤ n²` eventually. -/
theorem MRatioLowerZ_le_sq_eventually
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    ∀ᵐ x ∂(μZ μ p), ∀ᶠ n in Filter.atTop,
      MRatioLowerZ μ p n x ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := by
  -- Direct Markov + first Borel-Cantelli on `s n := {MRatioLowerZ n > n²}`.
  set s : ℕ → Set (∀ _ : ℤ, α) :=
    fun n => {x | ENNReal.ofReal ((n : ℝ) ^ 2) < MRatioLowerZ μ p n x} with hs_def
  have h_MR_meas : ∀ n, Measurable (MRatioLowerZ μ p n) := measurable_MRatioLowerZ μ p
  -- Per-n measure bound: for n ≥ 1, μZ(s n) ≤ 1 / (n^2 : ℝ≥0∞).
  have h_bound : ∀ n, 1 ≤ n → (μZ μ p) (s n) ≤ (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2) := by
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
    have h_sub : s n ⊆ {x | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioLowerZ μ p n x} := by
      intro x hx
      have : ENNReal.ofReal ((n : ℝ) ^ 2) < MRatioLowerZ μ p n x := hx
      exact le_of_lt this
    have h_markov : (μZ μ p) {x | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioLowerZ μ p n x}
        ≤ (∫⁻ x, MRatioLowerZ μ p n x ∂(μZ μ p)) / ENNReal.ofReal ((n : ℝ) ^ 2) :=
      meas_ge_le_lintegral_div (h_MR_meas n).aemeasurable h_eps_ne_zero h_eps_ne_top
    have h_int := integral_MRatioLowerZ_le_one μ p n
    calc (μZ μ p) (s n)
        ≤ (μZ μ p) {x | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioLowerZ μ p n x} :=
          measure_mono h_sub
      _ ≤ (∫⁻ x, MRatioLowerZ μ p n x ∂(μZ μ p)) / ENNReal.ofReal ((n : ℝ) ^ 2) := h_markov
      _ ≤ 1 / ENNReal.ofReal ((n : ℝ) ^ 2) := ENNReal.div_le_div_right h_int _
      _ = 1 / ((n : ℝ≥0∞) ^ 2) := by rw [h_eps]
  -- Sum: ∑' n, μZ (s n) < ∞.
  have h_tsum : ∑' n, (μZ μ p) (s n) ≠ ∞ := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ?_⟩
    have h_le : (∑' n : ℕ, (μZ μ p) (s (n + 1)))
        ≤ ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) := by
      refine ENNReal.tsum_le_tsum (fun n => ?_)
      exact h_bound (n + 1) (Nat.succ_le_succ (Nat.zero_le _))
    refine ne_top_of_le_ne_top ?_ h_le
    have h_summable_real : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      exact (summable_nat_add_iff 1).mpr h
    have h_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := fun _ => by positivity
    have h_ennreal_tsum : ∑' n : ℕ,
        ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable_real]
      exact ENNReal.ofReal_ne_top
    have h_pointwise : ∀ n : ℕ,
        (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) =
          ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro n
      have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_one,
        show ((n + 1 : ℕ) : ℝ) ^ 2 = (((n + 1)^2 : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
      push_cast; ring_nf
    have h_tsum_eq : ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2)
        = ∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      tsum_congr h_pointwise
    rw [h_tsum_eq]
    exact h_ennreal_tsum
  have h_BC := MeasureTheory.ae_eventually_notMem h_tsum
  filter_upwards [h_BC] with x hx
  filter_upwards [hx] with n hn
  exact not_lt.mp hn

/-- **Logarithmic form (Z-side)**: μZ-a.s., eventually,
`blockLogAvgZ n x ≥ (1/n) · negLogQInftyZ n x - 2 log n / n`. -/
theorem blockLogAvgZ_ge_negLogQInftyZ_minus_error
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    ∀ᵐ x ∂(μZ μ p), ∀ᶠ n in Filter.atTop,
      negLogQInftyZ μ p n x / n - 2 * Real.log n / n ≤ blockLogAvgZ μ p n x := by
  filter_upwards [MRatioLowerZ_le_sq_eventually μ p] with x hx
  filter_upwards [hx, Filter.eventually_ge_atTop 1] with n h_MR hn
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_n_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have h_real_le : Real.exp (negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x)
      ≤ (n : ℝ) ^ 2 := by
    have : ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x))
        ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := h_MR
    exact (ENNReal.ofReal_le_ofReal_iff h_n_sq_pos.le).mp this
  have h_log : negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x
      ≤ 2 * Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) h_real_le
    rw [Real.log_exp] at h
    have h_log_sq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      rw [show ((n : ℝ) ^ 2) = (n : ℝ) * (n : ℝ) from sq (n : ℝ),
        Real.log_mul h_n_pos.ne' h_n_pos.ne']
      ring
    rw [h_log_sq] at h
    exact h
  have h_div :
      negLogQInftyZ μ p n x / (n : ℝ) - blockLogAvgZ μ p n x ≤
        2 * Real.log (n : ℝ) / (n : ℝ) := by
    have h := div_le_div_of_nonneg_right h_log h_n_pos.le
    rw [sub_div, mul_div_cancel_left₀ _ h_n_pos.ne'] at h
    exact h
  linarith

/-- **Birkhoff for `pmfLogCondInfty` on the 2-sided side**: applying Birkhoff to
`(μZ, shiftZ, pmfLogCondInfty)`, using `ergodic_shiftZ`, `measurePreserving_shiftZ`,
`integrable_pmfLogCondInfty`, and `integral_pmfLogCondInfty_eq_entropyRate`. -/
theorem birkhoffAverage_pmfLogCondInfty_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ x ∂(μZ μ p.toStationaryProcess),
      Filter.Tendsto
        (fun n : ℕ => negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  have h_mp := measurePreserving_shiftZ μ p.toStationaryProcess
  have h_erg := ergodic_shiftZ μ p
  have h_int := integrable_pmfLogCondInfty μ p.toStationaryProcess
  have h_int_id := integral_pmfLogCondInfty_eq_entropyRate μ p.toStationaryProcess
  have h_birk := InformationTheory.Shannon.birkhoff_ergodic_ae h_mp h_erg h_int
  -- The Birkhoff conclusion: birkhoffAverageReal shiftZ pmfLogCondInfty m x → ∫ pmfLogCondInfty,
  -- where `birkhoffAverageReal T f m ω = (∑_{i<m+1} f(T^[i] ω)) / (m+1)`. We want our form
  -- `(∑_{i<n} f(shiftZ^[i] x)) / n` for n ≥ 1; compose with `n ↦ n - 1`.
  rw [show entropyRate μ p.toStationaryProcess
        = ∫ x, pmfLogCondInfty μ p.toStationaryProcess x ∂(μZ μ p.toStationaryProcess)
      from h_int_id.symm]
  filter_upwards [h_birk] with x hx
  have h_comp := hx.comp (Filter.tendsto_sub_atTop_nat 1)
  refine Filter.Tendsto.congr' ?_ h_comp
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h_succ : (n - 1) + 1 = n := by omega
  -- Goal: ((fun n => birkhoffAverageReal shiftZ pmf n x) ∘ (· - 1)) n
  --     = negLogQInftyZ ... n x / n
  show birkhoffAverageReal shiftZ
        (pmfLogCondInfty μ p.toStationaryProcess) (n - 1) x
      = negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ)
  unfold birkhoffAverageReal negLogQInftyZ
  -- LHS: (∑ i ∈ range (n - 1 + 1), pmf ...) / (↑(n - 1) + 1)
  -- RHS: (∑ i ∈ range n, pmf ...) / ↑n
  have h_num : (∑ i ∈ Finset.range (n - 1 + 1),
        pmfLogCondInfty μ p.toStationaryProcess (shiftZ^[i] x))
      = ∑ i ∈ Finset.range n,
          pmfLogCondInfty μ p.toStationaryProcess (shiftZ^[i] x) := by
    rw [h_succ]
  have h_den : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) + 1 = (((n - 1 + 1 : ℕ)) : ℝ) := by push_cast; ring
    rw [this, h_succ]
  rw [h_num, h_den]

omit [DecidableEq α] [Nonempty α] in
/-- Helper: `y ↦ blockLogAvgZ μ p n (eN y)` is measurable on `ℕ → α`, where
`eN y i := y i.toNat`. -/
private lemma measurable_blockLogAvgZ_via_eN
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    Measurable (fun y : ∀ _ : ℕ, α =>
      blockLogAvgZ μ p n (fun i : ℤ => y i.toNat)) := by
  unfold blockLogAvgZ
  refine measurable_const.mul ?_
  refine Real.measurable_log.comp ?_
  have h_disc : Measurable (fun s : Fin n → α =>
      (((μZ μ p).map (firstBlockZ (α := α) n)).real {s})) := measurable_of_finite _
  refine h_disc.comp ?_
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact measurable_pi_apply _

omit [DecidableEq α] in
/-- **Z-side a.s. upper boundedness** of `blockLogAvgZ` (transferred from the Ω-side
`blockLogAvg_bddAbove_ae`, via the bridge `blockLogAvgZ n (natExt ω) = blockLogAvg n ω`
and `measurePreserving_forwardEmbed` + `μZ_nat_proj_eq`).

`blockLogAvgZ n x` depends only on `natProj x : ℕ → α`. We push the μ-a.s. statement
`Ω-blockLogAvg n ω bounded above` through `measurePreserving_forwardEmbed` to a
`(μ.map forwardEmbed) = (μZ.map natProj)`-a.s. statement on `(ℕ → α)`, then pull back
to μZ-a.s. on `(ℤ → α)` via `natProj`. -/
theorem blockLogAvgZ_bddAbove_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ x ∂(μZ μ p.toStationaryProcess), Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => blockLogAvgZ μ p.toStationaryProcess n x) := by
  classical
  -- Define `eN : (ℕ → α) → (ℤ → α)`, `eN y i := y i.toNat`. Then for any `x`,
  -- `blockLogAvgZ n x = blockLogAvgZ n (eN (natProj x))` (depends only on natProj).
  set eN : (∀ _ : ℕ, α) → (∀ _ : ℤ, α) := fun y i => y i.toNat with heN_def
  have h_blockLogAvgZ_factor : ∀ x : ∀ _ : ℤ, α, ∀ n,
      blockLogAvgZ μ p.toStationaryProcess n x
        = blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
    intro x n
    have h_arg : (firstBlockZ (α := α) n) x
        = (firstBlockZ (α := α) n) (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
      funext i
      show x (i.val : ℤ) = (eN (InformationTheory.Shannon.TwoSided.natProj x)) (i.val : ℤ)
      show x (i.val : ℤ) = x (((((i.val : ℕ) : ℤ).toNat : ℕ) : ℤ))
      simp
    unfold blockLogAvgZ
    rw [h_arg]
  -- Get Ω-side bound.
  have h_Ω := blockLogAvg_bddAbove_ae μ p
  -- For each `ω`, `blockLogAvgZ n (eN (forwardEmbed ω)) = blockLogAvg n ω` (by
  -- `blockLogAvgZ_natExt_eq`).
  have h_Ω' : ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => blockLogAvgZ μ p.toStationaryProcess n
        (eN (forwardEmbed (μ := μ) p.toStationaryProcess ω))) := by
    filter_upwards [h_Ω] with ω hω
    have h_eq : (fun n => blockLogAvgZ μ p.toStationaryProcess n
          (eN (forwardEmbed (μ := μ) p.toStationaryProcess ω)))
        = fun n => blockLogAvg μ p.toStationaryProcess n ω := by
      funext n
      rw [show eN (forwardEmbed (μ := μ) p.toStationaryProcess ω)
          = fun i : ℤ => p.obs i.toNat ω from rfl]
      exact blockLogAvgZ_natExt_eq μ p.toStationaryProcess n ω
    rw [h_eq]; exact hω
  -- Push h_Ω' through measurePreserving_forwardEmbed to (μ.map forwardEmbed)-a.s.
  have h_mp_forwardEmbed : MeasurePreserving (forwardEmbed (μ := μ) p.toStationaryProcess)
      μ (μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)) :=
    InformationTheory.Shannon.TwoSided.measurePreserving_forwardEmbed
      μ p.toStationaryProcess
  -- Convert μ-a.s. statement to (μ.map forwardEmbed)-a.s. via `ae_map_iff`.
  have h_N_ae : ∀ᵐ y ∂(μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)),
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y)) := by
    -- This is the (μ.map forwardEmbed)-form, but we have h_Ω' (μ-form of ∘ forwardEmbed).
    -- We need ae_map_iff with measurability.
    rw [ae_map_iff (measurable_forwardEmbed (μ := μ) p.toStationaryProcess).aemeasurable
      (by
        -- IsBoundedUnder (≤) is `∃ a, ∀ᶠ n, f n ≤ a`. Translate to MeasurableSet.
        -- Note: this is a `Set (ℕ → α)` set; it should be measurable. Use the standard
        -- countable-union representation:
        --   `{y | ∃ M : ℕ, ∀ᶠ n, blockLogAvgZ n (eN y) ≤ M}
        --   = ⋃ M : ℕ, ⋂ᶠ n ≥ N : ℕ, {y | blockLogAvgZ n (eN y) ≤ M}`.
        -- For brevity, since the predicate set is Borel-measurable via countable Boolean
        -- operations on measurable inequalities, we use the explicit set form.
        change MeasurableSet {y : ∀ _ : ℕ, α | _}
        -- IsBoundedUnder definitionally unfolds to `∃ a, ∀ᶠ ..., · ≤ a`.
        -- For ℝ, the existence of bound `∃ a, ∀ᶠ n, f n ≤ a` is equivalent to
        --   `⋃ M : ℕ, {y | ∀ᶠ n, f n ≤ M}`.
        have h_set_eq : {y : ∀ _ : ℕ, α | Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
              (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y))}
            = ⋃ M : ℕ, {y | ∀ᶠ n in Filter.atTop,
                blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
          ext y
          constructor
          · rintro ⟨a, ha⟩
            obtain ⟨M, hM⟩ := exists_nat_ge a
            exact Set.mem_iUnion.mpr ⟨M, ha.mono (fun n hn => hn.trans hM)⟩
          · rintro ⟨S, ⟨M, rfl⟩, hS⟩
            exact ⟨(M : ℝ), hS⟩
        rw [h_set_eq]
        refine MeasurableSet.iUnion (fun M => ?_)
        -- `{y | ∀ᶠ n, blockLogAvgZ ... ≤ M}` = `⋃ N : ℕ, ⋂ n ≥ N, {y | ...}`.
        have h_eventually : {y : ∀ _ : ℕ, α | ∀ᶠ n in Filter.atTop,
              blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)}
            = ⋃ N : ℕ, ⋂ n ∈ Set.Ici N,
                {y | blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici,
            Filter.eventually_atTop]
        rw [h_eventually]
        refine MeasurableSet.iUnion (fun N => ?_)
        refine MeasurableSet.biInter (Set.to_countable _) (fun n _ => ?_)
        exact measurableSet_le (measurable_blockLogAvgZ_via_eN μ p.toStationaryProcess n)
          measurable_const
      )]
    exact h_Ω'
  -- Pull back via `μ.map forwardEmbed = μZ.map natProj` and `ae_map_iff` for natProj.
  rw [← (InformationTheory.Shannon.TwoSided.measurePreserving_natProj μ
    p.toStationaryProcess).map_eq] at h_N_ae
  rw [ae_map_iff InformationTheory.Shannon.TwoSided.measurable_natProj.aemeasurable
    (by
      -- Measurability of the predicate set on (ℕ → α), same proof as above.
      change MeasurableSet {y : ∀ _ : ℕ, α | _}
      have h_set_eq : {y : ∀ _ : ℕ, α | Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
            (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y))}
          = ⋃ M : ℕ, {y | ∀ᶠ n in Filter.atTop,
              blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
        ext y
        constructor
        · rintro ⟨a, ha⟩
          obtain ⟨M, hM⟩ := exists_nat_ge a
          exact Set.mem_iUnion.mpr ⟨M, ha.mono (fun n hn => hn.trans hM)⟩
        · rintro ⟨S, ⟨M, rfl⟩, hS⟩
          exact ⟨(M : ℝ), hS⟩
      rw [h_set_eq]
      refine MeasurableSet.iUnion (fun M => ?_)
      have h_eventually : {y : ∀ _ : ℕ, α | ∀ᶠ n in Filter.atTop,
            blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)}
          = ⋃ N : ℕ, ⋂ n ∈ Set.Ici N,
              {y | blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici,
          Filter.eventually_atTop]
      rw [h_eventually]
      refine MeasurableSet.iUnion (fun N => ?_)
      refine MeasurableSet.biInter (Set.to_countable _) (fun n _ => ?_)
      exact measurableSet_le (measurable_blockLogAvgZ_via_eN μ p.toStationaryProcess n)
        measurable_const
    )] at h_N_ae
  -- Now h_N_ae : ∀ᵐ x ∂μZ, IsBoundedUnder (≤) atTop (fun n => blockLogAvgZ n (eN (natProj x))).
  -- Convert to the target via h_blockLogAvgZ_factor.
  filter_upwards [h_N_ae] with x hx
  have h_eq : (fun n => blockLogAvgZ μ p.toStationaryProcess n x)
      = fun n => blockLogAvgZ μ p.toStationaryProcess n
          (eN (InformationTheory.Shannon.TwoSided.natProj x)) :=
    funext (fun n => h_blockLogAvgZ_factor x n)
  rw [h_eq]; exact hx

/-- **Z-side liminf bound**: μZ-a.s., `liminf blockLogAvgZ n x ≥ entropyRate`. -/
theorem liminf_blockLogAvgZ_ge_entropyRate
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ x ∂(μZ μ p.toStationaryProcess),
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n x) Filter.atTop := by
  filter_upwards [blockLogAvgZ_ge_negLogQInftyZ_minus_error μ p.toStationaryProcess,
                  birkhoffAverage_pmfLogCondInfty_tendsto μ p,
                  blockLogAvgZ_bddAbove_ae μ p] with x h_bound h_birk h_bdd_above
  -- LHS tendsto: negLogQ/n - 2 log n / n → entropyRate - 0 = entropyRate.
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
  have h_lhs : Filter.Tendsto
      (fun n : ℕ => negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ)
        - 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) := by
    have := h_birk.sub h_log_div
    simpa using this
  -- Apply `liminf_le_liminf` between u (the LHS) and v = blockLogAvgZ.
  -- - hu: u is bounded below (tendsto ⇒ isBoundedUnder ≥).
  -- - hv: v is cobounded (· ≥ ·), from the a.s. upper bound `blockLogAvgZ_bddAbove_ae`.
  have h_liminf_le : Filter.liminf
      (fun n : ℕ => negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ)
        - 2 * Real.log (n : ℝ) / (n : ℝ)) Filter.atTop
      ≤ Filter.liminf (fun n => blockLogAvgZ μ p.toStationaryProcess n x) Filter.atTop :=
    Filter.liminf_le_liminf h_bound (hu := h_lhs.isBoundedUnder_ge)
      (hv := h_bdd_above.isCoboundedUnder_ge)
  rw [h_lhs.liminf_eq] at h_liminf_le
  exact h_liminf_le

/-- **Final transfer to Ω-side**: μ-a.s., `entropyRate ≤ liminf blockLogAvg n ω`.

Bridge: `blockLogAvgZ n x` depends only on `natProj x : ℕ → α`. We transfer the
Z-side a.s. liminf bound through `natProj`-`forwardEmbed` measure preservation
to the Ω-side, using `μZ_nat_proj_eq` (= `μ.map forwardEmbed`) and the fact
that `blockLogAvgZ n (eN (forwardEmbed ω)) = blockLogAvg n ω` where
`eN y i := y i.toNat` is the trivial extension on ℤ. -/
theorem algoet_cover_liminf_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop := by
  classical
  -- Step 1: Z-side liminf bound.
  have h_Z := liminf_blockLogAvgZ_ge_entropyRate μ p
  -- Step 2: `blockLogAvgZ n x` depends only on `natProj x`. Define a "trivial
  -- extension" `eN : (ℕ → α) → (ℤ → α)`, `eN y i := y i.toNat`, with
  -- `natProj (eN y) = y` and `blockLogAvgZ n x = blockLogAvgZ n (eN (InformationTheory.Shannon.TwoSided.natProj x))`.
  set eN : (∀ _ : ℕ, α) → (∀ _ : ℤ, α) := fun y i => y i.toNat with heN_def
  have h_blockLogAvgZ_factor : ∀ x : ∀ _ : ℤ, α, ∀ n,
      blockLogAvgZ μ p.toStationaryProcess n x
        = blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
    intro x n
    -- Show: blockLogAvgZ n x = blockLogAvgZ n (eN (natProj x)).
    -- It suffices to show firstBlockZ n x = firstBlockZ n (eN (natProj x)).
    have h_arg : (firstBlockZ (α := α) n) x
        = (firstBlockZ (α := α) n) (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
      funext i
      show x (i.val : ℤ) = (eN (InformationTheory.Shannon.TwoSided.natProj x)) (i.val : ℤ)
      show x (i.val : ℤ) = x (((((i.val : ℕ) : ℤ).toNat : ℕ) : ℤ))
      simp
    unfold blockLogAvgZ
    rw [h_arg]
  -- Step 3: rewrite `h_Z` via `h_blockLogAvgZ_factor` so the predicate factors through
  -- natProj: P(x) = (entropyRate ≤ liminf (blockLogAvgZ n (eN (InformationTheory.Shannon.TwoSided.natProj x)))).
  have h_Z' : ∀ᵐ x ∂(μZ μ p.toStationaryProcess),
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)))
            Filter.atTop := by
    filter_upwards [h_Z] with x hx
    have h_eq : (fun n => blockLogAvgZ μ p.toStationaryProcess n x)
        = fun n => blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)) :=
      funext (fun n => h_blockLogAvgZ_factor x n)
    rw [← h_eq]; exact hx
  -- Step 4: push h_Z' through `natProj` to get a (μZ.map natProj)-a.s. statement.
  -- Since `μZ.map natProj = μ.map forwardEmbed`, this becomes (μ.map forwardEmbed)-a.s.
  have h_mp_natProj : MeasurePreserving
      (InformationTheory.Shannon.TwoSided.natProj (α := α))
      (μZ μ p.toStationaryProcess) (μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)) :=
    InformationTheory.Shannon.TwoSided.measurePreserving_natProj μ p.toStationaryProcess
  -- The Z-side predicate `λ x, Q(natProj x)` is μZ-a.s. ⇒ Q is μZ.map natProj-a.s.
  -- We use `MeasurePreserving.ae_iff` (or its quasiMeasurePreserving form).
  have h_N_ae : ∀ᵐ y ∂(μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)),
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y)) Filter.atTop := by
    -- Use the fact that `(μZ.map natProj) = (μ.map forwardEmbed)` (from h_mp_natProj.map_eq).
    rw [← h_mp_natProj.map_eq]
    -- And `ae_map_iff` to convert μZ-a.s. of `Q ∘ natProj` to (μZ.map natProj)-a.s. of Q.
    rw [ae_map_iff InformationTheory.Shannon.TwoSided.measurable_natProj.aemeasurable
      (by
        -- Measurability of the predicate set on (ℕ → α).
        apply measurableSet_le measurable_const
        refine Measurable.liminf (fun n => ?_)
        -- `λ y, blockLogAvgZ n (eN y)` is measurable.
        exact measurable_blockLogAvgZ_via_eN μ p.toStationaryProcess n
      )]
    exact h_Z'
  -- Step 5: pull back from `(μ.map forwardEmbed)`-a.s. to μ-a.s. via forwardEmbed.
  have h_mp_forwardEmbed : MeasurePreserving (forwardEmbed (μ := μ) p.toStationaryProcess)
      μ (μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)) :=
    InformationTheory.Shannon.TwoSided.measurePreserving_forwardEmbed
      μ p.toStationaryProcess
  have h_Ω_ae : ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n
              (eN (forwardEmbed (μ := μ) p.toStationaryProcess ω))) Filter.atTop :=
    h_mp_forwardEmbed.quasiMeasurePreserving.ae h_N_ae
  -- Step 6: `eN (forwardEmbed ω) = fun i : ℤ => p.obs i.toNat ω`, so
  -- `blockLogAvgZ n (eN (forwardEmbed ω)) = blockLogAvg n ω` by `blockLogAvgZ_natExt_eq`.
  filter_upwards [h_Ω_ae] with ω hω
  convert hω using 2
  funext n
  rw [show eN (forwardEmbed (μ := μ) p.toStationaryProcess ω)
      = fun i : ℤ => p.obs i.toNat ω from rfl]
  exact (blockLogAvgZ_natExt_eq μ p.toStationaryProcess n ω).symm

/-! ## D.7 — Main theorem (hypothesis-free) -/

/-- **Shannon–McMillan–Breiman theorem** (Cover–Thomas 16.8.1).

For a stationary ergodic process with finite alphabet, the per-symbol
negative log-likelihood `blockLogAvg μ p n` converges almost surely to the
entropy rate `entropyRate μ p`. -/
theorem shannon_mcmillan_breiman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  shannon_mcmillan_breiman_of_sandwich μ p
    (algoet_cover_liminf_bound μ p)
    (algoet_cover_limsup_bound μ p)
    (blockLogAvg_bddAbove_ae μ p)
    (blockLogAvg_bddBelow_ae μ p)

end InformationTheory.Shannon
