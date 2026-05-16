import Common2026.Shannon.Stationary
import Common2026.Shannon.EntropyRate
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# SMB chain rule decomposition (Phase C.1 + C.2)

For a stationary process `p : StationaryProcess μ α` over a finite alphabet,
this file establishes the Cover–Thomas 16.8 **chain rule for log-likelihood**:

  `-log P_n({block_n ω}) = ∑_{i<n} -log P(obs i | block_i)(block_i ω){obs i ω}`

a.s. over `ω`. The right-hand side is named `pmfLogCond μ p i ω`. The result
is the algebraic skeleton that Phase C.3 (Levy convergence) and Phase D
(Birkhoff + Cesàro sandwich) use to discharge the four hypotheses of
`shannon_mcmillan_breiman_of_sandwich`.

## Main definitions

* `pmfLogCond μ p i ω` — per-step conditional negative log-likelihood
  `-log (condDistrib (obs i) (blockRV i) μ (block_i ω)).real {obs i ω}`.

## Main results

* `block_measure_succ_singleton_eq` — multiplicative ENNReal chain rule at
  singletons: `P_{n+1}({block_{n+1} ω}) = P_n({block_n ω}) · c_n(...){obs n ω}`.
* `block_singleton_pos_ae_at` — a.s. positivity of `P_n({block_n ω})` for each `n`.
* `log_block_eq_sum_pmfLogCond` — a.s. log identity (chain rule):
  `-log P_n({block_n ω}) = ∑_{i<n} pmfLogCond μ p i ω`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Per-step conditional log-likelihood -/

/-- Per-step conditional negative log-likelihood:
`pmfLogCond μ p i ω = -log (condDistrib (obs i) (blockRV i) μ (block_i ω)).real {obs i ω}`.

For `i = 0`, `blockRV 0` is the unique map to `Fin 0 → α`, so the conditional
kernel reduces to the marginal `μ.map (p.X)`. -/
noncomputable def pmfLogCond
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (i : ℕ) : Ω → ℝ :=
  fun ω => -Real.log
    ((condDistrib (p.obs i) (p.blockRV i) μ (p.blockRV i ω)).real {p.obs i ω})

omit [DecidableEq α] in
lemma measurable_pmfLogCond
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (i : ℕ) :
    Measurable (pmfLogCond μ p i) := by
  unfold pmfLogCond
  -- `(blockRV i ω, obs i ω)` is measurable; postcomposed with the discrete
  -- function `(b, a) ↦ (condDistrib (obs i) (blockRV i) μ b).real {a}`.
  have h_meas_pair : Measurable (fun ω => (p.blockRV i ω, p.obs i ω)) :=
    (p.measurable_blockRV i).prodMk (p.measurable_obs i)
  have h_disc : Measurable (fun (q : (Fin i → α) × α) =>
      -Real.log ((condDistrib (p.obs i) (p.blockRV i) μ q.1).real {q.2})) :=
    measurable_of_finite _
  exact h_disc.comp h_meas_pair

/-! ## Multiplicative chain rule at singletons (ENNReal level) -/

omit [DecidableEq α] in
/-- **Chain rule for the block measure** (ENNReal singleton form).

Pushforward of `μ` by `blockRV (n+1)` factors at any singleton via the
conditional kernel `condDistrib (obs n) (blockRV n) μ`:
`P_{n+1}({block_{n+1} ω}) = P_n({block_n ω}) · c_n(block_n ω){obs n ω}`. -/
theorem block_measure_succ_singleton_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    (μ.map (p.blockRV (n + 1))) {p.blockRV (n + 1) ω}
      = (μ.map (p.blockRV n)) {p.blockRV n ω}
        * (condDistrib (p.obs n) (p.blockRV n) μ (p.blockRV n ω)) {p.obs n ω} := by
  classical
  have h_block_meas : Measurable (p.blockRV n) := p.measurable_blockRV n
  have h_obs_meas : Measurable (p.obs n) := p.measurable_obs n
  have h_block_succ_meas : Measurable (p.blockRV (n + 1)) := p.measurable_blockRV (n + 1)
  have h_pair_meas : Measurable (fun ω => (p.blockRV n ω, p.obs n ω)) :=
    h_block_meas.prodMk h_obs_meas
  -- Equiv `e : (Fin (n+1) → α) ≃ᵐ α × (Fin n → α)` from `piFinSuccAbove (Fin.last n)`.
  let e : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)
  have h_e_eq : ∀ ω, e (p.blockRV (n + 1) ω) = (p.obs n ω, p.blockRV n ω) := by
    intro ω
    apply Prod.ext
    · show p.blockRV (n + 1) ω (Fin.last n) = p.obs n ω
      show p.obs (Fin.last n) ω = p.obs n ω
      rfl
    · funext j
      show p.blockRV (n + 1) ω ((Fin.last n).succAbove j) = p.blockRV n ω j
      show p.obs ((Fin.last n).succAbove j) ω = p.obs j ω
      rw [Fin.succAbove_last_apply j]
      rfl
  -- Compose with `prodComm` to land in `(Fin n → α) × α`.
  let e' : (Fin (n + 1) → α) ≃ᵐ (Fin n → α) × α := e.trans MeasurableEquiv.prodComm
  have h_e'_eq : ∀ ω, e' (p.blockRV (n + 1) ω) = (p.blockRV n ω, p.obs n ω) := by
    intro ω
    simp [e', MeasurableEquiv.prodComm, h_e_eq]
  -- `μ.map (blockRV (n+1)) = (μ.map pair).map e'.symm` via `Measure.map_map`.
  have h_block_succ_eq : ∀ ω, p.blockRV (n + 1) ω
      = e'.symm (p.blockRV n ω, p.obs n ω) := fun ω =>
    (e'.symm_apply_eq.mpr (h_e'_eq ω).symm).symm
  have h_map_succ : μ.map (p.blockRV (n + 1))
      = (μ.map (fun ω => (p.blockRV n ω, p.obs n ω))).map e'.symm := by
    rw [Measure.map_map e'.symm.measurable h_pair_meas]
    congr 1
    funext ω
    exact h_block_succ_eq ω
  -- Apply equiv to singleton: `e'.symm ⁻¹' {block_{n+1} ω} = {(block_n ω, obs n ω)}`.
  have h_preim : e'.symm ⁻¹' {p.blockRV (n + 1) ω}
      = {(p.blockRV n ω, p.obs n ω)} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hq
      have := congrArg e' hq
      rw [MeasurableEquiv.apply_symm_apply, h_e'_eq] at this
      exact this
    · intro hq
      rw [hq]
      exact (h_block_succ_eq ω).symm
  have h_sing : (μ.map (p.blockRV (n + 1))) {p.blockRV (n + 1) ω}
      = (μ.map (fun ω' => (p.blockRV n ω', p.obs n ω')))
          {(p.blockRV n ω, p.obs n ω)} := by
    rw [h_map_succ, Measure.map_apply e'.symm.measurable
      (measurableSet_singleton _), h_preim]
  rw [h_sing]
  -- Factor the joint via condDistrib.
  have h_joint : μ.map (fun ω' => (p.blockRV n ω', p.obs n ω'))
      = (μ.map (p.blockRV n)) ⊗ₘ (condDistrib (p.obs n) (p.blockRV n) μ) :=
    (compProd_map_condDistrib h_obs_meas.aemeasurable).symm
  rw [h_joint]
  -- Compute singleton via compProd_apply_prod + lintegral_singleton.
  have h_sb : ({(p.blockRV n ω, p.obs n ω)} : Set ((Fin n → α) × α))
      = {p.blockRV n ω} ×ˢ {p.obs n ω} :=
    Set.singleton_prod_singleton.symm
  rw [h_sb, Measure.compProd_apply_prod (measurableSet_singleton _)
    (measurableSet_singleton _), lintegral_singleton, mul_comm]

omit [DecidableEq α] in
/-- Real-valued multiplicative chain rule at singletons. -/
theorem block_measure_succ_singleton_real_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    (μ.map (p.blockRV (n + 1))).real {p.blockRV (n + 1) ω}
      = (μ.map (p.blockRV n)).real {p.blockRV n ω}
        * (condDistrib (p.obs n) (p.blockRV n) μ (p.blockRV n ω)).real {p.obs n ω} := by
  rw [Measure.real, Measure.real, Measure.real,
    block_measure_succ_singleton_eq μ p n ω, ENNReal.toReal_mul]

/-! ## A.s. positivity of `P_n({block_n ω})` -/

omit [DecidableEq α] [Nonempty α] in
/-- For any finite alphabet pushforward and `n`, the singleton mass at the
observed block `block_n ω` is a.s. positive (the trajectory lies in the support).
-/
lemma block_singleton_pos_ae_at
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ ω ∂μ, 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω} := by
  classical
  have h_meas : Measurable (p.blockRV n) := p.measurable_blockRV n
  -- The "bad" set `S = {x | (μ.map blockRV n).real {x} = 0}` is finite, so measurable.
  set S : Set (Fin n → α) :=
    {x | (μ.map (p.blockRV n)).real {x} = 0} with hS_def
  have h_S_finite : S.Finite := Set.toFinite S
  have h_S_meas : MeasurableSet S := h_S_finite.measurableSet
  -- (μ.map blockRV n) S = sum over `x ∈ S.toFinset` of singleton masses = 0.
  have h_S_zero : (μ.map (p.blockRV n)) S = 0 := by
    have hS_eq : S = (h_S_finite.toFinset : Set (Fin n → α)) :=
      (Set.Finite.coe_toFinset h_S_finite).symm
    rw [hS_eq, ← sum_measure_singleton]
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hx_mem : x ∈ S := by rwa [Set.Finite.mem_toFinset] at hx
    have hx_real : (μ.map (p.blockRV n)).real {x} = 0 := hx_mem
    have h_lt : (μ.map (p.blockRV n)) {x} < ∞ := measure_lt_top _ _
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hx_real
    exact hx_real.resolve_right h_lt.ne
  -- Convert: μ {ω | block_n ω ∈ S} = 0.
  have h_preim : μ ((p.blockRV n) ⁻¹' S) = 0 := by
    rw [← Measure.map_apply h_meas h_S_meas]; exact h_S_zero
  refine ae_iff.mpr ?_
  refine measure_mono_null ?_ h_preim
  intro ω hω
  simp only [Set.mem_setOf_eq, not_lt] at hω
  show ω ∈ (p.blockRV n) ⁻¹' S
  simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
  exact le_antisymm hω measureReal_nonneg

omit [DecidableEq α] [Nonempty α] in
/-- A.s., the singleton mass at every prefix `block_i ω` (for `i ≤ n`) is positive. -/
lemma block_singleton_pos_ae_upTo
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ i ≤ n, 0 < (μ.map (p.blockRV i)).real {p.blockRV i ω} := by
  classical
  -- Intersection over the (finitely many) `i ≤ n`.
  have h_finset : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range (n + 1),
      0 < (μ.map (p.blockRV i)).real {p.blockRV i ω} := by
    refine (ae_ball_iff (Finset.range (n + 1)).countable_toSet).mpr ?_
    intro i _
    exact block_singleton_pos_ae_at μ p i
  filter_upwards [h_finset] with ω hω i hi
  exact hω i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-! ## Conditional singleton positivity (consequence of block positivity) -/

omit [DecidableEq α] in
/-- A.s. positivity of the conditional kernel singleton mass:
`(condDistrib (obs n) (blockRV n) μ (block_n ω)).real {obs n ω} > 0` a.s. -/
lemma cond_singleton_pos_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ ω ∂μ, 0 < (condDistrib (p.obs n) (p.blockRV n) μ
      (p.blockRV n ω)).real {p.obs n ω} := by
  -- From `block_singleton_pos_ae_at` at `n+1` and the chain rule, both factors must be positive.
  filter_upwards [block_singleton_pos_ae_at μ p (n + 1)] with ω hω
  have h_chain := block_measure_succ_singleton_real_eq μ p n ω
  have h_cond_nn : 0 ≤ (condDistrib (p.obs n) (p.blockRV n) μ
      (p.blockRV n ω)).real {p.obs n ω} := measureReal_nonneg
  rw [h_chain] at hω
  rcases lt_or_eq_of_le h_cond_nn with h | h
  · exact h
  · exfalso
    have h_prod_zero :
        (μ.map (p.blockRV n)).real {p.blockRV n ω}
          * (condDistrib (p.obs n) (p.blockRV n) μ (p.blockRV n ω)).real {p.obs n ω} = 0 := by
      rw [← h]; ring
    linarith

/-! ## Log identity: chain rule decomposition -/

omit [DecidableEq α] in
/-- **SMB chain rule** (a.s. log identity).

For a stationary process over a finite alphabet, the negative log-likelihood
of the observed block decomposes as a sum of per-step conditional negative
log-likelihoods:

  `-log P_n({block_n ω}) = ∑_{i<n} pmfLogCond μ p i ω`

almost surely. This is Cover–Thomas equation (16.107) in measure-theoretic
form. Proof: induction on `n`, using `block_measure_succ_singleton_real_eq`
and `Real.log_mul` (positive factors a.s.). -/
theorem log_block_eq_sum_pmfLogCond
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      -Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})
        = ∑ i ∈ Finset.range n, pmfLogCond μ p i ω := by
  classical
  induction n with
  | zero =>
    -- Base case: `blockRV 0` returns the unique map of empty type, mass 1.
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Finset.range_zero, Finset.sum_empty]
    have h_const : (μ.map (p.blockRV 0)).real {p.blockRV 0 ω} = 1 := by
      have h_meas : Measurable (p.blockRV 0) := p.measurable_blockRV 0
      rw [Measure.real, Measure.map_apply h_meas (measurableSet_singleton _)]
      have h_univ : (p.blockRV 0) ⁻¹' {p.blockRV 0 ω} = Set.univ := by
        ext ω'
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        funext i
        exact i.elim0
      rw [h_univ, measure_univ]
      rfl
    rw [h_const, Real.log_one, neg_zero]
  | succ n ih =>
    -- Step: combine `ih` with the multiplicative chain rule and `Real.log_mul`.
    filter_upwards [ih, block_singleton_pos_ae_upTo μ p n, cond_singleton_pos_ae μ p n]
      with ω h_ih h_pos h_cond_pos
    have h_chain := block_measure_succ_singleton_real_eq μ p n ω
    have h_Pn_pos : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω} :=
      h_pos n (le_refl n)
    rw [h_chain, Real.log_mul (ne_of_gt h_Pn_pos) (ne_of_gt h_cond_pos), neg_add]
    rw [Finset.sum_range_succ, ← h_ih]
    rfl

end InformationTheory.Shannon
