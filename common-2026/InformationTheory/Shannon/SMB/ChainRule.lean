import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import InformationTheory.Shannon.BirkhoffErgodic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# SMB chain rule decomposition

For a stationary process `p : StationaryProcess μ α` over a finite alphabet,
this file establishes the Cover–Thomas 16.8 chain rule for log-likelihood:

  `-log P_n({block_n ω}) = ∑_{i<n} -log P(obs i | block_i)(block_i ω){obs i ω}`

a.s. over `ω`. The right-hand side is named `pmfLogCond μ p i ω`. The result
is the algebraic identity that the Levy convergence and the Birkhoff +
Cesàro sandwich use to discharge the four hypotheses of
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
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Per-step conditional log-likelihood -/

/-- Per-step conditional negative log-likelihood:
`pmfLogCond μ p i ω = -log (condDistrib (obs i) (blockRV i) μ (block_i ω)).real {obs i ω}`.

For `i = 0`, `blockRV 0` is the unique map to `Fin 0 → α`, so the conditional
kernel reduces to the marginal `μ.map (p.X)`. -/
@[entry_point]
noncomputable def pmfLogCond
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (i : ℕ) : Ω → ℝ :=
  fun ω ↦ -Real.log
    ((condDistrib (p.obs i) (p.blockRV i) μ (p.blockRV i ω)).real {p.obs i ω})

omit [DecidableEq α] in
lemma measurable_pmfLogCond
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (i : ℕ) :
    Measurable (pmfLogCond μ p i) := by
  unfold pmfLogCond
  -- `(blockRV i ω, obs i ω)` is measurable; postcomposed with the discrete
  -- function `(b, a) ↦ (condDistrib (obs i) (blockRV i) μ b).real {a}`.
  have h_meas_pair : Measurable (fun ω ↦ (p.blockRV i ω, p.obs i ω)) :=
    (p.measurable_blockRV i).prodMk (p.measurable_obs i)
  have h_disc : Measurable (fun (q : (Fin i → α) × α) ↦
      -Real.log ((condDistrib (p.obs i) (p.blockRV i) μ q.1).real {q.2})) :=
    measurable_of_finite _
  exact h_disc.comp h_meas_pair

/-! ## Multiplicative chain rule at singletons (ENNReal level) -/

omit [DecidableEq α] in
/-- Chain rule for the block measure (ENNReal singleton form).

Pushforward of `μ` by `blockRV (n+1)` factors at any singleton via the
conditional kernel `condDistrib (obs n) (blockRV n) μ`:
`P_{n+1}({block_{n+1} ω}) = P_n({block_n ω}) · c_n(block_n ω){obs n ω}`. -/
@[entry_point]
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
  have h_pair_meas : Measurable (fun ω ↦ (p.blockRV n ω, p.obs n ω)) :=
    h_block_meas.prodMk h_obs_meas
  -- Equiv `e : (Fin (n+1) → α) ≃ᵐ α × (Fin n → α)` from `piFinSuccAbove (Fin.last n)`.
  let e : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) (Fin.last n)
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
      = e'.symm (p.blockRV n ω, p.obs n ω) := fun ω ↦
    (e'.symm_apply_eq.mpr (h_e'_eq ω).symm).symm
  have h_map_succ : μ.map (p.blockRV (n + 1))
      = (μ.map (fun ω ↦ (p.blockRV n ω, p.obs n ω))).map e'.symm := by
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
      = (μ.map (fun ω' ↦ (p.blockRV n ω', p.obs n ω')))
          {(p.blockRV n ω, p.obs n ω)} := by
    rw [h_map_succ, Measure.map_apply e'.symm.measurable
      (measurableSet_singleton _), h_preim]
  rw [h_sing]
  -- Factor the joint via condDistrib.
  have h_joint : μ.map (fun ω' ↦ (p.blockRV n ω', p.obs n ω'))
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
@[entry_point]
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
@[entry_point]
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
@[entry_point]
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

/-! ## Integrability and integral identity

`pmfLogCond μ p l` is integrable, and its integral equals
`conditionalEntropyTail μ p l`. This bridges the Birkhoff time-average to the
spatial average used by the sandwich. -/

omit [DecidableEq α] in
/-- The expected per-step conditional log-likelihood equals the conditional
entropy tail (Cover–Thomas (16.107) expectation):
`∫ ω, pmfLogCond μ p l ω dμ = conditionalEntropyTail μ p l`.

Proof: push forward through `(blockRV l, obs l)`, disintegrate via
`compProd_map_condDistrib`, apply Fubini, evaluate the inner integral over the
finite alphabet via `integral_fintype`, and recognize the result as the
definition of `conditionalEntropyTail`. -/
@[entry_point]
theorem integral_pmfLogCond_eq_conditionalEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (l : ℕ) :
    ∫ ω, pmfLogCond μ p l ω ∂μ = conditionalEntropyTail μ p l := by
  classical
  have h_block_meas : Measurable (p.blockRV l) := p.measurable_blockRV l
  have h_obs_meas : Measurable (p.obs l) := p.measurable_obs l
  have h_pair_meas : Measurable (fun ω ↦ (p.blockRV l ω, p.obs l ω)) :=
    h_block_meas.prodMk h_obs_meas
  -- Define `F : (Fin l → α) × α → ℝ` as `(y, x) ↦ -log (cd y).real {x}`.
  set F : (Fin l → α) × α → ℝ :=
    fun q ↦ -Real.log ((condDistrib (p.obs l) (p.blockRV l) μ q.1).real {q.2}) with hF_def
  have hF_meas : Measurable F := measurable_of_finite _
  -- Step 1: `∫ ω, pmfLogCond p l ω dμ = ∫ (y, x), F (y, x) d(μ.map pair)`.
  have h_step1 : ∫ ω, pmfLogCond μ p l ω ∂μ
      = ∫ q, F q ∂(μ.map (fun ω ↦ (p.blockRV l ω, p.obs l ω))) := by
    rw [integral_map h_pair_meas.aemeasurable hF_meas.aestronglyMeasurable]
    rfl
  rw [h_step1]
  -- Step 2: factor joint via compProd_map_condDistrib.
  have h_joint : μ.map (fun ω ↦ (p.blockRV l ω, p.obs l ω))
      = (μ.map (p.blockRV l)) ⊗ₘ (condDistrib (p.obs l) (p.blockRV l) μ) :=
    (compProd_map_condDistrib h_obs_meas.aemeasurable).symm
  rw [h_joint]
  -- Step 3: Fubini via integral_compProd.
  haveI : IsProbabilityMeasure (μ.map (p.blockRV l)) :=
    Measure.isProbabilityMeasure_map h_block_meas.aemeasurable
  have hF_int :
      Integrable F ((μ.map (p.blockRV l)) ⊗ₘ (condDistrib (p.obs l) (p.blockRV l) μ)) := by
    rw [← h_joint]
    exact Integrable.of_finite
  rw [Measure.integral_compProd hF_int]
  -- Step 4: rewrite inner integral over each `cd y` (a Markov probability measure on α)
  -- as a finite sum: `∫ x, F (y, x) d(cd y) = ∑ x, (cd y).real {x} • F (y, x)`.
  -- For each y, the inner integrand is bounded (Fintype), so integrable.
  unfold conditionalEntropyTail InformationTheory.MeasureFano.condEntropy
  refine MeasureTheory.integral_congr_ae ?_
  refine ae_of_all _ fun y ↦ ?_
  -- inner: ∫ x, F (y, x) d(cd y) vs ∑ x, negMulLog ((cd y).real {x})
  show ∫ x, F (y, x) ∂(condDistrib (p.obs l) (p.blockRV l) μ y)
      = ∑ x, Real.negMulLog ((condDistrib (p.obs l) (p.blockRV l) μ y).real {x})
  haveI : IsProbabilityMeasure (condDistrib (p.obs l) (p.blockRV l) μ y) := inferInstance
  rw [integral_fintype (μ := condDistrib (p.obs l) (p.blockRV l) μ y) Integrable.of_finite]
  refine Finset.sum_congr rfl ?_
  intro x _
  -- `(cd y).real {x} • F (y, x) = (cd y).real {x} * (-log ((cd y).real {x})) = negMulLog ...`
  show (condDistrib (p.obs l) (p.blockRV l) μ y).real {x} • F (y, x)
      = Real.negMulLog ((condDistrib (p.obs l) (p.blockRV l) μ y).real {x})
  rw [hF_def, Real.negMulLog, smul_eq_mul]
  ring

omit [DecidableEq α] in
/-- `pmfLogCond μ p l` is integrable. -/
lemma integrable_pmfLogCond
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (l : ℕ) :
    Integrable (pmfLogCond μ p l) μ := by
  classical
  have h_block_meas : Measurable (p.blockRV l) := p.measurable_blockRV l
  have h_obs_meas : Measurable (p.obs l) := p.measurable_obs l
  have h_pair_meas : Measurable (fun ω ↦ (p.blockRV l ω, p.obs l ω)) :=
    h_block_meas.prodMk h_obs_meas
  -- View `pmfLogCond p l` as `F ∘ pair` where `F : (Fin l → α) × α → ℝ` is measurable.
  set F : (Fin l → α) × α → ℝ :=
    fun q ↦ -Real.log ((condDistrib (p.obs l) (p.blockRV l) μ q.1).real {q.2})
  have hF_meas : Measurable F := measurable_of_finite _
  have h_eq : pmfLogCond μ p l = F ∘ (fun ω ↦ (p.blockRV l ω, p.obs l ω)) := by
    funext ω; rfl
  rw [h_eq]
  -- Integrable iff bounded ∫⁻ ‖F ∘ pair‖. Push to μ.map pair and use Fintype.
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ (p.blockRV l ω, p.obs l ω))) :=
    Measure.isProbabilityMeasure_map h_pair_meas.aemeasurable
  have h_int_pair : Integrable F (μ.map (fun ω ↦ (p.blockRV l ω, p.obs l ω))) :=
    Integrable.of_finite
  exact (MeasureTheory.integrable_map_measure hF_meas.aestronglyMeasurable
    h_pair_meas.aemeasurable).mp h_int_pair

/-! ## Birkhoff per-level application

For each fixed level `l`, the Birkhoff time average of `pmfLogCond p l` along
the orbit converges a.s. to `conditionalEntropyTail μ p l`. This is the
"l-Markov approximation" output that the SMB sandwich (Algoet–Cover) chains
with `H_l → entropyRate` to obtain the full result. -/

omit [DecidableEq α] in
/-- Birkhoff applied to per-step conditional log-likelihood.

For an ergodic process and fixed level `l`, the Birkhoff time average of
`pmfLogCond p l` converges a.s. to `conditionalEntropyTail μ p l`:

  `(1/(n+1)) ∑_{i=0}^{n} pmfLogCond p l (T^[i] ω) → H_l = H(X_l | X_0, …, X_{l-1})`.

The proof composes:
* `birkhoff_ergodic_ae` (file `BirkhoffErgodic.lean`) for the abstract Birkhoff
  convergence;
* `integrable_pmfLogCond` for integrability;
* `integral_pmfLogCond_eq_conditionalEntropyTail` for the integral identity. -/
@[entry_point]
theorem birkhoffAverage_pmfLogCond_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) (l : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n ↦ birkhoffAverageReal p.T (pmfLogCond μ p.toStationaryProcess l) n ω)
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess l)) := by
  have h_int :
      Integrable (pmfLogCond μ p.toStationaryProcess l) μ :=
    integrable_pmfLogCond μ p.toStationaryProcess l
  have h_integral_eq :
      ∫ x, pmfLogCond μ p.toStationaryProcess l x ∂μ
        = conditionalEntropyTail μ p.toStationaryProcess l :=
    integral_pmfLogCond_eq_conditionalEntropyTail μ p.toStationaryProcess l
  -- Apply Birkhoff to f := pmfLogCond and rewrite the limit via the integral identity.
  have h_birkhoff :=
    birkhoff_ergodic_ae p.measurePreserving p.ergodic h_int
  rw [← h_integral_eq]
  exact h_birkhoff

end InformationTheory.Shannon
