import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.Achievability
import InformationTheory.Shannon.MaxEntropy.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Shannon noisy channel coding theorem — full form (Cover-Thomas 7.7.1)

Integrates input distribution maximization, expurgation (average → max error),
and the main achievability argument.

## Main definitions

* `pmfToMeasure` — lifts a pmf vector `p : α → ℝ` to a `Measure α`.
* `capacity` — channel capacity `sup { I(p; W).toReal | p ∈ stdSimplex }`.
* `Code.subcode` — restricts a code to a sub-message set.
* `pSmooth` — smoothed input `(1-δ) • p₀ + δ • uniform`.
* `Code_lift_from_subtype` — lifts a code on the support subtype to the full alphabet.

## Main statements

* `capacity_nonneg` — `capacity W ≥ 0`.
* `exists_capacity_achiever` — capacity is attained by some `p ∈ stdSimplex`.
* `capacity_lt_implies_exists_pmf` — `R < capacity W` implies some `p` with `R < I(p; W)`.
* `continuous_mutualInfoOfChannel_left` — `p ↦ I(pmfToMeasure p; W).toReal` is continuous
  on `stdSimplex`.
* `channel_coding_achievability_max_error` — average error → max error via expurgation.
* `mutualInfoOfChannel_restrict_to_support` — MI is invariant under restriction to support.
* `shannon_noisy_channel_coding_theorem` — for any `R < capacity W` and `ε > 0`,
  there exists `N` such that for all `n ≥ N`, a code of size `≥ exp(n R)` with max error `< ε`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Input distribution maximization -/

/-- **Lift a pmf vector to a measure**:
`pmfToMeasure p = ∑ a, ENNReal.ofReal (p a) • Measure.dirac a`. -/
noncomputable def pmfToMeasure (p : α → ℝ) : Measure α :=
  ∑ a : α, ENNReal.ofReal (p a) • Measure.dirac a

omit [DecidableEq α] [Nonempty α] in
/-- Atom evaluation: `(pmfToMeasure p) {a} = ENNReal.ofReal (p a)`. -/
lemma pmfToMeasure_apply_singleton (p : α → ℝ) (a : α) :
    (pmfToMeasure p) ({a} : Set α) = ENNReal.ofReal (p a) := by
  unfold pmfToMeasure
  rw [Measure.finsetSum_apply Finset.univ _ {a}]
  -- ∑ b, (ENNReal.ofReal (p b) • Measure.dirac b) {a} collapses to b = a.
  rw [Finset.sum_eq_single a]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton a)]
  · intro b _ hb
    simp [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton a),
      Set.indicator_of_notMem
        (show b ∉ ({a} : Set α) by simp only [Set.mem_singleton_iff]; exact hb)]
  · intro h
    exact (h (Finset.mem_univ a)).elim

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `pmfToMeasure p` is a probability measure when `p ∈ stdSimplex ℝ α`. -/
lemma pmfToMeasure_isProbabilityMeasure
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α) :
    IsProbabilityMeasure (pmfToMeasure p) := by
  refine ⟨?_⟩
  unfold pmfToMeasure
  rw [Measure.finsetSum_apply Finset.univ _ Set.univ]
  -- ∑ a, (ENNReal.ofReal (p a) • Measure.dirac a) Set.univ = ∑ a, ENNReal.ofReal (p a).
  have h_each : ∀ a ∈ (Finset.univ : Finset α),
      (ENNReal.ofReal (p a) • Measure.dirac a) (Set.univ : Set α) = ENNReal.ofReal (p a) := by
    intro a _
    simp [Measure.smul_apply]
  rw [Finset.sum_congr rfl h_each]
  -- ∑ a, ENNReal.ofReal (p a) = 1
  have hsum := hp.2
  have hnn : ∀ a, 0 ≤ p a := hp.1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ hnn a), hsum, ENNReal.ofReal_one]

omit [DecidableEq α] [Nonempty α] in
/-- `(pmfToMeasure p).real {a} = p a` when `p ∈ stdSimplex`. -/
lemma pmfToMeasure_real_singleton
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α) (a : α) :
    (pmfToMeasure p).real {a} = p a := by
  unfold Measure.real
  rw [pmfToMeasure_apply_singleton]
  exact ENNReal.toReal_ofReal (hp.1 a)

/-- **Channel capacity** (Cover-Thomas 7.5):
`capacity W := sup { I(p; W).toReal | p ∈ stdSimplex }`. -/
noncomputable def capacity (W : Channel α β) : ℝ :=
  sSup ((fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
        stdSimplex ℝ α)

omit [DecidableEq α] [MeasurableSingletonClass α] [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
/-- The capacity image set is nonempty (witnessed by a `Pi.single` Dirac input). -/
lemma capacity_image_nonempty (W : Channel α β) :
    ((fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
      stdSimplex ℝ α).Nonempty := by
  classical
  exact ⟨_, Pi.single (Classical.arbitrary α) 1, single_mem_stdSimplex ℝ _, rfl⟩

omit [DecidableEq α] [DecidableEq β] in
/-- `capacity` value set is bounded above by `H(X) + H(Y)`-style entropy bound. -/
theorem capacity_bddAbove (W : Channel α β) [IsMarkovKernel W] :
    BddAbove ((fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
              stdSimplex ℝ α) := by
  classical
  -- I(p; W).toReal = H(X) + H(Y) - H(X,Y) ≤ H(X) + H(Y) ≤ log |α| + log |β|.
  refine ⟨Real.log (Fintype.card α) + Real.log (Fintype.card β), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  have h_id := mutualInfoOfChannel_eq_HX_add_HY_sub_HZ (pmfToMeasure p) W
  show (mutualInfoOfChannel (pmfToMeasure p) W).toReal
      ≤ Real.log (Fintype.card α) + Real.log (Fintype.card β)
  rw [h_id]
  -- H(X) ≤ log |α|.
  have hHX_le : entropy (jointDistribution (pmfToMeasure p) W) Prod.fst
      ≤ Real.log (Fintype.card α) :=
    entropy_le_log_card _ Prod.fst measurable_fst
  have hHY_le : entropy (jointDistribution (pmfToMeasure p) W) Prod.snd
      ≤ Real.log (Fintype.card β) :=
    entropy_le_log_card _ Prod.snd measurable_snd
  -- H(X,Y) ≥ 0.
  have hHXY_nn : 0 ≤ entropy (jointDistribution (pmfToMeasure p) W) id :=
    entropy_nonneg _ id measurable_id
  linarith

omit [DecidableEq α] [DecidableEq β] in
/-- `capacity W ≥ 0`. -/
@[entry_point]
theorem capacity_nonneg (W : Channel α β) [IsMarkovKernel W] : 0 ≤ capacity W := by
  unfold capacity
  -- Each `.toReal` value in the image is ≥ 0.
  obtain ⟨v, hv_mem_image⟩ := capacity_image_nonempty W
  refine le_csSup_of_le (capacity_bddAbove W) hv_mem_image ?_
  obtain ⟨_p, _hp_mem, hp_eq⟩ := hv_mem_image
  simp only at hp_eq
  rw [← hp_eq]
  exact ENNReal.toReal_nonneg

/-! ### Continuity of `I(p; W).toReal` in p -/

omit [Nonempty α] [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β] in
/-- For `p ∈ stdSimplex`, the output marginal `(p ⊗ₘ W).snd` real-value on `{b}` is
`∑ a, p a · (W a).real {b}`. -/
private lemma outputDistribution_real_singleton_of_stdSimplex
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] (b : β) :
    (outputDistribution (pmfToMeasure p) W).real {b}
      = ∑ a : α, p a * (W a).real {b} := by
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  -- ((p ⊗ₘ W).snd){b} = (p ⊗ₘ W)(univ ×ˢ {b}) = ∫⁻ a, W a {b} ∂(pmfToMeasure p).
  have h1 : (outputDistribution (pmfToMeasure p) W) {b}
      = (jointDistribution (pmfToMeasure p) W) (Set.univ ×ˢ ({b} : Set β)) := by
    show (jointDistribution (pmfToMeasure p) W).snd {b} = _
    rw [Measure.snd_apply (measurableSet_singleton _)]
    congr 1; ext ⟨a, b'⟩; simp
  rw [Measure.real, h1, jointDistribution_def]
  have h2 : ((pmfToMeasure p) ⊗ₘ W) (Set.univ ×ˢ ({b} : Set β))
      = ∫⁻ a, W a {b} ∂(pmfToMeasure p) := by
    rw [Measure.compProd_apply (MeasurableSet.univ.prod (measurableSet_singleton _))]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
    show (W a) (Prod.mk a ⁻¹' (Set.univ ×ˢ ({b} : Set β))) = (W a) {b}
    congr 1; ext y; simp
  rw [h2]
  -- ∫⁻ a, W a {b} ∂(pmfToMeasure p) = ∑ a, ENNReal.ofReal (p a) * (W a) {b}.
  unfold pmfToMeasure
  rw [MeasureTheory.lintegral_finsetSum_measure]
  simp_rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_sum (by
    intro a _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp.1 a)]
  rfl

omit [Nonempty α] [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β] in
/-- For `p ∈ stdSimplex`, the joint `(p ⊗ₘ W)` real-value on `{(a,b)}` is
`(p a) · (W a).real {b}`. -/
private lemma jointDistribution_real_singleton_of_stdSimplex
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] (a : α) (b : β) :
    (jointDistribution (pmfToMeasure p) W).real {(a, b)}
      = p a * (W a).real {b} := by
  classical
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  -- {(a, b)} = {a} ×ˢ {b}.
  have h_eq : ({(a, b)} : Set (α × β)) = ({a} : Set α) ×ˢ ({b} : Set β) := by
    ext ⟨x, y⟩; simp [Prod.ext_iff]
  rw [Measure.real, jointDistribution_def, h_eq,
      Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
  -- ∫⁻ x in {a}, W x {b} ∂(pmfToMeasure p) = ENNReal.ofReal (p a) * W a {b}.
  -- Use setLIntegral on dirac decomposition: rewrite as
  -- ∫⁻ x, ({a}.indicator (fun x => W x {b})) x ∂...
  rw [← MeasureTheory.lintegral_indicator (measurableSet_singleton _)]
  unfold pmfToMeasure
  rw [MeasureTheory.lintegral_finsetSum_measure]
  simp_rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac, smul_eq_mul]
  -- ∑ a', ENNReal.ofReal (p a') * (({a}.indicator (fun x => W x {b})) a').
  -- For a' = a: indicator value is W a {b}. For a' ≠ a: 0.
  have h_each : ∀ a' ∈ (Finset.univ : Finset α),
      ENNReal.ofReal (p a') * Set.indicator ({a} : Set α) (fun x ↦ W x {b}) a'
        = if a' = a then ENNReal.ofReal (p a) * W a {b} else 0 := by
    intro a' _
    by_cases hcase : a' = a
    · subst hcase
      rw [if_pos rfl, Set.indicator_of_mem (Set.mem_singleton _)]
    · rw [if_neg hcase, Set.indicator_of_notMem (by simp [hcase])]
      simp
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ a)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp.1 a)]
  rfl

omit [Nonempty α] [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
/-- For `p ∈ stdSimplex`, `(pmfToMeasure p).real {a}` rewritten using `J.map Prod.fst = p`. -/
private lemma jointMap_fst_real_singleton_of_stdSimplex
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] (a : α) :
    ((jointDistribution (pmfToMeasure p) W).map Prod.fst).real {a} = p a := by
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  have h_fst : (jointDistribution (pmfToMeasure p) W).map Prod.fst = pmfToMeasure p := by
    show ((pmfToMeasure p) ⊗ₘ W).map Prod.fst = pmfToMeasure p
    rw [show ((pmfToMeasure p) ⊗ₘ W).map Prod.fst = ((pmfToMeasure p) ⊗ₘ W).fst from rfl]
    exact Measure.fst_compProd _ W
  rw [h_fst, pmfToMeasure_real_singleton hp]

omit [Nonempty α] [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β] in
/-- For `p ∈ stdSimplex`, `J.map Prod.snd .real {b} = ∑ a, p a · (W a).real {b}`. -/
private lemma jointMap_snd_real_singleton_of_stdSimplex
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] (b : β) :
    ((jointDistribution (pmfToMeasure p) W).map Prod.snd).real {b}
      = ∑ a : α, p a * (W a).real {b} := by
  have h_snd : (jointDistribution (pmfToMeasure p) W).map Prod.snd
      = outputDistribution (pmfToMeasure p) W := rfl
  rw [h_snd]
  exact outputDistribution_real_singleton_of_stdSimplex hp W b

omit [Nonempty α] [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β] in
/-- For `p ∈ stdSimplex`, `J.map id .real {(a,b)} = p a · (W a).real {b}`. -/
private lemma jointMap_id_real_singleton_of_stdSimplex
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] (a : α) (b : β) :
    ((jointDistribution (pmfToMeasure p) W).map id).real {(a, b)} = p a * (W a).real {b} := by
  rw [Measure.map_id]
  exact jointDistribution_real_singleton_of_stdSimplex hp W a b

omit [DecidableEq α] [DecidableEq β] in
/-- For `p ∈ stdSimplex`, `I(pmfToMeasure p; W).toReal` equals the 3-entropy expression
in `p`. -/
private lemma mutualInfoOfChannel_toReal_eq_of_stdSimplex
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] :
    (mutualInfoOfChannel (pmfToMeasure p) W).toReal
      = (∑ a : α, Real.negMulLog (p a))
        + (∑ b : β, Real.negMulLog (∑ a : α, p a * (W a).real {b}))
        - (∑ ab : α × β, Real.negMulLog (p ab.1 * (W ab.1).real {ab.2})) := by
  classical
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  rw [mutualInfoOfChannel_eq_HX_add_HY_sub_HZ]
  -- entropy μ X = ∑ x, negMulLog ((μ.map X).real {x}).
  unfold InformationTheory.Shannon.entropy
  congr 1
  · -- H(X) + H(Y) match.
    congr 1
    · refine Finset.sum_congr rfl (fun a _ ↦ ?_)
      rw [jointMap_fst_real_singleton_of_stdSimplex hp W a]
    · refine Finset.sum_congr rfl (fun b _ ↦ ?_)
      rw [jointMap_snd_real_singleton_of_stdSimplex hp W b]
  · -- H(X,Y) over α × β.
    refine Finset.sum_congr rfl (fun ab _ ↦ ?_)
    rw [jointMap_id_real_singleton_of_stdSimplex hp W ab.1 ab.2]

omit [DecidableEq α] [DecidableEq β] in
/-- `p ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal` is continuous on `stdSimplex ℝ α`. -/
theorem continuous_mutualInfoOfChannel_left (W : Channel α β) [IsMarkovKernel W] :
    ContinuousOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) := by
  -- Define the 3-entropy expression in p (continuous on Set.univ).
  set g : (α → ℝ) → ℝ := fun p ↦
    (∑ a : α, Real.negMulLog (p a))
      + (∑ b : β, Real.negMulLog (∑ a : α, p a * (W a).real {b}))
      - (∑ ab : α × β, Real.negMulLog (p ab.1 * (W ab.1).real {ab.2})) with hg_def
  have h_eq_on : ∀ p ∈ stdSimplex ℝ α,
      (mutualInfoOfChannel (pmfToMeasure p) W).toReal = g p := by
    intro p hp
    exact mutualInfoOfChannel_toReal_eq_of_stdSimplex hp W
  -- ContinuousOn from Continuous on a superset.
  refine ContinuousOn.congr ?_ h_eq_on
  refine Continuous.continuousOn ?_
  -- Continuity of g.
  refine Continuous.sub ?_ ?_
  · refine Continuous.add ?_ ?_
    · -- ∑ a, negMulLog (p a).
      refine continuous_finsetSum _ (fun a _ ↦ ?_)
      exact Real.continuous_negMulLog.comp (continuous_apply a)
    · -- ∑ b, negMulLog (∑ a, p a * c_a)
      refine continuous_finsetSum _ (fun b _ ↦ ?_)
      refine Real.continuous_negMulLog.comp ?_
      refine continuous_finsetSum _ (fun a _ ↦ ?_)
      exact (continuous_apply a).mul continuous_const
  · -- ∑ ab, negMulLog (p ab.1 * c_{ab.1, ab.2}).
    refine continuous_finsetSum _ (fun ab _ ↦ ?_)
    refine Real.continuous_negMulLog.comp ?_
    exact (continuous_apply ab.1).mul continuous_const

omit [DecidableEq α] [DecidableEq β] in
/-- Capacity is attained: there exists `p ∈ stdSimplex` maximizing `I(pmfToMeasure p; W)`. -/
@[entry_point]
theorem exists_capacity_achiever (W : Channel α β) [IsMarkovKernel W] :
    ∃ p ∈ stdSimplex ℝ α, IsMaxOn
      (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p := by
  classical
  refine IsCompact.exists_isMaxOn (isCompact_stdSimplex ℝ α) ?_
    (continuous_mutualInfoOfChannel_left W)
  exact ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary α)⟩

omit [DecidableEq α] [DecidableEq β] in
/-- `R < capacity W` implies there exists `p ∈ stdSimplex` with
`R < I(pmfToMeasure p; W).toReal`. -/
theorem capacity_lt_implies_exists_pmf
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p ∈ stdSimplex ℝ α,
      R < (mutualInfoOfChannel (pmfToMeasure p) W).toReal := by
  unfold capacity at hR
  -- `lt_csSup_iff` requires BddAbove and Nonempty.
  have h_bdd := capacity_bddAbove W
  have h_ne := capacity_image_nonempty W
  rw [lt_csSup_iff h_bdd h_ne] at hR
  obtain ⟨v, ⟨p, hp_mem, hp_eq⟩, hv_lt⟩ := hR
  refine ⟨p, hp_mem, ?_⟩
  simp only at hp_eq
  rw [hp_eq]
  exact hv_lt

/-! ## Expurgation (average → max error) -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Markov inequality: the number of `m` with `errorProbAt > K · avg` is at most `M / K`. -/
theorem errorProbAt_filter_card_bound
    {M n : ℕ} (c : Code M n α β) (W : Channel α β) [IsMarkovKernel W]
    {K : ℝ} (hK : 1 < K) :
    ((Finset.univ : Finset (Fin M)).filter
        (fun m ↦ K * (c.averageErrorProb W).toReal < (c.errorProbAt W m).toReal)).card
      * K ≤ (M : ℝ) := by
  classical
  set f : Fin M → ℝ := fun m ↦ (c.errorProbAt W m).toReal with hf_def
  set avg : ℝ := (c.averageErrorProb W).toReal with havg_def
  set F : Finset (Fin M) := (Finset.univ : Finset (Fin M)).filter
      (fun m ↦ K * avg < f m) with hF_def
  -- Each summand is finite and bounded.
  have hK_pos : 0 < K := lt_trans zero_lt_one hK
  have h_each_le_one : ∀ m : Fin M, c.errorProbAt W m ≤ 1 := by
    intro m
    haveI : IsProbabilityMeasure (Measure.pi (fun i ↦ W (c.encoder m i))) := by infer_instance
    exact prob_le_one
  have h_each_ne_top : ∀ m : Fin M, c.errorProbAt W m ≠ ∞ := fun m ↦
    ((h_each_le_one m).trans_lt ENNReal.one_lt_top).ne
  have hf_nn : ∀ m, 0 ≤ f m := fun m ↦ ENNReal.toReal_nonneg
  -- Case split on M = 0.
  by_cases hM : M = 0
  · subst hM
    -- F is empty.
    have hF_empty : F = ∅ := Finset.eq_empty_of_forall_notMem (fun m ↦ Fin.elim0 m)
    simp [hF_empty]
  · have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have hM_R_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    -- avg as a Real sum: avg = (1/M) * ∑ f m.
    have h_avg_eq : avg = (M : ℝ)⁻¹ * ∑ m : Fin M, f m := by
      simp only [havg_def, hf_def, Code.averageErrorProb, hM, if_false]
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          ENNReal.toReal_sum (fun m _ ↦ h_each_ne_top m)]
    -- Sum of f over all = M * avg.
    have h_sum_eq : ∑ m : Fin M, f m = (M : ℝ) * avg := by
      rw [h_avg_eq, ← mul_assoc, mul_inv_cancel₀ hM_R_pos.ne', one_mul]
    -- avg ≥ 0.
    have h_avg_nn : 0 ≤ avg := ENNReal.toReal_nonneg
    -- Sub-case avg = 0: F is empty.
    by_cases h_avg_zero : avg = 0
    · -- ∑ f m = 0 with all f m ≥ 0 implies each f m = 0.
      have h_sum_zero : ∑ m : Fin M, f m = 0 := by rw [h_sum_eq, h_avg_zero, mul_zero]
      have h_each_zero : ∀ m ∈ (Finset.univ : Finset (Fin M)), f m = 0 := by
        intro m hm
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hf_nn i)).mp h_sum_zero m hm
      have hF_empty : F = ∅ := by
        rw [hF_def]
        refine Finset.filter_false_of_mem ?_
        intro m hm
        rw [h_each_zero m hm, h_avg_zero, mul_zero]
        exact lt_irrefl 0
      rw [hF_empty]
      simp [hM_R_pos.le]
    · have h_avg_pos : 0 < avg := lt_of_le_of_ne h_avg_nn (Ne.symm h_avg_zero)
      -- For m ∈ F, f m ≥ K * avg (in fact >).
      have h_F_lb : ∀ m ∈ F, K * avg ≤ f m := by
        intro m hm
        rw [hF_def, Finset.mem_filter] at hm
        exact hm.2.le
      -- card F * (K * avg) ≤ ∑_{m ∈ F} f m  (via Finset.card_nsmul_le_sum).
      have h_card_le_sum_F : (F.card : ℝ) * (K * avg) ≤ ∑ m ∈ F, f m := by
        have := F.card_nsmul_le_sum (fun m ↦ f m) (K * avg) h_F_lb
        simpa [nsmul_eq_mul] using this
      -- ∑_{m ∈ F} f m ≤ ∑ all f m = M * avg.
      have h_sum_F_le : ∑ m ∈ F, f m ≤ ∑ m : Fin M, f m := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro m _; exact Finset.mem_univ m
        · intros m _ _; exact hf_nn m
      have h_card_le_M_avg : (F.card : ℝ) * (K * avg) ≤ (M : ℝ) * avg :=
        h_card_le_sum_F.trans (h_sum_F_le.trans_eq h_sum_eq)
      -- Divide by avg > 0.
      have h_rewrite : (F.card : ℝ) * (K * avg) = ((F.card : ℝ) * K) * avg := by ring
      rw [h_rewrite] at h_card_le_M_avg
      exact (mul_le_mul_iff_of_pos_right h_avg_pos).mp h_card_le_M_avg

/-- **Sub-code** restricted to a message subset `S`: encoder restricts to `S`, decoder maps
outside `S` to a fixed fallback message. -/
noncomputable def Code.subcode
    {M n : ℕ} (c : Code M n α β) (S : Finset (Fin M)) (hS : 0 < S.card) :
    Code S.card n α β :=
  { encoder := fun m' ↦ c.encoder (S.equivFin.symm ⟨m', by simp⟩).val
    decoder := fun y ↦
      let m := c.decoder y
      if h : m ∈ S then
        ⟨(S.equivFin ⟨m, h⟩).val, by simp⟩
      else ⟨0, hS⟩ }

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Sub-code error probability is bounded above by the original code's `errorProbAt`. -/
theorem Code.subcode_errorProbAt_le
    {M n : ℕ} (c : Code M n α β) (W : Channel α β) [IsMarkovKernel W]
    (S : Finset (Fin M)) (hS : 0 < S.card) (m' : Fin S.card) :
    (c.subcode S hS).errorProbAt W m'
      ≤ c.errorProbAt W (S.equivFin.symm ⟨m', by simp⟩).val := by
  classical
  -- Notation: `m₀_sub : ↑S` is `S.equivFin.symm ⟨m'.val, _⟩`; `m₀ : Fin M` is its `.val`.
  set m₀_sub : ↑S := S.equivFin.symm ⟨m'.val, by simp⟩ with hm₀_sub_def
  set m₀ : Fin M := m₀_sub.val with hm₀_def
  have hm₀_mem : m₀ ∈ S := m₀_sub.property
  -- Encoder coincidence: (subcode).encoder m' = c.encoder m₀.
  have h_enc_eq : (c.subcode S hS).encoder m' = c.encoder m₀ := by
    show c.encoder (S.equivFin.symm ⟨m'.val, by simp⟩).val
        = c.encoder m₀
    rfl
  -- The two `Measure.pi` factors coincide.
  have h_meas_eq :
      Measure.pi (fun i ↦ W ((c.subcode S hS).encoder m' i))
        = Measure.pi (fun i ↦ W (c.encoder m₀ i)) := by
    rfl
  -- Set inclusion: (subcode).errorEvent m' ⊆ c.errorEvent m₀.
  have h_subset : (c.subcode S hS).errorEvent m' ⊆ c.errorEvent m₀ := by
    intro y hy
    rw [Code.mem_errorEvent] at hy ⊢
    -- hy : (subcode).decoder y ≠ m'.
    -- Goal: c.decoder y ≠ m₀.
    intro h_eq
    apply hy
    -- Show (subcode).decoder y = m'.
    show (if h : c.decoder y ∈ S then
            (⟨(S.equivFin ⟨c.decoder y, h⟩).val, by simp⟩
              : Fin S.card)
          else ⟨0, hS⟩) = m'
    have h_mem : c.decoder y ∈ S := h_eq ▸ hm₀_mem
    rw [dif_pos h_mem]
    -- Now show: ⟨(S.equivFin ⟨c.decoder y, h_mem⟩).val, _⟩ = m'.
    have h_efy_eq : S.equivFin ⟨c.decoder y, h_mem⟩ = ⟨m'.val, by simp⟩ := by
      have h_subS_eq : (⟨c.decoder y, h_mem⟩ : ↑S) = m₀_sub := by
        apply Subtype.ext
        simp [hm₀_def, h_eq]
      rw [h_subS_eq, hm₀_sub_def, Equiv.apply_symm_apply]
    -- Conclude.
    apply Fin.ext
    rw [h_efy_eq]
  -- Conclude with measure monotonicity.
  show Measure.pi (fun i ↦ W ((c.subcode S hS).encoder m' i))
        ((c.subcode S hS).errorEvent m') ≤
      Measure.pi (fun i ↦ W (c.encoder m₀ i)) (c.errorEvent m₀)
  rw [h_meas_eq]
  exact measure_mono h_subset

/-- Helper: linearization `(fun n : ℕ => (n : ℝ) * c) → ∞` for `c > 0`. -/
lemma tendsto_nat_mul_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * c) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro b
  refine ⟨Nat.ceil (b / c) + 1, ?_⟩
  intro n hn
  have h_n_R : b / c ≤ (n : ℝ) := by
    have h1 : (b / c : ℝ) ≤ Nat.ceil (b / c) := Nat.le_ceil _
    have h2 : (Nat.ceil (b / c) : ℝ) ≤ (n : ℝ) := by
      have : Nat.ceil (b / c) ≤ n := Nat.le_of_succ_le hn
      exact_mod_cast this
    linarith
  have h_mul : b / c * c ≤ (n : ℝ) * c :=
    mul_le_mul_of_nonneg_right h_n_R hc.le
  rwa [div_mul_cancel₀ _ hc.ne'] at h_mul

/-- Helper: for `0 < R < R'`, eventually `2 * ⌈exp(n R)⌉ ≤ ⌈exp(n R')⌉`. -/
lemma exists_N_two_ceil_exp_le
    {R R' : ℝ} (hR_pos : 0 < R) (hRR' : R < R') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * Nat.ceil (Real.exp ((n : ℝ) * R))
        ≤ Nat.ceil (Real.exp ((n : ℝ) * R')) := by
  -- We show eventually `2 * exp(n R) + 2 ≤ exp(n R')`. Then
  -- `2 * ⌈exp(n R)⌉₊ ≤ 2 * (exp(n R) + 1) = 2 * exp(n R) + 2 ≤ exp(n R') ≤ ⌈exp(n R')⌉₊`.
  have h_delta_pos : 0 < R' - R := by linarith
  -- `exp(n R) → ∞` (since R > 0).
  have h_exp_R_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * R)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_nat_mul_atTop hR_pos)
  -- `exp(n (R' - R)) → ∞`.
  have h_exp_delta_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * (R' - R))) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_nat_mul_atTop h_delta_pos)
  -- `exp(n R) * (exp(n (R'-R)) - 2) - 2 → ∞`.
  -- We bound `exp(n (R'-R)) - 2 ≥ 1` eventually, and `exp(n R) → ∞`, so the product → ∞;
  -- subtracting 2 keeps it tending to ∞.
  -- Eventually `exp(n (R'-R)) ≥ 3`.
  have h_ev_delta_3 : ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ Real.exp ((n : ℝ) * (R' - R)) :=
    h_exp_delta_tendsto.eventually_ge_atTop 3
  -- And `exp(n R) → ∞`, so eventually `exp(n R) ≥ b + 2` for any `b`.
  -- We use that `exp(n R) * 1 ≤ exp(n R) * (exp(n (R'-R)) - 2)` once
  -- `exp(n (R'-R)) ≥ 3`, i.e., `exp(n (R'-R)) - 2 ≥ 1`.
  -- So `exp(n R) ≤ exp(n R) * (exp(n (R'-R)) - 2) = exp(n R') - 2 * exp(n R)`.
  -- Hence `2 * exp(n R) + 2 ≤ exp(n R') + 2 - exp(n R)`. Hmm that's not tight enough.
  -- Try: `exp(n R') ≥ 3 * exp(n R)`, so `exp(n R') - 2 * exp(n R) ≥ exp(n R)`.
  -- Then `2 * exp(n R) + 2 ≤ exp(n R')` iff `2 ≤ exp(n R') - 2 * exp(n R)` iff `2 ≤ exp(n R)`.
  -- So we need `exp(n R) ≥ 2` AND `exp(n (R'-R)) ≥ 3`. Both hold eventually.
  have h_ev_exp_R_2 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.exp ((n : ℝ) * R) :=
    h_exp_R_tendsto.eventually_ge_atTop 2
  rw [Filter.eventually_atTop] at h_ev_delta_3 h_ev_exp_R_2
  obtain ⟨N₁, hN₁⟩ := h_ev_delta_3
  obtain ⟨N₂, hN₂⟩ := h_ev_exp_R_2
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : N₂ ≤ n := (le_max_right _ _).trans hn
  have h_delta_ge : (3 : ℝ) ≤ Real.exp ((n : ℝ) * (R' - R)) := hN₁ n hn1
  have h_exp_R_ge : (2 : ℝ) ≤ Real.exp ((n : ℝ) * R) := hN₂ n hn2
  -- `exp(n R) * 3 ≤ exp(n R) * exp(n (R'-R)) = exp(n R')`.
  have h_exp_R_nn : 0 ≤ Real.exp ((n : ℝ) * R) := (Real.exp_pos _).le
  have h_expR'_eq : Real.exp ((n : ℝ) * R')
      = Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (R' - R)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_3R_le_R' : 3 * Real.exp ((n : ℝ) * R) ≤ Real.exp ((n : ℝ) * R') := by
    rw [h_expR'_eq, mul_comm (Real.exp ((n : ℝ) * R))]
    exact mul_le_mul_of_nonneg_right h_delta_ge h_exp_R_nn
  -- So `2 * exp(n R) + 2 ≤ 3 * exp(n R) ≤ exp(n R')` (using `exp(n R) ≥ 2`).
  have h_target_real : 2 * Real.exp ((n : ℝ) * R) + 2 ≤ Real.exp ((n : ℝ) * R') := by
    have : 2 * Real.exp ((n : ℝ) * R) + 2 ≤ 3 * Real.exp ((n : ℝ) * R) := by linarith
    linarith
  -- Now convert to `Nat.ceil` form.
  have h_lhs_real : ((2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℕ) : ℝ)
      ≤ 2 * Real.exp ((n : ℝ) * R) + 2 := by
    have h_ceil_lt : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) < Real.exp ((n : ℝ) * R) + 1 :=
      Nat.ceil_lt_add_one h_exp_R_nn
    push_cast
    linarith
  have h_rhs_real : Real.exp ((n : ℝ) * R')
      ≤ ((Nat.ceil (Real.exp ((n : ℝ) * R')) : ℕ) : ℝ) := Nat.le_ceil _
  have h_combined : ((2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℕ) : ℝ)
      ≤ ((Nat.ceil (Real.exp ((n : ℝ) * R')) : ℕ) : ℝ) :=
    h_lhs_real.trans (h_target_real.trans h_rhs_real)
  exact_mod_cast h_combined

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
lemma exists_subcode_maxError_lt_two_mul
    {n M' : ℕ} (c : Code M' n α β) (W' : Channel α β) [IsMarkovKernel W']
    {R R' ε' : ℝ} (hR_pos : 0 < R)
    (hM'_lb : Nat.ceil (Real.exp ((n : ℝ) * R')) ≤ M')
    (hrate : 2 * Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ Nat.ceil (Real.exp ((n : ℝ) * R')))
    (h_avg_lt : (c.averageErrorProb W').toReal < ε') :
    ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (cs : Code M n α β),
      ∀ m, (cs.errorProbAt W' m).toReal < 2 * ε' := by
  classical
  have hK : (1 : ℝ) < 2 := by norm_num
  have h_filter_bound := errorProbAt_filter_card_bound (M := M') (n := n) c W' hK
  set T : Finset (Fin M') := (Finset.univ : Finset (Fin M')).filter
      (fun m ↦ 2 * (c.averageErrorProb W').toReal <
        (c.errorProbAt W' m).toReal) with hT_def
  set S : Finset (Fin M') := (Finset.univ : Finset (Fin M')).filter
      (fun m ↦ (c.errorProbAt W' m).toReal ≤
        2 * (c.averageErrorProb W').toReal) with hS_def
  have hST_partition : S.card + T.card = M' := by
    have h_union : S ∪ T = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro m
      rw [Finset.mem_union, hS_def, hT_def, Finset.mem_filter, Finset.mem_filter]
      rcases le_or_gt ((c.errorProbAt W' m).toReal)
          (2 * (c.averageErrorProb W').toReal) with h | h
      · exact Or.inl ⟨Finset.mem_univ m, h⟩
      · exact Or.inr ⟨Finset.mem_univ m, h⟩
    have h_disj : Disjoint S T := by
      rw [hS_def, hT_def]
      refine Finset.disjoint_filter.mpr ?_
      intro m _ hm
      exact not_lt_of_ge hm
    have := Finset.card_union_of_disjoint h_disj
    rw [h_union, Finset.card_univ, Fintype.card_fin] at this
    linarith
  have h_T_card_le : 2 * T.card ≤ M' := by
    have h_real : ((T.card : ℝ) * 2 : ℝ) ≤ (M' : ℝ) := h_filter_bound
    have h_real' : ((2 * T.card : ℕ) : ℝ) ≤ ((M' : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h_real'
  have h_2S_ge_M : M' ≤ 2 * S.card := by
    have : M' = S.card + T.card := hST_partition.symm
    omega
  have h_rate_inequality : 2 * Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ 2 * S.card :=
    hrate.trans (hM'_lb.trans h_2S_ge_M)
  have h_ceil_le_S_card : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ S.card := by
    have h2 : (2 : ℕ) > 0 := by norm_num
    exact Nat.le_of_mul_le_mul_left h_rate_inequality h2
  have h_exp_nR_pos : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR_pos.le
  have h_ceil_ge_1 : 1 ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
    exact lt_of_lt_of_le zero_lt_one (Real.one_le_exp h_exp_nR_pos)
  have hS_pos : 0 < S.card := lt_of_lt_of_le h_ceil_ge_1 h_ceil_le_S_card
  refine ⟨S.card, h_ceil_le_S_card, c.subcode S hS_pos, ?_⟩
  intro m'
  have h_sub_le := c.subcode_errorProbAt_le W' S hS_pos m'
  set m₀ : Fin M' := (S.equivFin.symm ⟨m'.val, by simp [Fin.is_lt]⟩).val with hm₀_def
  have hm₀_mem : m₀ ∈ S := (S.equivFin.symm ⟨m'.val, by simp [Fin.is_lt]⟩).property
  have h_m₀_le : (c.errorProbAt W' m₀).toReal ≤
      2 * (c.averageErrorProb W').toReal := by
    rw [hS_def, Finset.mem_filter] at hm₀_mem
    exact hm₀_mem.2
  have h_sub_le_top : c.errorProbAt W' m₀ ≠ ∞ := by
    haveI : IsProbabilityMeasure
        (Measure.pi (fun i ↦ W' (c.encoder m₀ i))) := by infer_instance
    exact ((prob_le_one
      (μ := Measure.pi (fun i ↦ W' (c.encoder m₀ i)))
      (s := c.errorEvent m₀)).trans_lt ENNReal.one_lt_top).ne
  have h_sub_le_toReal :
      ((c.subcode S hS_pos).errorProbAt W' m').toReal
        ≤ (c.errorProbAt W' m₀).toReal :=
    (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top h_sub_le_top h_sub_le) h_sub_le_top).mpr h_sub_le
  calc ((c.subcode S hS_pos).errorProbAt W' m').toReal
      ≤ (c.errorProbAt W' m₀).toReal := h_sub_le_toReal
    _ ≤ 2 * (c.averageErrorProb W').toReal := h_m₀_le
    _ < 2 * ε' := by linarith

omit [DecidableEq α] [DecidableEq β] in
/-- **Expurgation**: average error achievability implies max error achievability. -/
@[entry_point]
theorem channel_coding_achievability_max_error
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  classical
  -- Step 1: rate slack. Define `R' := (R + I)/2` so `R < R' < I`.
  set I : ℝ := (mutualInfoOfChannel p W).toReal with hI_def
  set R' : ℝ := (R + I) / 2 with hR'_def
  have hI_pos : 0 < I := lt_trans hR_pos hR
  have hR_lt_R' : R < R' := by rw [hR'_def]; linarith
  have hR'_lt_I : R' < I := by rw [hR'_def]; linarith
  have hR'_pos : 0 < R' := lt_trans hR_pos hR_lt_R'
  -- Step 2: smaller error target. `ε' := ε/4`.
  set ε' : ℝ := ε / 4 with hε'_def
  have hε'_pos : 0 < ε' := by rw [hε'_def]; linarith
  -- Step 3: apply existing average-error achievability.
  obtain ⟨N₀, hN₀⟩ := channel_coding_achievability W p hp_pos hW_pos hR'_pos hR'_lt_I hε'_pos
  -- Step 4: rate-asymptotic claim.
  obtain ⟨N_rate, hN_rate⟩ := exists_N_two_ceil_exp_le hR_pos hR_lt_R'
  -- Final N.
  refine ⟨max N₀ N_rate, ?_⟩
  intro n hn
  have hn0 : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : N_rate ≤ n := (le_max_right _ _).trans hn
  obtain ⟨M, hM_lb, c, h_avg_lt⟩ := hN₀ n hn0
  -- Expurgation (subcode trick): from `M ≥ ⌈exp(n R')⌉` with `2 ⌈exp(n R)⌉ ≤ ⌈exp(n R')⌉`
  -- and avg error `< ε'`, pick the good half to get max-error `< 2 ε' = ε/2 < ε`.
  obtain ⟨M₂, hM₂_lb, cs, h_max_lt⟩ :=
    exists_subcode_maxError_lt_two_mul c W hR_pos hM_lb (hN_rate n hn1) h_avg_lt
  refine ⟨M₂, hM₂_lb, cs, fun m' ↦ ?_⟩
  calc (cs.errorProbAt W m').toReal
      < 2 * ε' := h_max_lt m'
    _ = ε / 2 := by rw [hε'_def]; ring
    _ < ε := by linarith

/-! ## Full-support assumption removal

MI is invariant under restriction to the support `{a | 0 < p.real {a}}` via `klDiv`
invariance under `MeasurableEmbedding`-pushforward. -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- For a `MeasurableEmbedding f`, AC of pushforwards is equivalent to AC of the originals.
This is the contrapositive of `MeasurableEmbedding.absolutelyContinuous_map` together with
that lemma itself. -/
private lemma absolutelyContinuous_map_iff_of_measurableEmbedding
    {α' β' : Type*} {_ : MeasurableSpace α'} {_ : MeasurableSpace β'} {f : α' → β'}
    (hf : MeasurableEmbedding f) (μ ν : Measure α') :
    μ.map f ≪ ν.map f ↔ μ ≪ ν := by
  refine ⟨fun h s hνs ↦ ?_, fun h ↦ hf.absolutelyContinuous_map h⟩
  -- `μ s = (μ.map f) (f '' s)` by `hf.map_apply` + injectivity of `f`.
  have hν_image : ν.map f (f '' s) = 0 := by
    rw [hf.map_apply, hf.injective.preimage_image]; exact hνs
  have hμ_image : μ.map f (f '' s) = 0 := h hν_image
  rwa [hf.map_apply, hf.injective.preimage_image] at hμ_image

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- **`klDiv` is invariant under `MeasurableEmbedding`-pushforward** of both arguments
(finite-measure side). Proof: split on `μ ≪ ν`; in the AC case use the lintegral form
`klDiv_eq_lintegral_klFun_of_ac` + `MeasurableEmbedding.rnDeriv_map` +
`MeasurableEmbedding.lintegral_map`; in the not-AC case both sides are `∞`. -/
private lemma klDiv_map_measurableEmbedding
    {α' β' : Type*} {_ : MeasurableSpace α'} {_ : MeasurableSpace β'} {f : α' → β'}
    (hf : MeasurableEmbedding f) (μ ν : Measure α')
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  by_cases hac : μ ≪ ν
  · have hac' : μ.map f ≪ ν.map f := hf.absolutelyContinuous_map hac
    rw [klDiv_eq_lintegral_klFun_of_ac hac, klDiv_eq_lintegral_klFun_of_ac hac']
    -- Rewrite the LHS via lintegral_map for measurable embedding.
    rw [hf.lintegral_map (fun y ↦ ENNReal.ofReal
      (InformationTheory.klFun ((μ.map f).rnDeriv (ν.map f) y).toReal))]
    -- Now compare ∫⁻ x, klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal ∂ν
    -- vs ∫⁻ x, klFun ((μ.rnDeriv ν) x).toReal ∂ν.
    refine lintegral_congr_ae ?_
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · have hac_map_iff := absolutelyContinuous_map_iff_of_measurableEmbedding hf μ ν
    have hac' : ¬ (μ.map f ≪ ν.map f) := fun h ↦ hac (hac_map_iff.mp h)
    rw [klDiv_of_not_ac hac, klDiv_of_not_ac hac']

omit [DecidableEq α] [Nonempty α] in
/-- The support set `{a : α | 0 < p.real {a}}` is measurable (singletons are measurable). -/
private lemma measurableSet_support (p : Measure α) :
    MeasurableSet {a : α | 0 < p.real {a}} := by
  -- In `MeasurableSingletonClass α`, every set is measurable... actually it requires `Countable α`
  -- but we have `Fintype α`. Use `Set.Finite.measurableSet`.
  exact (Set.toFinite _).measurableSet

omit [DecidableEq α] [Nonempty α] in
/-- `Subtype.val : {a // 0 < p.real {a}} → α` is a `MeasurableEmbedding`. -/
private lemma measurableEmbedding_subtype_support (p : Measure α) :
    MeasurableEmbedding (Subtype.val : {a : α // 0 < p.real {a}} → α) :=
  MeasurableEmbedding.subtype_coe (measurableSet_support p)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `range Subtype.val = {a | 0 < p.real {a}}`. -/
private lemma range_subtype_val_support (p : Measure α) :
    Set.range (Subtype.val : {a : α // 0 < p.real {a}} → α)
      = {a : α | 0 < p.real {a}} := Subtype.range_val

omit [DecidableEq α] [Nonempty α] in
/-- `p` is null outside its support `{a | 0 < p.real {a}}`. -/
private lemma measure_compl_support_eq_zero (p : Measure α) [IsFiniteMeasure p] :
    p ({a : α | 0 < p.real {a}}ᶜ) = 0 := by
  -- The complement is finite (subset of `Fintype α`); rewrite as a finite union of singletons.
  have hcompl_eq : ({a : α | 0 < p.real {a}}ᶜ : Set α) = ⋃ a ∈ (Finset.univ.filter
      (fun a ↦ ¬ 0 < p.real {a})), ({a} : Set α) := by
    ext x
    simp [Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [hcompl_eq, measure_biUnion_finset (fun a _ b _ hab ↦ by
        simpa [Function.onFun, Set.disjoint_singleton] using hab)
      (fun a _ ↦ MeasurableSet.singleton a)]
  refine Finset.sum_eq_zero (fun a ha ↦ ?_)
  -- `a` is in the filter, so `¬ 0 < p.real {a}`.
  have hnot : ¬ 0 < p.real {a} := (Finset.mem_filter.mp ha).2
  -- Hence `p.real {a} = 0`.
  have hreal : p.real {a} = 0 :=
    le_antisymm (not_lt.mp hnot) measureReal_nonneg
  -- Translate `p.real {a} = 0` to `p {a} = 0` (since `p {a} ≠ ∞`).
  have hne_top : p {a} ≠ ∞ := measure_ne_top p _
  have htoReal : (p {a}).toReal = 0 := hreal
  rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal with h | h
  · exact h
  · exact (hne_top h).elim

omit [DecidableEq α] [Nonempty α] in
/-- The pushforward of `p.comap Subtype.val` back along `Subtype.val` recovers `p`,
because `p` is concentrated on its support. -/
private lemma map_comap_subtype_support_eq_self
    (p : Measure α) [IsFiniteMeasure p] :
    (p.comap (Subtype.val : {a : α // 0 < p.real {a}} → α)).map Subtype.val = p := by
  rw [(measurableEmbedding_subtype_support p).map_comap, range_subtype_val_support]
  -- `p.restrict S = p` because `p` is concentrated on `S = {a | 0 < p.real {a}}`.
  refine Measure.restrict_eq_self_of_ae_mem ?_
  -- `∀ᵐ a ∂p, a ∈ S` iff `p Sᶜ = 0`.
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{a : α | 0 < p.real {a}}, ?_, fun a ha ↦ ha⟩
  rw [mem_ae_iff]
  -- `{a | a ∈ S}ᶜ = Sᶜ`.
  exact measure_compl_support_eq_zero p

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
@[entry_point]
theorem mutualInfoOfChannel_restrict_to_support
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    mutualInfoOfChannel p W
      = mutualInfoOfChannel
          (p.comap (Subtype.val : {a : α // 0 < p.real {a}} → α))
          (W.comap (Subtype.val : {a : α // 0 < p.real {a}} → α)
            (Measurable.subtype_val measurable_id)) := by
  -- Set up notation: j is the subtype inclusion, an `MeasurableEmbedding`.
  set j : {a : α // 0 < p.real {a}} → α := Subtype.val with hj_def
  have hj_meas : Measurable j := Measurable.subtype_val measurable_id
  have hj_emb : MeasurableEmbedding j := measurableEmbedding_subtype_support p
  set p_supp : Measure {a : α // 0 < p.real {a}} := p.comap j with hp_supp_def
  set W_supp : Channel {a : α // 0 < p.real {a}} β := W.comap j hj_meas with hW_supp_def
  -- `p_supp` is a probability measure.
  haveI : IsProbabilityMeasure p_supp := by
    refine hj_emb.isProbabilityMeasure_comap ?_
    -- ∀ᵐ a ∂p, a ∈ range j; range j = support.
    rw [MeasureTheory.ae_iff, ← Set.compl_setOf]
    show p (({a : α | a ∈ Set.range j})ᶜ) = 0
    rw [show ({a : α | a ∈ Set.range j} : Set α) = Set.range j from rfl,
      range_subtype_val_support]
    exact measure_compl_support_eq_zero p
  -- `W_supp` is a Markov kernel (Mathlib instance).
  haveI : IsMarkovKernel W_supp := Kernel.IsMarkovKernel.comap W hj_meas
  -- ===== Step 1: Joint pushforward = original joint. =====
  -- `(p_supp ⊗ₘ W_supp).map (Prod.map j id) = p ⊗ₘ W`
  have h_joint_map : (p_supp ⊗ₘ W_supp).map (Prod.map j (id : β → β)) = p ⊗ₘ W := by
    refine Measure.ext fun T hT ↦ ?_
    have h_emb_map : MeasurableEmbedding (Prod.map j (id : β → β)) :=
      hj_emb.prodMap MeasurableEmbedding.id
    rw [h_emb_map.map_apply, Measure.compProd_apply hT,
      Measure.compProd_apply (h_emb_map.measurable hT)]
    -- LHS: ∫⁻ a' ∂p_supp, W_supp a' (Prod.mk a' ⁻¹' (Prod.map j id ⁻¹' T))
    -- RHS: ∫⁻ a ∂p, W a (Prod.mk a ⁻¹' T)
    -- W_supp a' = W (j a') by Kernel.comap_apply.
    have h_pre (a' : {a : α // 0 < p.real {a}}) :
        W_supp a' (Prod.mk a' ⁻¹' (Prod.map j (id : β → β) ⁻¹' T))
          = W (j a') (Prod.mk (j a') ⁻¹' T) := by
      rw [show W_supp = W.comap j hj_meas from rfl, Kernel.comap_apply]
      -- Prod.mk a' ⁻¹' (Prod.map j id ⁻¹' T) = Prod.mk (j a') ⁻¹' T as sets.
      have h_set :
          Prod.mk a' ⁻¹' (Prod.map j (id : β → β) ⁻¹' T) = Prod.mk (j a') ⁻¹' T := by
        ext b; simp [Prod.map_apply]
      rw [h_set]
    simp_rw [h_pre]
    -- Now convert ∫⁻ a' ∂p_supp to ∫⁻ a ∂p via map_comap_subtype_support_eq_self.
    -- p_supp = p.comap j by definition; (p.comap j).map j = p.
    have h_map_back : (p.comap j).map j = p := map_comap_subtype_support_eq_self p
    calc ∫⁻ a' : {a : α // 0 < p.real {a}}, W (j a') (Prod.mk (j a') ⁻¹' T) ∂p_supp
        = ∫⁻ a' : {a : α // 0 < p.real {a}}, W (j a') (Prod.mk (j a') ⁻¹' T) ∂(p.comap j) := by
            rw [hp_supp_def]
      _ = ∫⁻ a, W a (Prod.mk a ⁻¹' T) ∂((p.comap j).map j) := by
            rw [hj_emb.lintegral_map]
      _ = ∫⁻ a, W a (Prod.mk a ⁻¹' T) ∂p := by rw [h_map_back]
  -- ===== Step 2: Output distribution is invariant. =====
  -- outputDistribution p_supp W_supp = outputDistribution p W
  have h_output_eq : outputDistribution p_supp W_supp = outputDistribution p W := by
    unfold outputDistribution jointDistribution
    rw [← h_joint_map, Measure.snd, Measure.snd,
      Measure.map_map measurable_snd (hj_emb.measurable.prodMap measurable_id)]
    -- Prod.snd ∘ Prod.map j id = Prod.snd (after eta).
    rfl
  -- ===== Step 3: Product pushforward = original product. =====
  -- (p_supp.prod (outputDistribution p_supp W_supp)).map (Prod.map j id) = p.prod q
  have h_prod_map : (p_supp.prod (outputDistribution p_supp W_supp)).map
        (Prod.map j (id : β → β))
      = p.prod (outputDistribution p W) := by
    rw [h_output_eq]
    -- Use Measure.map_prod_map with f := j, g := id.
    rw [← Measure.map_prod_map (μa := p_supp) (μc := outputDistribution p W)
      hj_meas measurable_id]
    rw [map_comap_subtype_support_eq_self, Measure.map_id]
  -- ===== Step 4: Apply `klDiv` invariance. =====
  show klDiv (jointDistribution p W) (p.prod (outputDistribution p W))
    = klDiv (jointDistribution p_supp W_supp)
        (p_supp.prod (outputDistribution p_supp W_supp))
  unfold jointDistribution
  rw [← h_joint_map, ← h_prod_map]
  exact klDiv_map_measurableEmbedding (hj_emb.prodMap MeasurableEmbedding.id) _ _

/-- **Lift a code** from the support subtype to the full alphabet by composing the encoder
with `Subtype.val`. -/
@[entry_point]
noncomputable def Code_lift_from_subtype
    {M n : ℕ} (p : Measure α)
    (c : Code M n {a : α // 0 < p.real {a}} β) : Code M n α β :=
  { encoder := fun m i ↦ (c.encoder m i).val
    decoder := c.decoder }

/-! ## Main theorem -/

/-- Uniform input distribution `unif a := 1/|α|`, used as a smoothing target. -/
noncomputable def uniformInput (α : Type*) [Fintype α] : α → ℝ :=
  fun _ ↦ (Fintype.card α : ℝ)⁻¹
omit [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- `uniformInput α ∈ stdSimplex ℝ α`. -/
lemma uniformInput_mem_stdSimplex : uniformInput α ∈ stdSimplex ℝ α := by
  unfold uniformInput
  refine ⟨fun _ ↦ ?_, ?_⟩
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpos : (0 : ℝ) < Fintype.card α := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card α)
    exact mul_inv_cancel₀ hpos.ne'

omit [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- `uniformInput α a > 0` for any `a`. -/
lemma uniformInput_pos (a : α) : 0 < uniformInput α a := by
  unfold uniformInput
  refine inv_pos.mpr ?_
  exact_mod_cast Fintype.card_pos_iff.mpr inferInstance

/-- Smoothed input `pSmooth p₀ δ := (1-δ) • p₀ + δ • uniformInput`. -/
noncomputable def pSmooth (p₀ : α → ℝ) (δ : ℝ) : α → ℝ :=
  fun a ↦ (1 - δ) * p₀ a + δ * uniformInput α a

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- `pSmooth p₀ 0 = p₀`. -/
lemma pSmooth_zero (p₀ : α → ℝ) : pSmooth p₀ 0 = p₀ := by
  unfold pSmooth
  funext a
  ring

omit [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- For `δ ∈ [0,1]` and `p₀ ∈ stdSimplex`, `pSmooth p₀ δ ∈ stdSimplex`. -/
lemma pSmooth_mem_stdSimplex {p₀ : α → ℝ} (hp₀ : p₀ ∈ stdSimplex ℝ α)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : pSmooth p₀ δ ∈ stdSimplex ℝ α := by
  have h := convex_stdSimplex (𝕜 := ℝ) (ι := α) hp₀ uniformInput_mem_stdSimplex
    (a := 1 - δ) (b := δ) (by linarith) hδ0 (by ring)
  -- h : (1-δ) • p₀ + δ • uniformInput ∈ stdSimplex
  have h_eq : pSmooth p₀ δ = (1 - δ) • p₀ + δ • uniformInput α := by
    funext a
    simp [pSmooth, smul_eq_mul]
  rw [h_eq]
  exact h

omit [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- For `δ ∈ (0,1]` and `p₀ ∈ stdSimplex`, each entry `(pSmooth p₀ δ) a > 0`. -/
lemma pSmooth_pos {p₀ : α → ℝ} (hp₀ : p₀ ∈ stdSimplex ℝ α)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1) (a : α) : 0 < pSmooth p₀ δ a := by
  unfold pSmooth
  have h1 : 0 ≤ (1 - δ) * p₀ a := mul_nonneg (by linarith) (hp₀.1 a)
  have h2 : 0 < δ * uniformInput α a := mul_pos hδ_pos (uniformInput_pos a)
  linarith

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `δ ↦ pSmooth p₀ δ` is continuous (as a curve into `α → ℝ` with product topology). -/
lemma continuous_pSmooth (p₀ : α → ℝ) : Continuous (fun δ : ℝ ↦ pSmooth p₀ δ) := by
  refine continuous_pi (fun a ↦ ?_)
  unfold pSmooth
  exact (continuous_const.sub continuous_id).mul continuous_const
    |>.add (continuous_id.mul continuous_const)

omit [DecidableEq α] [DecidableEq β] in
/-- **Shannon noisy channel coding theorem** (Cover-Thomas 7.7.1): for any `R < capacity W`
and `ε > 0`, there exists `N` such that for all `n ≥ N` there is a code of size `≥ exp(n R)`
achieving max error probability `< ε`.

Proof: extract `p₀` with `R < I(p₀; W)`, smooth to `pSmooth p₀ δ₀` to get full support,
then apply the expurgation wrapper `channel_coding_achievability_max_error`. -/
@[entry_point]
theorem shannon_noisy_channel_coding_theorem
    (W : Channel α β) [IsMarkovKernel W]
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  classical
  -- Step 1: extract `p₀ ∈ stdSimplex` with `R < I(p₀; W)`.
  obtain ⟨p₀, hp₀_mem, hp₀_lt⟩ := capacity_lt_implies_exists_pmf W hR
  set I₀ : ℝ := (mutualInfoOfChannel (pmfToMeasure p₀) W).toReal with hI₀_def
  -- Step 2: midpoint rate R₀ := (R + I₀)/2.
  set R₀ : ℝ := (R + I₀) / 2 with hR₀_def
  have hR_lt_R₀ : R < R₀ := by rw [hR₀_def]; linarith
  have hR₀_lt_I₀ : R₀ < I₀ := by rw [hR₀_def]; linarith
  have hR₀_pos : 0 < R₀ := lt_trans hR_pos hR_lt_R₀
  -- Step 3: continuity of `δ ↦ I(pSmooth p₀ δ; W).toReal` at δ = 0.
  have hI_cont_on := continuous_mutualInfoOfChannel_left W
  -- Restrict to the path `δ ↦ pSmooth p₀ δ`.
  have h_path : ∀ δ ∈ Set.Icc (0 : ℝ) 1, pSmooth p₀ δ ∈ stdSimplex ℝ α :=
    fun δ hδ ↦ pSmooth_mem_stdSimplex hp₀_mem hδ.1 hδ.2
  have h_pSmooth_zero_eq : pSmooth p₀ 0 = p₀ := pSmooth_zero p₀
  have h_at_zero_in : pSmooth p₀ 0 ∈ stdSimplex ℝ α := by
    rw [h_pSmooth_zero_eq]; exact hp₀_mem
  -- Compose: `δ ↦ pSmooth p₀ δ` continuous + ContinuousOn of `I(·; W).toReal`.
  have h_curve_cont : Continuous (fun δ : ℝ ↦ pSmooth p₀ δ) := continuous_pSmooth p₀
  -- `f δ := I(pmfToMeasure (pSmooth p₀ δ); W).toReal` is continuous on `[0,1]`.
  set f : ℝ → ℝ := fun δ ↦ (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ)) W).toReal with hf_def
  have hf_cont_on : ContinuousOn f (Set.Icc 0 1) := by
    have h_maps : Set.MapsTo (fun δ : ℝ ↦ pSmooth p₀ δ) (Set.Icc 0 1) (stdSimplex ℝ α) :=
      fun δ hδ ↦ h_path δ hδ
    exact hI_cont_on.comp h_curve_cont.continuousOn h_maps
  -- f 0 = I₀, so f 0 > R₀.
  have hf_zero : f 0 = I₀ := by
    simp [hf_def, h_pSmooth_zero_eq, hI₀_def]
  have hf_zero_gt : R₀ < f 0 := by rw [hf_zero]; exact hR₀_lt_I₀
  -- Step 4: pick small δ₀ > 0 with `R₀ < f δ₀`.
  -- Continuity ⟹ ∃ open nbhd of 0 in [0,1] with f > R₀ on it.
  have h_at_zero : ContinuousWithinAt f (Set.Icc 0 1) 0 := by
    refine hf_cont_on 0 ⟨le_refl _, by norm_num⟩
  -- Use `eventually_lt` form: there exists ε_δ > 0 such that for all δ ∈ [0, ε_δ) ∩ [0,1],
  -- f δ > R₀.
  have h_ev_gt : ∀ᶠ δ in (nhdsWithin (0 : ℝ) (Set.Icc 0 1)), R₀ < f δ := by
    have := h_at_zero.tendsto
    exact this.eventually_const_lt hf_zero_gt
  -- Convert to existence of δ₀ > 0 in [0,1] with f δ₀ > R₀.
  have h_ev_gt_mem : {δ | R₀ < f δ} ∈ 𝓝[Set.Icc (0 : ℝ) 1] 0 := h_ev_gt
  rw [Metric.mem_nhdsWithin_iff] at h_ev_gt_mem
  obtain ⟨η, hη_pos, h_η⟩ := h_ev_gt_mem
  set δ₀ : ℝ := min (η / 2) 1 with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]; exact lt_min (by linarith) (by norm_num)
  have hδ₀_le_1 : δ₀ ≤ 1 := min_le_right _ _
  have hδ₀_lt_η : δ₀ < η := by
    rw [hδ₀_def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ₀_mem_Icc : δ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ₀_pos.le, hδ₀_le_1⟩
  have hδ₀_mem_ball : δ₀ ∈ Metric.ball (0 : ℝ) η := by
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hδ₀_pos]
    exact hδ₀_lt_η
  have hf_δ₀ : R₀ < f δ₀ := h_η ⟨hδ₀_mem_ball, hδ₀_mem_Icc⟩
  -- Step 5: pSmooth p₀ δ₀ has full support.
  have h_pδ₀_mem : pSmooth p₀ δ₀ ∈ stdSimplex ℝ α :=
    pSmooth_mem_stdSimplex hp₀_mem hδ₀_pos.le hδ₀_le_1
  have h_pδ₀_pos : ∀ a, 0 < pSmooth p₀ δ₀ a :=
    fun a ↦ pSmooth_pos hp₀_mem hδ₀_pos hδ₀_le_1 a
  -- Convert to (pmfToMeasure (pSmooth p₀ δ₀)).real {a} > 0.
  haveI hpmf_pm : IsProbabilityMeasure (pmfToMeasure (pSmooth p₀ δ₀)) :=
    pmfToMeasure_isProbabilityMeasure h_pδ₀_mem
  have hp_pos_meas : ∀ a, 0 < (pmfToMeasure (pSmooth p₀ δ₀)).real {a} := by
    intro a
    rw [pmfToMeasure_real_singleton h_pδ₀_mem]
    exact h_pδ₀_pos a
  -- Step 6: rate condition R < f δ₀ (note: hf_δ₀ gives R₀ < f δ₀, and R < R₀).
  have hR_lt_f_δ₀ : R < f δ₀ := lt_trans hR_lt_R₀ hf_δ₀
  -- Step 7: apply B.4.
  exact channel_coding_achievability_max_error W (pmfToMeasure (pSmooth p₀ δ₀))
    hp_pos_meas hW_pos hR_pos hR_lt_f_δ₀ hε

end InformationTheory.Shannon.ChannelCoding
