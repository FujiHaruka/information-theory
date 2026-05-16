import Common2026.Shannon.RateDistortionAchievabilityPhaseB
import Common2026.Shannon.StrongTypicality
import Common2026.Shannon.IIDProductInputJoint

/-!
# Rate-distortion achievability — Phase E (strong-typicality variant), Phases α–γ

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)

This file develops the **joint strongly-typical** apparatus that is used in the
strong-typicality variant of the rate-distortion achievability theorem (E-3''').
The construction reuses the single-axis strong typicality machinery from
`StrongTypicality.lean` instantiated on the product alphabet `α × β`, with the
joint sequence `jointSequence Xs Ys i ω = (Xs i ω, Ys i ω)`.

## Phases scope

This commit covers **Phases α–γ**:

* **Phase α** — `jointStronglyTypicalSet` definition and basic structure lemmas
  (membership-iff, measurability, finiteness, subset relation to
  `jointlyTypicalSet`).
* **Phase β** — joint strong-typicality probability tends to one
  (direct corollary of `stronglyTypicalSet_prob_tendsto_one` applied to the
  joint sequence over `α × β`).
* **Phase γ** — distortion bridge: for any pair `(x, y)` strongly jointly
  typical at level `ε`, the empirical block distortion is `ε · D_max`-close
  to the pmf-form expected distortion, hence inside `distortionTypicalSet`
  for an appropriate `δ`.

Phases δ–η (witness-form achievability, random-coding entropy bound,
δ → 0 limit) will follow in subsequent commits.

## Design notes

* The joint sequence i.i.d. infrastructure (`iidAmbientJoint_iIndepFun_joint`,
  `iidAmbientJoint_identDistrib_joint`) lives in `IIDProductInputJoint.lean`.
  We hypothesise the pair / ident-distrib of the joint sequence at the
  statement level to stay abstract.
* `expectedDistortionPmf d qStar` is the pmf-form expectation
  `∑_{a,b} qStar(a,b) · d(a,b)`. The strong-typicality bound says
  `|blockDistortion - expectedDistortionPmf d (pmf of joint at index 0)|
   ≤ ε · ∑_{a,b} d(a,b)`. When `expectedDistortionPmf d qStar ≤ D`, this
  gives the rate-distortion bound at `δ := ε · ∑_{a,b} d(a,b)` slack.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Filter
open InformationTheory.Shannon.ChannelCoding
  (jointSequence jointSequence_apply measurable_jointSequence jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-! ## Phase α — Joint strongly typical set -/

/-- **Joint strongly typical set** over the product alphabet `α × β`. A pair
`(x, y) : (Fin n → α) × (Fin n → β)` is in the set iff the "reshape"
`fun i => (x i, y i) : Fin n → α × β` lies in the single-axis strongly typical
set for the joint sequence `jointSequence Xs Ys`.

Concretely (unfolding `stronglyTypicalSet`):

  `(x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε ↔
    ∀ (a, b), |(typeCount (fun i => (x i, y i)) (a, b) : ℝ)/n -
                (μ.map (jointSequence Xs Ys 0)).real {(a, b)}| ≤ ε`. -/
noncomputable def jointStronglyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α) × (Fin n → β)) :=
  { p | (fun i => (p.1 i, p.2 i)) ∈
        stronglyTypicalSet μ (jointSequence Xs Ys) n ε }

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mem_jointStronglyTypicalSet_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x : Fin n → α) (y : Fin n → β) :
    (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε ↔
      (fun i => (x i, y i)) ∈
        stronglyTypicalSet μ (jointSequence Xs Ys) n ε := Iff.rfl

/-- The joint strongly typical set is measurable (finite ambient). -/
theorem measurableSet_jointStronglyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) :
    MeasurableSet (jointStronglyTypicalSet μ Xs Ys n ε) :=
  (Set.toFinite _).measurableSet

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- The joint strongly typical set is finite. -/
lemma jointStronglyTypicalSet_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) :
    (jointStronglyTypicalSet μ Xs Ys n ε).Finite := Set.toFinite _

/-- **Strong ⟹ weak joint typicality (joint axis only).** If
`(x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε` and `ε · logSumAbs ≤ ε'`,
then the joint condition of `jointlyTypicalSet` (third conjunct) holds.

NOTE: `jointlyTypicalSet` requires *all three* of X-, Y-, and joint-axis
typicality. The strongly-typical-joint axis implies the joint axis only;
to get full `jointlyTypicalSet` membership one additionally needs the X-axis
and Y-axis weak typicality, which can be derived from the joint strong
typicality via marginalisation but is deferred. The conclusion here is the
single joint-axis condition. -/
lemma jointStronglyTypicalSet_joint_axis_subset
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    {n : ℕ} (hn : 0 < n) {ε ε' : ℝ}
    (h_bound : ε * logSumAbs μ (jointSequence Xs Ys) < ε') :
    ∀ p ∈ jointStronglyTypicalSet μ Xs Ys n ε,
      (fun i => (p.1 i, p.2 i)) ∈
        typicalSet μ (jointSequence Xs Ys) n ε' := by
  intro p hp
  have hZ : ∀ i, Measurable (jointSequence Xs Ys i) := fun i =>
    measurable_jointSequence Xs Ys hXs hYs i
  exact stronglyTypicalSet_subset_typicalSet μ
    (jointSequence Xs Ys) hZ hn h_bound hp

/-! ## Phase β — Joint strong typicality probability tends to one -/

/-- **Joint strong typicality, AEP form.** For an i.i.d. joint sequence
`jointSequence Xs Ys` over the product alphabet `α × β`, the probability
that the block pair `(jointRV Xs n, jointRV Ys n)` lies in
`jointStronglyTypicalSet μ Xs Ys n ε` tends to `1`. -/
theorem jointStronglyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepZ : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i)
      (jointSequence Xs Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
                            jointStronglyTypicalSet μ Xs Ys n ε})
      atTop (𝓝 1) := by
  classical
  -- Apply stronglyTypicalSet_prob_tendsto_one to the joint sequence.
  have hZmeas : ∀ i, Measurable (jointSequence Xs Ys i) := fun i =>
    measurable_jointSequence Xs Ys hXs hYs i
  have h := stronglyTypicalSet_prob_tendsto_one μ (jointSequence Xs Ys)
    hZmeas hindepZ hidentZ hε
  -- h : Tendsto (fun n => μ {ω | jointRV (jointSequence Xs Ys) n ω
  --                              ∈ stronglyTypicalSet μ (jointSequence Xs Ys) n ε}) atTop (𝓝 1)
  -- Rewrite events to the (jointRV Xs n ω, jointRV Ys n ω) ∈ jointStronglyTypicalSet form.
  refine Tendsto.congr (fun n => ?_) h
  apply congrArg μ
  ext ω
  -- The two events coincide because
  --   jointRV (jointSequence Xs Ys) n ω i = (Xs i ω, Ys i ω) = (jointRV Xs n ω i, jointRV Ys n ω i).
  show jointRV (jointSequence Xs Ys) n ω ∈ stronglyTypicalSet μ (jointSequence Xs Ys) n ε
      ↔ (jointRV Xs n ω, jointRV Ys n ω) ∈ jointStronglyTypicalSet μ Xs Ys n ε
  rw [mem_jointStronglyTypicalSet_iff]
  -- Both sides are `(fun i => (Xs i ω, Ys i ω)) ∈ stronglyTypicalSet ...`.
  -- jointRV (jointSequence Xs Ys) n ω i = jointSequence Xs Ys i ω = (Xs i ω, Ys i ω)
  -- (fun i => (jointRV Xs n ω i, jointRV Ys n ω i)) i = (Xs i ω, Ys i ω)
  rfl

/-! ## Phase γ — Distortion bridge -/

/-- **Block distortion as a type-count sum.** For any pair `(x, y)`,
`blockDistortion d n x y = ∑_{a,b} (typeCount (fun i => (x i, y i)) (a, b) / n) · d(a, b)`.

This is the discrete change-of-variables identity: replace the sum over indices
`i : Fin n` by a sum over alphabet pairs `(a, b)` weighted by the empirical count
of that pair, using `Finset.sum_fiberwise_of_maps_to'`. -/
lemma blockDistortion_eq_typeCount_sum
    (d : DistortionFn α β) {n : ℕ} (x : Fin n → α) (y : Fin n → β) :
    blockDistortion d n x y
      = ∑ p : α × β,
          ((typeCount (fun i => (x i, y i)) p : ℝ) / n)
            * ((d p.1 p.2 : NNReal) : ℝ) := by
  classical
  unfold blockDistortion
  -- LHS = (1/n) · ∑ i : Fin n, d(x i, y i)
  -- RHS = ∑ p, (typeCount z p / n) · d(p.1, p.2) where z i = (x i, y i)
  set z : Fin n → α × β := fun i => (x i, y i) with hz_def
  set f : α × β → ℝ := fun p => ((d p.1 p.2 : NNReal) : ℝ) with hf_def
  -- Step 1: ∑ i, d(x i, y i) = ∑ i, f (z i)
  have h_eq1 : (∑ i : Fin n, ((d (x i) (y i) : NNReal) : ℝ)) = ∑ i : Fin n, f (z i) := rfl
  rw [h_eq1]
  -- Step 2: aggregate via fiberwise: ∑ i, f (z i) = ∑ p, (typeCount z p) · f p
  have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      z i ∈ (Finset.univ : Finset (α × β)) := fun i _ => Finset.mem_univ _
  have h_fiber := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (α × β))) h_maps f
  -- h_fiber : ∑ p ∈ univ, ∑ i ∈ univ.filter (z · = p), f p = ∑ i ∈ univ, f (z i)
  have h_agg : (∑ i : Fin n, f (z i))
      = ∑ p : α × β, (typeCount z p : ℝ) * f p := by
    rw [← h_fiber]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [h_agg]
  -- Step 3: (1/n) · ∑ p, (typeCount z p : ℝ) * f p = ∑ p, (typeCount z p / n) * f p
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **Distortion bridge.** Let `qStar := fun p => (μ.map (jointSequence Xs Ys 0)).real {p}`
(the law of the joint sequence at index 0). If `(x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε`,
then the empirical block distortion is `ε · (∑_{p} d(p))`-close to
`expectedDistortionPmf d qStar`:

  `|blockDistortion d n x y - expectedDistortionPmf d qStar| ≤ ε · ∑_{p} d(p.1, p.2)`. -/
theorem jointStronglyTypicalSet_implies_distortion_close
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) {n : ℕ} {ε : ℝ}
    (x : Fin n → α) (y : Fin n → β)
    (hxy : (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε) :
    |blockDistortion d n x y
        - expectedDistortionPmf d
            (fun p => (μ.map (jointSequence Xs Ys 0)).real {p})|
      ≤ ε * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) := by
  classical
  set qStar : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hqStar_def
  set z : Fin n → α × β := fun i => (x i, y i) with hz_def
  -- Rewrite both sides as sums over α × β.
  rw [blockDistortion_eq_typeCount_sum d x y]
  -- expectedDistortionPmf d qStar = ∑ a, ∑ b, qStar (a, b) · d(a, b)
  --                              = ∑ p : α × β, qStar p · d(p.1, p.2)
  have h_exp_eq : expectedDistortionPmf d qStar
      = ∑ p : α × β, qStar p * ((d p.1 p.2 : NNReal) : ℝ) := by
    unfold expectedDistortionPmf
    rw [← Finset.sum_product']
    rfl
  rw [h_exp_eq]
  -- Combine into a single sum:
  --   ∑ p, ((typeCount z p / n) - qStar p) · d(p.1, p.2)
  rw [← Finset.sum_sub_distrib]
  -- Apply abs ∑ ≤ ∑ abs, then bound each term by ε · |d(p)|.
  calc |∑ p : α × β,
          ((typeCount z p : ℝ) / n * ((d p.1 p.2 : NNReal) : ℝ)
            - qStar p * ((d p.1 p.2 : NNReal) : ℝ))|
      ≤ ∑ p : α × β,
          |(typeCount z p : ℝ) / n * ((d p.1 p.2 : NNReal) : ℝ)
            - qStar p * ((d p.1 p.2 : NNReal) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : α × β,
          |(typeCount z p : ℝ) / n - qStar p| * ((d p.1 p.2 : NNReal) : ℝ) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← sub_mul, abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
    _ ≤ ∑ p : α × β, ε * ((d p.1 p.2 : NNReal) : ℝ) := by
          refine Finset.sum_le_sum fun p _ => ?_
          -- |typeCount z p / n - qStar p| ≤ ε from hxy
          have h_strong : ∀ a : α × β,
              |(typeCount z a : ℝ) / n - qStar a| ≤ ε := by
            rw [mem_jointStronglyTypicalSet_iff] at hxy
            rw [mem_stronglyTypicalSet_iff] at hxy
            intro a
            exact hxy a
          exact mul_le_mul_of_nonneg_right (h_strong p) (NNReal.coe_nonneg _)
    _ = ε * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) := by
          rw [← Finset.mul_sum]

/-- **Strongly typical ⊆ distortion typical** (under appropriate slack).
If `(x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε` and the joint-distortion
expectation under `μ` equals the pmf-form expectation, then
`(x, y) ∈ distortionTypicalSet μ Xs Ys d n ε' δ` provided
`ε · (∑_{p} d(p)) ≤ δ` and the joint axis weak-typicality follows.

This is the "γ.4" wrap-up. We need TWO inclusions:

1. the joint-axis weak typicality (from `jointStronglyTypicalSet_joint_axis_subset`);
2. the X-axis and Y-axis weak typicality (deferred — strong-marginal implication);
3. the distortion bound (`jointStronglyTypicalSet_implies_distortion_close`).

For Phase γ MVP we provide ONLY the distortion bound conclusion. The
inclusion into `distortionTypicalSet` (which packages it with `jointlyTypicalSet`
membership) is deferred to Phase δ, where we will state the result in the
strong-typicality form directly (skipping the weak `jointlyTypicalSet`
intermediate). -/
theorem jointStronglyTypicalSet_implies_distortion_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) {n : ℕ} {ε δ : ℝ}
    (hε : 0 ≤ ε)
    (h_slack : ε * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ)
    (x : Fin n → α) (y : Fin n → β)
    (hxy : (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε) :
    blockDistortion d n x y
      ≤ expectedDistortionPmf d
          (fun p => (μ.map (jointSequence Xs Ys 0)).real {p}) + δ := by
  have h_bound := jointStronglyTypicalSet_implies_distortion_close
    μ Xs Ys d x y hxy
  -- |A - B| ≤ ε · S ≤ δ ⟹ A ≤ B + δ
  have h_abs : blockDistortion d n x y
        - expectedDistortionPmf d
            (fun p => (μ.map (jointSequence Xs Ys 0)).real {p})
      ≤ ε * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) :=
    le_trans (le_abs_self _) h_bound
  linarith

end InformationTheory.Shannon
