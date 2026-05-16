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

/-! ## Phase δ — Strong-typical independent probability lower bound -/

/-! ### δ.1 — Marginalisation of `typeCount` over the second/first coordinate -/

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- **Marginalising the joint type-count over `β` recovers the X type-count**:
`∑_b typeCount (fun i => (x i, y i)) (a, b) = typeCount x a`. -/
lemma typeCount_joint_sum_snd
    {n : ℕ} (x : Fin n → α) (y : Fin n → β) (a : α) :
    ∑ b : β, typeCount (fun i => (x i, y i)) (a, b) = typeCount x a := by
  classical
  -- typeCount (z) (a,b) = card of fibre, partition Fin n by y i to recover typeCount x a.
  unfold typeCount
  -- Σ_b card (filter (z i = (a,b))) = card (filter (x i = a))
  have h_eq : ∀ b : β,
      (Finset.univ.filter (fun i : Fin n => (x i, y i) = (a, b))).card
        = (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card := by
    intro b
    congr 1
    ext i
    simp [Prod.mk.injEq]
  simp_rw [h_eq]
  -- ∑ b, card (filter (x i = a ∧ y i = b)) = card (filter (x i = a))
  -- via fiberwise: filter (x i = a) = ⋃_b filter (x i = a ∧ y i = b)
  rw [← Finset.card_biUnion (s := Finset.univ)
    (t := fun b : β => Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)) (by
    intros b₁ _ b₂ _ hb12
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    simp only [Finset.mem_filter] at hi₁ hi₂
    exact hb12 (hi₁.2.2.symm.trans hi₂.2.2))]
  congr 1
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ⟨_, hxa, _⟩ => hxa, fun hxa => ⟨y i, hxa, rfl⟩⟩

omit [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- **Marginalising the joint type-count over `α` recovers the Y type-count**. -/
lemma typeCount_joint_sum_fst
    {n : ℕ} (x : Fin n → α) (y : Fin n → β) (b : β) :
    ∑ a : α, typeCount (fun i => (x i, y i)) (a, b) = typeCount y b := by
  classical
  unfold typeCount
  have h_eq : ∀ a : α,
      (Finset.univ.filter (fun i : Fin n => (x i, y i) = (a, b))).card
        = (Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)).card := by
    intro a
    congr 1
    ext i
    simp [Prod.mk.injEq]
  simp_rw [h_eq]
  rw [← Finset.card_biUnion (s := Finset.univ)
    (t := fun a : α => Finset.univ.filter (fun i : Fin n => x i = a ∧ y i = b)) (by
    intros a₁ _ a₂ _ ha12
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    simp only [Finset.mem_filter] at hi₁ hi₂
    exact ha12 (hi₁.2.1.symm.trans hi₂.2.1))]
  congr 1
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ⟨_, _, hyb⟩ => hyb, fun hyb => ⟨x i, ⟨rfl, hyb⟩⟩⟩

/-! ### δ.2 — Strong joint ⟹ Strong X and Strong Y typicality (with widened slack) -/

/-- **Strong joint typicality ⟹ Strong X-typicality (slack widened by `|β|`)**.
Given `(fun i => (x i, y i)) ∈ stronglyTypicalSet μ (jointSequence Xs Ys) n ε` and
`(μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0)`, we have
`x ∈ stronglyTypicalSet μ Xs n (Fintype.card β · ε)`. -/
lemma jointStronglyTypicalSet_implies_X_stronglyTypical
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε)
    (x : Fin n → α) (y : Fin n → β)
    (hxy : (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε) :
    x ∈ stronglyTypicalSet μ Xs n ((Fintype.card β : ℝ) * ε) := by
  classical
  rw [mem_jointStronglyTypicalSet_iff, mem_stronglyTypicalSet_iff] at hxy
  intro a
  -- typeCount x a / n = ∑_b typeCount (x,y) (a,b) / n
  have h_marg : (typeCount x a : ℝ) = ∑ b : β,
      (typeCount (fun i => (x i, y i)) (a, b) : ℝ) := by
    rw [← typeCount_joint_sum_snd x y a, Nat.cast_sum]
  -- P_X(a) = ∑_b q(a,b) where q := (μ.map jointSequence) and the marginal map equals P_X.
  set q : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hq_def
  have h_PX : (μ.map (Xs 0)).real {a} = ∑ b : β, q (a, b) := by
    -- (μ.map (Xs 0)).real {a} = ((μ.map (Z 0)).map fst).real {a} = ∑_b (μ.map (Z 0)).real {(a,b)}.
    rw [← hmarg_X]
    have h_meas_fst : Measurable (Prod.fst : α × β → α) := measurable_fst
    have h_preimage_eq :
        (Prod.fst : α × β → α) ⁻¹' {a}
          = ⋃ b ∈ (Finset.univ : Finset β), ({(a, b)} : Set (α × β)) := by
      ext p
      constructor
      · intro hp
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
        refine Set.mem_biUnion (Finset.mem_univ p.2) ?_
        rw [Set.mem_singleton_iff]
        exact Prod.ext hp rfl
      · intro hp
        rw [Set.mem_iUnion₂] at hp
        obtain ⟨b, _, hp_eq⟩ := hp
        rw [Set.mem_singleton_iff] at hp_eq
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        rw [hp_eq]
    show ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a}
        = ∑ b : β, q (a, b)
    have h_map_apply :
        ((μ.map (jointSequence Xs Ys 0)).map Prod.fst).real {a}
          = (μ.map (jointSequence Xs Ys 0)).real ((Prod.fst : α × β → α) ⁻¹' {a}) := by
      show (((μ.map (jointSequence Xs Ys 0)).map Prod.fst) {a}).toReal
          = ((μ.map (jointSequence Xs Ys 0)) ((Prod.fst : α × β → α) ⁻¹' {a})).toReal
      congr 1
      exact Measure.map_apply h_meas_fst (measurableSet_singleton a)
    rw [h_map_apply, h_preimage_eq]
    -- Apply measureReal_biUnion_finset.
    rw [measureReal_biUnion_finset (s := (Finset.univ : Finset β))
      (f := fun b : β => ({(a, b)} : Set (α × β)))
      (hd := by
        intros b₁ _ b₂ _ hb12
        show Disjoint _ _
        rw [Set.disjoint_iff_inter_eq_empty]
        ext p
        constructor
        · rintro ⟨h1, h2⟩
          rw [Set.mem_singleton_iff] at h1 h2
          subst h1
          have : b₁ = b₂ := (Prod.mk.injEq _ _ _ _).mp h2 |>.2
          exact (hb12 this).elim
        · intro h; exact h.elim)
      (hm := fun b _ => measurableSet_singleton _)]
  -- Now bound |typeCount x a / n - P_X(a)| via triangle inequality through the joint sum.
  have h_diff_eq :
      (typeCount x a : ℝ) / n - (μ.map (Xs 0)).real {a}
        = ∑ b : β,
            ((typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n - q (a, b)) := by
    rw [h_marg, h_PX, Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [h_diff_eq]
  calc |∑ b : β,
            ((typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n - q (a, b))|
      ≤ ∑ b : β,
            |((typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n - q (a, b))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : β, ε := by
        refine Finset.sum_le_sum fun b _ => ?_
        exact hxy (a, b)
    _ = (Fintype.card β : ℝ) * ε := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **Strong joint typicality ⟹ Strong Y-typicality (slack widened by `|α|`)**. -/
lemma jointStronglyTypicalSet_implies_Y_stronglyTypical
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε)
    (x : Fin n → α) (y : Fin n → β)
    (hxy : (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε) :
    y ∈ stronglyTypicalSet μ Ys n ((Fintype.card α : ℝ) * ε) := by
  classical
  rw [mem_jointStronglyTypicalSet_iff, mem_stronglyTypicalSet_iff] at hxy
  intro b
  have h_marg : (typeCount y b : ℝ) = ∑ a : α,
      (typeCount (fun i => (x i, y i)) (a, b) : ℝ) := by
    rw [← typeCount_joint_sum_fst x y b, Nat.cast_sum]
  set q : α × β → ℝ := fun p => (μ.map (jointSequence Xs Ys 0)).real {p} with hq_def
  have h_PY : (μ.map (Ys 0)).real {b} = ∑ a : α, q (a, b) := by
    rw [← hmarg_Y]
    have h_meas_snd : Measurable (Prod.snd : α × β → β) := measurable_snd
    have h_preimage_eq :
        (Prod.snd : α × β → β) ⁻¹' {b}
          = ⋃ a ∈ (Finset.univ : Finset α), ({(a, b)} : Set (α × β)) := by
      ext p
      constructor
      · intro hp
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
        refine Set.mem_biUnion (Finset.mem_univ p.1) ?_
        rw [Set.mem_singleton_iff]
        exact Prod.ext rfl hp
      · intro hp
        rw [Set.mem_iUnion₂] at hp
        obtain ⟨a, _, hp_eq⟩ := hp
        rw [Set.mem_singleton_iff] at hp_eq
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        rw [hp_eq]
    show ((μ.map (jointSequence Xs Ys 0)).map Prod.snd).real {b}
        = ∑ a : α, q (a, b)
    have h_map_apply :
        ((μ.map (jointSequence Xs Ys 0)).map Prod.snd).real {b}
          = (μ.map (jointSequence Xs Ys 0)).real ((Prod.snd : α × β → β) ⁻¹' {b}) := by
      show (((μ.map (jointSequence Xs Ys 0)).map Prod.snd) {b}).toReal
          = ((μ.map (jointSequence Xs Ys 0)) ((Prod.snd : α × β → β) ⁻¹' {b})).toReal
      congr 1
      exact Measure.map_apply h_meas_snd (measurableSet_singleton b)
    rw [h_map_apply, h_preimage_eq]
    rw [measureReal_biUnion_finset (s := (Finset.univ : Finset α))
      (f := fun a : α => ({(a, b)} : Set (α × β)))
      (hd := by
        intros a₁ _ a₂ _ ha12
        show Disjoint _ _
        rw [Set.disjoint_iff_inter_eq_empty]
        ext p
        constructor
        · rintro ⟨h1, h2⟩
          rw [Set.mem_singleton_iff] at h1 h2
          subst h1
          have : a₁ = a₂ := (Prod.mk.injEq _ _ _ _).mp h2 |>.1
          exact (ha12 this).elim
        · intro h; exact h.elim)
      (hm := fun a _ => measurableSet_singleton _)]
  have h_diff_eq :
      (typeCount y b : ℝ) / n - (μ.map (Ys 0)).real {b}
        = ∑ a : α,
            ((typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n - q (a, b)) := by
    rw [h_marg, h_PY, Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [h_diff_eq]
  calc |∑ a : α,
            ((typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n - q (a, b))|
      ≤ ∑ a : α,
            |((typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n - q (a, b))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : α, ε := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact hxy (a, b)
    _ = (Fintype.card α : ℝ) * ε := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-! ### δ.3 — Main theorem: strong joint typicality probability lower bound -/

/-- **Strong-typical independent probability lower bound** (mirror of
`jointlyTypicalSet_indep_prob_ge` for the strong-typicality version).

For an i.i.d. joint sequence with marginals matching `μ.map (Xs 0)` and `μ.map (Ys 0)`,
and any `η > 0`, eventually for all `n` large enough,

  `(1 - η) · exp(n · ((H(Z) - H(X) - H(Y)) - ((Fintype.card β · L_X + Fintype.card α · L_Y + L_Z) · ε + 3 δ)))
    ≤ (μ_X^n × μ_Y^n).real (jointStronglyTypicalSet ε)`,

where `L_X := logSumAbs μ Xs`, `L_Y := logSumAbs μ Ys`, `L_Z := logSumAbs μ (jointSequence Xs Ys)`,
and `δ > 0` is an arbitrary auxiliary slack.

Compared to the weak version's `3ε` slack, the strong version has slack
`(Fintype.card β · L_X + Fintype.card α · L_Y + L_Z) · ε + 3 δ` because converting from the
strong joint typicality (slack `ε`) to weak X/Y/joint typicality (slack `< ε'`)
through `stronglyTypicalSet_subset_typicalSet` amplifies `ε` by the Lipschitz constant. -/
theorem jointStronglyTypicalSet_indep_prob_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hindepZ_pair : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i)
                      (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - η) * Real.exp ((n : ℝ) *
        ((entropy μ (jointSequence Xs Ys 0)
            - entropy μ (Xs 0) - entropy μ (Ys 0))
          - (((Fintype.card β : ℝ) * ε * logSumAbs μ Xs
              + (Fintype.card α : ℝ) * ε * logSumAbs μ Ys
              + ε * logSumAbs μ (jointSequence Xs Ys))
              + 3 * δ)))
        ≤ ((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real
            (jointStronglyTypicalSet μ Xs Ys n ε) := by
  classical
  set Zs : ℕ → Ω → α × β := jointSequence Xs Ys with hZs_def
  set HX : ℝ := entropy μ (Xs 0) with hHX_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set HZ : ℝ := entropy μ (Zs 0) with hHZ_def
  set LX : ℝ := logSumAbs μ Xs with hLX_def
  set LY : ℝ := logSumAbs μ Ys with hLY_def
  set LZ : ℝ := logSumAbs μ Zs with hLZ_def
  have hLX_nn : 0 ≤ LX := logSumAbs_nonneg μ Xs
  have hLY_nn : 0 ≤ LY := logSumAbs_nonneg μ Ys
  have hLZ_nn : 0 ≤ LZ := logSumAbs_nonneg μ Zs
  -- Strong-typical card lower bound (eventually).
  have hZmeas : ∀ i, Measurable (Zs i) := fun i =>
    measurable_jointSequence Xs Ys hXs hYs i
  obtain ⟨N₀, hN₀⟩ := stronglyTypicalSet_card_ge_eventually μ Zs hZmeas
    hindepZ_full hindepZ_pair hidentZ hposZ hε hδ hη
  refine ⟨max N₀ 1, fun n hn_ge => ?_⟩
  have hn_N₀ : N₀ ≤ n := le_of_max_le_left hn_ge
  have hn_pos : 0 < n := by have := le_of_max_le_right hn_ge; omega
  -- Card lower bound on stronglyTypicalSet of Zs.
  have h_card_ge :
      (1 - η) * Real.exp ((n : ℝ) * (HZ - ε * LZ - δ))
        ≤ ((stronglyTypicalSet μ Zs n ε).toFinite.toFinset.card : ℝ) := hN₀ n hn_N₀
  -- Reshape: define A := jointStronglyTypicalSet via the φ-injection.
  let φ : (Fin n → α) × (Fin n → β) → (Fin n → α × β) :=
    fun p i => (p.1 i, p.2 i)
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    apply Prod.ext
    · funext i
      exact ((Prod.mk.injEq _ _ _ _).mp (congr_fun hpq i)).1
    · funext i
      exact ((Prod.mk.injEq _ _ _ _).mp (congr_fun hpq i)).2
  set A : Set ((Fin n → α) × (Fin n → β)) := jointStronglyTypicalSet μ Xs Ys n ε
    with hA_def
  set Afin : Finset ((Fin n → α) × (Fin n → β)) :=
    (jointStronglyTypicalSet_finite μ Xs Ys n ε).toFinset with hAfin_def
  -- The image φ '' Afin lies in (stronglyTypicalSet μ Zs n ε).toFinset.
  -- And |φ '' Afin| = |Afin|.
  set Tfin : Finset (Fin n → α × β) := (stronglyTypicalSet μ Zs n ε).toFinite.toFinset
    with hTfin_def
  -- φ is bijective: inverse is z ↦ (fun i => (z i).1, fun i => (z i).2).
  have hφ_surj : Function.Surjective φ := by
    intro z
    refine ⟨(fun i => (z i).1, fun i => (z i).2), ?_⟩
    funext i; rfl
  -- φ '' Afin = Tfin via membership iff.
  have h_image_eq : Afin.image φ = Tfin := by
    ext q
    simp only [Finset.mem_image, hAfin_def, hTfin_def, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨x, y⟩, hxy_mem, rfl⟩
      rw [mem_jointStronglyTypicalSet_iff] at hxy_mem
      exact hxy_mem
    · intro hq
      obtain ⟨p, rfl⟩ := hφ_surj q
      refine ⟨p, ?_, rfl⟩
      rw [show p = (p.1, p.2) from rfl, mem_jointStronglyTypicalSet_iff]
      exact hq
  have h_card_eq_nat : Afin.card = Tfin.card := by
    rw [← h_image_eq, Finset.card_image_of_injective _ hφ_inj]
  have h_card_eq : (Afin.card : ℝ) = (Tfin.card : ℝ) := by
    exact_mod_cast h_card_eq_nat
  have h_Afin_ge : (1 - η) * Real.exp ((n : ℝ) * (HZ - ε * LZ - δ))
      ≤ (Afin.card : ℝ) := by
    rw [h_card_eq]; exact h_card_ge
  -- Strong joint ⟹ Strong X (slack |β|·ε), then ⊆ Weak X (slack |β|·ε·LX + δ).
  have h_meas_X : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
  have h_meas_Y : Measurable (jointRV Ys n) := measurable_jointRV Ys hYs n
  set μXn : Measure (Fin n → α) := μ.map (jointRV Xs n) with hμXn_def
  set μYn : Measure (Fin n → β) := μ.map (jointRV Ys n) with hμYn_def
  haveI hμX_isProb : IsProbabilityMeasure μXn :=
    Measure.isProbabilityMeasure_map h_meas_X.aemeasurable
  haveI hμY_isProb : IsProbabilityMeasure μYn :=
    Measure.isProbabilityMeasure_map h_meas_Y.aemeasurable
  haveI : IsProbabilityMeasure (μXn.prod μYn) := by infer_instance
  set εX : ℝ := (Fintype.card β : ℝ) * ε with hεX_def
  set εY : ℝ := (Fintype.card α : ℝ) * ε with hεY_def
  set εX' : ℝ := εX * LX + δ with hεX'_def
  set εY' : ℝ := εY * LY + δ with hεY'_def
  have hεX_nn : 0 ≤ εX := mul_nonneg (Nat.cast_nonneg _) hε.le
  have hεY_nn : 0 ≤ εY := mul_nonneg (Nat.cast_nonneg _) hε.le
  have hεX'_pos : 0 < εX' := by
    have : 0 ≤ εX * LX := mul_nonneg hεX_nn hLX_nn
    linarith
  have hεY'_pos : 0 < εY' := by
    have : 0 ≤ εY * LY := mul_nonneg hεY_nn hLY_nn
    linarith
  -- Per-pair pointwise lower bound on the product measure.
  have h_each_ge : ∀ p ∈ Afin,
      Real.exp (-(n : ℝ) * (HX + εX'))
        * Real.exp (-(n : ℝ) * (HY + εY'))
        ≤ μXn.real {p.1} * μYn.real {p.2} := by
    intro p hp
    have hp_set : p ∈ A := (Set.Finite.mem_toFinset _).mp hp
    rcases p with ⟨x, y⟩
    -- x is strongly typical for Xs at εX = |β|·ε.
    have hxX_strong : x ∈ stronglyTypicalSet μ Xs n εX :=
      jointStronglyTypicalSet_implies_X_stronglyTypical μ Xs Ys hXs hYs hmarg_X
        hn_pos hε.le x y hp_set
    -- x is weakly typical for Xs at εX' = εX·LX + δ (strict bound from strong ⊆ weak).
    have hxX_weak : x ∈ typicalSet μ Xs n εX' := by
      apply stronglyTypicalSet_subset_typicalSet μ Xs hXs hn_pos
      show εX * LX < εX * LX + δ
      linarith
      exact hxX_strong
    -- y is strongly typical for Ys at εY = |α|·ε.
    have hyY_strong : y ∈ stronglyTypicalSet μ Ys n εY :=
      jointStronglyTypicalSet_implies_Y_stronglyTypical μ Xs Ys hXs hYs hmarg_Y
        hn_pos hε.le x y hp_set
    have hyY_weak : y ∈ typicalSet μ Ys n εY' := by
      apply stronglyTypicalSet_subset_typicalSet μ Ys hYs hn_pos
      show εY * LY < εY * LY + δ
      linarith
      exact hyY_strong
    have hbdX : Real.exp (-(n : ℝ) * (HX + εX')) ≤ μXn.real {x} :=
      InformationTheory.Shannon.typicalSet_prob_ge μ Xs hXs hindepX_full hidentX
        hposX n x hxX_weak
    have hbdY : Real.exp (-(n : ℝ) * (HY + εY')) ≤ μYn.real {y} :=
      InformationTheory.Shannon.typicalSet_prob_ge μ Ys hYs hindepY_full hidentY
        hposY n y hyY_weak
    have hY_exp_nn : 0 ≤ Real.exp (-(n : ℝ) * (HY + εY')) := (Real.exp_pos _).le
    have hX_nn : 0 ≤ μXn.real {x} := measureReal_nonneg
    calc Real.exp (-(n : ℝ) * (HX + εX')) * Real.exp (-(n : ℝ) * (HY + εY'))
        ≤ μXn.real {x} * Real.exp (-(n : ℝ) * (HY + εY')) := by
          exact mul_le_mul_of_nonneg_right hbdX hY_exp_nn
      _ ≤ μXn.real {x} * μYn.real {y} := by
          exact mul_le_mul_of_nonneg_left hbdY hX_nn
  -- Sum the per-pair bounds over Afin.
  set C : ℝ := Real.exp (-(n : ℝ) * (HX + εX')) * Real.exp (-(n : ℝ) * (HY + εY'))
    with hC_def
  have hC_nn : 0 ≤ C :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have h_sum_ge : (Afin.card : ℝ) * C
      ≤ ∑ p ∈ Afin, μXn.real {p.1} * μYn.real {p.2} := by
    calc (Afin.card : ℝ) * C
        = ∑ _p ∈ Afin, C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ Afin, μXn.real {p.1} * μYn.real {p.2} :=
          Finset.sum_le_sum h_each_ge
  -- Sum identifies as product measure.
  have h_sum_eq :
      (∑ p ∈ Afin, μXn.real {p.1} * μYn.real {p.2})
        = (μXn.prod μYn).real A := by
    have h_real_eq : (μXn.prod μYn).real A
        = ∑ p ∈ Afin, (μXn.prod μYn).real {p} := by
      have h_coe : (Afin : Set _) = A :=
        (jointStronglyTypicalSet_finite μ Xs Ys n ε).coe_toFinset
      rw [← h_coe, ← sum_measureReal_singleton (μ := μXn.prod μYn) Afin]
    rw [h_real_eq]
    refine (Finset.sum_congr rfl ?_).symm
    intro p _
    have h_singleton_prod : ({p} : Set ((Fin n → α) × (Fin n → β)))
        = ({p.1} : Set (Fin n → α)) ×ˢ ({p.2} : Set (Fin n → β)) := by
      ext q
      simp [Prod.ext_iff]
    rw [h_singleton_prod]
    exact measureReal_prod_prod (μ := μXn) (ν := μYn)
      ({p.1} : Set (Fin n → α)) ({p.2} : Set (Fin n → β))
  -- Combine: lower-bound LHS = (1-η)·exp(...) ≤ Afin.card · C ≤ (μXn.prod μYn).real A.
  -- Need to verify the LHS exponent matches.
  -- LHS exp = n · ((HZ - HX - HY) - ((|β|·LX + |α|·LY + LZ)·ε + 3δ))
  --        = n · (HZ - ε·LZ - δ) + n · (-(HX + εX')) + n · (-(HY + εY'))
  -- because the second and third terms combine as -n·(HX+HY+εX·LX+εY·LY+2δ)
  -- = -n·(HX+HY+|β|·ε·LX+|α|·ε·LY+2δ) and combined with n·(HZ-ε·LZ-δ) we get
  -- n·(HZ-HX-HY-|β|·ε·LX-|α|·ε·LY-ε·LZ-3δ).  ✓
  have h_exp_combine :
      Real.exp ((n : ℝ) * (HZ - ε * LZ - δ)) * C
        = Real.exp ((n : ℝ) *
          ((HZ - HX - HY) - ((εX * LX + εY * LY + ε * LZ) + 3 * δ))) := by
    rw [hC_def]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    -- Goal: n*(HZ-ε*LZ-δ) + (-n*(HX+εX') + -n*(HY+εY'))
    --       = n*((HZ-HX-HY) - ((εX*LX + εY*LY + ε*LZ) + 3*δ))
    -- With εX' = εX*LX+δ, εY' = εY*LY+δ this is a ring identity.
    show (n : ℝ) * (HZ - ε * LZ - δ)
        + (-(n : ℝ) * (HX + (εX * LX + δ)) + -(n : ℝ) * (HY + (εY * LY + δ)))
      = (n : ℝ) * ((HZ - HX - HY) - ((εX * LX + εY * LY + ε * LZ) + 3 * δ))
    ring
  -- Lower bound: (1-η) · exp(n · (HZ - ε·LZ - δ)) · C ≤ Afin.card · C ≤ sum ≤ (μXn.prod μYn).real A.
  have h_mul_C : (1 - η) * Real.exp ((n : ℝ) * (HZ - ε * LZ - δ)) * C
      ≤ (Afin.card : ℝ) * C := mul_le_mul_of_nonneg_right h_Afin_ge hC_nn
  calc (1 - η) * Real.exp ((n : ℝ) *
        ((HZ - HX - HY)
          - ((εX * LX + εY * LY + ε * LZ) + 3 * δ)))
      = (1 - η) * (Real.exp ((n : ℝ) * (HZ - ε * LZ - δ)) * C) := by
        rw [h_exp_combine]
    _ = (1 - η) * Real.exp ((n : ℝ) * (HZ - ε * LZ - δ)) * C := by ring
    _ ≤ (Afin.card : ℝ) * C := h_mul_C
    _ ≤ ∑ p ∈ Afin, μXn.real {p.1} * μYn.real {p.2} := h_sum_ge
    _ = (μXn.prod μYn).real A := h_sum_eq

end InformationTheory.Shannon
