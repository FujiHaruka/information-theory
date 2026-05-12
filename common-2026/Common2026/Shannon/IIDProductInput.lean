import Common2026.Shannon.ChannelCoding
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# i.i.d. ambient `(μ, Xs, Ys)` for Phase D-(b) of channel coding achievability

[B-3'' Phase C+D plan](../../../docs/shannon/channel-coding-phase-cd-plan.md).

This file provides the **i.i.d. ambient probability space** consumed by the
abstract `random_codebook_average_le` (Phase C-(c)) and the main theorem
`channel_coding_achievability` (Phase D-(b)) of
`Common2026/Shannon/ChannelCodingAchievability.lean`.

## Construction

Given an input distribution `p : Measure α` (a probability measure) and a
channel `W : Channel α β` (a Markov kernel), the i.i.d. ambient space is
`Ω := ℕ → α × β` equipped with the product measure
`μ := Measure.infinitePi (fun _ : ℕ => jointDistribution p W)`. Random variables
are coordinate projections:

* `iidXs i ω := (ω i).1` — the i-th input symbol
* `iidYs i ω := (ω i).2` — the i-th output symbol

These exactly match the abstract `Xs`, `Ys` hypothesis shapes (`iIndepFun`,
`IdentDistrib`, marginal-matching) demanded by the Phase B / C lemmas.

## Channel positivity

The `hposY` / `hposZ` positivity lemmas require the channel-positivity
hypothesis `∀ a y, 0 < W a {y}` (in addition to input positivity
`∀ a, 0 < p.real {a}`). Without it `outputDistribution p W` and
`jointDistribution p W` can hit zero on some singleton.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Ambient measure on `ℕ → α × β` -/

/-- The i.i.d. ambient measure for input distribution `p` and channel `W`:
`Measure.infinitePi (fun _ : ℕ => jointDistribution p W)` on `ℕ → α × β`. -/
noncomputable def iidAmbientMeasure
    (p : Measure α) (W : Channel α β) : Measure (ℕ → α × β) :=
  Measure.infinitePi (fun _ : ℕ => jointDistribution p W)

instance iidAmbientMeasure.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    IsProbabilityMeasure (iidAmbientMeasure p W) := by
  unfold iidAmbientMeasure
  infer_instance

/-- The `i`-th input random variable: `ω ↦ (ω i).1`. -/
def iidXs : ℕ → (ℕ → α × β) → α := fun i ω => (ω i).1

/-- The `i`-th output random variable: `ω ↦ (ω i).2`. -/
def iidYs : ℕ → (ℕ → α × β) → β := fun i ω => (ω i).2

omit [MeasurableSpace α] [MeasurableSpace β] in
@[simp] lemma iidXs_apply (i : ℕ) (ω : ℕ → α × β) : iidXs i ω = (ω i).1 := rfl

omit [MeasurableSpace α] [MeasurableSpace β] in
@[simp] lemma iidYs_apply (i : ℕ) (ω : ℕ → α × β) : iidYs i ω = (ω i).2 := rfl

lemma measurable_iidXs (i : ℕ) : Measurable (iidXs (α := α) (β := β) i) :=
  (measurable_pi_apply i).fst

lemma measurable_iidYs (i : ℕ) : Measurable (iidYs (α := α) (β := β) i) :=
  (measurable_pi_apply i).snd

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- The joint sequence collapses to the raw coordinate projection
`fun ω ↦ ω i` modulo `Prod.mk` η. -/
lemma jointSequence_iidXs_iidYs (i : ℕ) :
    jointSequence (α := α) (β := β) iidXs iidYs i = fun ω => ω i := by
  funext ω; rfl

/-! ### Marginal laws

The three coordinate-marginal identifications `μ.map (Xs 0) = p`,
`μ.map (Ys 0) = outputDistribution p W`,
`μ.map (jointSequence Xs Ys 0) = jointDistribution p W`. -/

/-- The joint sequence marginal at index `i` is the joint distribution `p ⊗ₘ W`. -/
lemma iidAmbient_map_jointSequence
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (i : ℕ) :
    (iidAmbientMeasure p W).map (jointSequence iidXs iidYs i)
      = jointDistribution p W := by
  rw [jointSequence_iidXs_iidYs]
  exact Measure.infinitePi_map_eval (μ := fun _ : ℕ => jointDistribution p W) i

/-- The input marginal `μ.map (Xs i) = p`. -/
lemma iidAmbient_map_iidXs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (i : ℕ) :
    (iidAmbientMeasure p W).map (iidXs i) = p := by
  -- iidXs i = Prod.fst ∘ (fun ω => ω i)
  have h_comp : iidXs (α := α) (β := β) i
      = Prod.fst ∘ (fun ω : ℕ → α × β => ω i) := by
    funext ω; rfl
  rw [h_comp, ← Measure.map_map measurable_fst (measurable_pi_apply i)]
  -- (iidAmbientMeasure p W).map (fun ω => ω i) = jointDistribution p W
  have h_eval : (iidAmbientMeasure p W).map (fun ω : ℕ → α × β => ω i)
      = jointDistribution p W :=
    Measure.infinitePi_map_eval (μ := fun _ : ℕ => jointDistribution p W) i
  rw [h_eval]
  -- (jointDistribution p W).map Prod.fst = (jointDistribution p W).fst = p
  show (jointDistribution p W).fst = p
  rw [jointDistribution_def]
  exact Measure.fst_compProd p W

/-- The output marginal `μ.map (Ys i) = outputDistribution p W`. -/
lemma iidAmbient_map_iidYs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (i : ℕ) :
    (iidAmbientMeasure p W).map (iidYs i) = outputDistribution p W := by
  have h_comp : iidYs (α := α) (β := β) i
      = Prod.snd ∘ (fun ω : ℕ → α × β => ω i) := by
    funext ω; rfl
  rw [h_comp, ← Measure.map_map measurable_snd (measurable_pi_apply i)]
  have h_eval : (iidAmbientMeasure p W).map (fun ω : ℕ → α × β => ω i)
      = jointDistribution p W :=
    Measure.infinitePi_map_eval (μ := fun _ : ℕ => jointDistribution p W) i
  rw [h_eval]
  rfl

/-! ### `IdentDistrib` along each axis -/

lemma iidAmbient_identDistrib_iidXs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (i : ℕ) :
    IdentDistrib (iidXs i) (iidXs 0)
      (iidAmbientMeasure p W) (iidAmbientMeasure p W) where
  aemeasurable_fst := (measurable_iidXs i).aemeasurable
  aemeasurable_snd := (measurable_iidXs 0).aemeasurable
  map_eq := by rw [iidAmbient_map_iidXs, iidAmbient_map_iidXs]

lemma iidAmbient_identDistrib_iidYs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (i : ℕ) :
    IdentDistrib (iidYs i) (iidYs 0)
      (iidAmbientMeasure p W) (iidAmbientMeasure p W) where
  aemeasurable_fst := (measurable_iidYs i).aemeasurable
  aemeasurable_snd := (measurable_iidYs 0).aemeasurable
  map_eq := by rw [iidAmbient_map_iidYs, iidAmbient_map_iidYs]

lemma iidAmbient_identDistrib_joint
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (i : ℕ) :
    IdentDistrib (jointSequence iidXs iidYs i) (jointSequence iidXs iidYs 0)
      (iidAmbientMeasure p W) (iidAmbientMeasure p W) where
  aemeasurable_fst :=
    (measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs i).aemeasurable
  aemeasurable_snd :=
    (measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs 0).aemeasurable
  map_eq := by rw [iidAmbient_map_jointSequence, iidAmbient_map_jointSequence]

/-! ### `iIndepFun` along each axis -/

/-- The input coordinates `Xs i ω = (ω i).1` are mutually independent under the
i.i.d. ambient measure. -/
lemma iidAmbient_iIndepFun_iidXs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    iIndepFun (fun i : ℕ => iidXs (α := α) (β := β) i) (iidAmbientMeasure p W) := by
  -- iidXs i ω = Prod.fst (ω i), of the shape `fun i ω => f i (ω i)` with `f i := Prod.fst`.
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ => jointDistribution p W)
    (X := fun _ : ℕ => Prod.fst (α := α) (β := β))
    (fun _ => measurable_fst)

/-- The output coordinates `Ys i ω = (ω i).2` are mutually independent. -/
lemma iidAmbient_iIndepFun_iidYs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    iIndepFun (fun i : ℕ => iidYs (α := α) (β := β) i) (iidAmbientMeasure p W) := by
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ => jointDistribution p W)
    (X := fun _ : ℕ => Prod.snd (α := α) (β := β))
    (fun _ => measurable_snd)

/-- The joint coordinate sequence `jointSequence iidXs iidYs i ω = ω i` is
mutually independent. -/
lemma iidAmbient_iIndepFun_joint
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    iIndepFun (fun i : ℕ => jointSequence (α := α) (β := β) iidXs iidYs i)
      (iidAmbientMeasure p W) := by
  -- jointSequence iidXs iidYs i ω = ω i = id (ω i)
  have h_eq :
      (fun i : ℕ => jointSequence (α := α) (β := β) iidXs iidYs i)
        = (fun (i : ℕ) (ω : ℕ → α × β) => (id : α × β → α × β) (ω i)) := by
    funext i ω; rfl
  rw [h_eq]
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ => jointDistribution p W)
    (X := fun _ : ℕ => (id : α × β → α × β))
    (fun _ => measurable_id)

/-- Pairwise independence for the joint axis: needed by
`jointlyTypicalSet_prob_tendsto_one` (which takes the `Pairwise … ⟂ᵢ[μ] …` form
rather than the full `iIndepFun` form). -/
lemma iidAmbient_pairwise_indep_joint
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    Pairwise fun i j =>
      IndepFun (jointSequence (α := α) (β := β) iidXs iidYs i)
        (jointSequence iidXs iidYs j) (iidAmbientMeasure p W) := by
  intro i j hij
  exact (iidAmbient_iIndepFun_joint p W).indepFun hij

lemma iidAmbient_pairwise_indep_iidXs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    Pairwise fun i j =>
      IndepFun (iidXs (α := α) (β := β) i) (iidXs j) (iidAmbientMeasure p W) := by
  intro i j hij
  exact (iidAmbient_iIndepFun_iidXs p W).indepFun hij

lemma iidAmbient_pairwise_indep_iidYs
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    Pairwise fun i j =>
      IndepFun (iidYs (α := α) (β := β) i) (iidYs j) (iidAmbientMeasure p W) := by
  intro i j hij
  exact (iidAmbient_iIndepFun_iidYs p W).indepFun hij

/-! ### Positivity of singleton marginals -/

section Positivity

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [MeasurableSingletonClass β]

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Singleton mass of the joint distribution: `(p ⊗ₘ W) {(x, y)} = p {x} * W x {y}`.
Uses `Set.singleton_prod_singleton` to rewrite the singleton as a product set and
then `compProd_apply_prod` + `lintegral_singleton` to evaluate. -/
lemma jointDistribution_singleton
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (x : α) (y : β) :
    jointDistribution p W {(x, y)} = p {x} * W x {y} := by
  classical
  rw [jointDistribution_def, ← Set.singleton_prod_singleton,
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
  -- ∫⁻ a in {x}, W a {y} ∂p = (fun a => W a {y}) x * p {x} = W x {y} * p {x}.
  rw [lintegral_singleton (fun a => W a {y}) x, mul_comm]

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Positivity of `(jointDistribution p W).real {(x, y)}` from input + channel
positivity. -/
lemma jointDistribution_singleton_pos
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b})
    (x : α) (y : β) :
    0 < (jointDistribution p W).real {(x, y)} := by
  unfold Measure.real
  rw [jointDistribution_singleton]
  -- 0 < ENNReal.toReal (p {x} * W x {y}).
  refine ENNReal.toReal_pos ?_ ?_
  · -- p {x} * W x {y} ≠ 0
    intro h
    rcases mul_eq_zero.mp h with hpx | hWy
    · have hp_real : p.real {x} = 0 := by unfold Measure.real; rw [hpx]; simp
      exact (hp_pos x).ne' hp_real
    · have hW_real : (W x).real {y} = 0 := by unfold Measure.real; rw [hWy]; simp
      exact (hW_pos x y).ne' hW_real
  · exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [MeasurableSingletonClass β] in
/-- Positivity of the input marginal: `0 < (μ.map (iidXs 0)).real {x}`. -/
lemma iidAmbient_iidXs_real_singleton_pos
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    (hp_pos : ∀ a : α, 0 < p.real {a}) (x : α) :
    0 < ((iidAmbientMeasure p W).map (iidXs 0)).real {x} := by
  rw [iidAmbient_map_iidXs]
  exact hp_pos x

omit [DecidableEq α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] in
/-- Positivity of the output marginal: `0 < (μ.map (iidYs 0)).real {y}`. Requires
input positivity and channel positivity. -/
lemma iidAmbient_iidYs_real_singleton_pos
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b}) (y : β) :
    0 < ((iidAmbientMeasure p W).map (iidYs 0)).real {y} := by
  rw [iidAmbient_map_iidYs]
  -- outputDistribution p W = (p ⊗ₘ W).snd. We bound from below by a single mass
  -- `(p ⊗ₘ W) (univ ×ˢ {y}) ≥ (p ⊗ₘ W) ({x} ×ˢ {y}) > 0` for any fixed `x`.
  -- Pick an arbitrary `x : α` (using `Fintype.card_pos` from `[Nonempty α]`).
  -- Since `α` is finite + DecidableEq, just use `Classical.arbitrary` from `[Nonempty α]`.
  classical
  -- We need `Nonempty α` from `hp_pos : ∀ a, 0 < p.real {a}`. That's vacuous if α empty.
  -- Instead we observe: outputDistribution {y} = ∑ a, p {a} * W a {y} ≥ p {a₀} * W a₀ {y} > 0
  -- for ANY a₀, hence picking `a₀ := Classical.arbitrary α` works iff [Nonempty α].
  -- If α is empty, hp_pos is vacuously true but ouputDistribution{y} = 0. We need [Nonempty α].
  -- However outputDistribution is a probability measure, so `outputDistribution univ = 1`, and α
  -- being empty makes the sum over α empty, contradiction. So we can derive Nonempty α from
  -- IsProbabilityMeasure p: p univ = 1, but `Fintype α` empty ⇒ univ = ∅ ⇒ p univ = 0.
  -- Slightly cleaner: argue via `outputDistribution`'s probability mass.
  -- For the bound itself, use `compProd_apply_prod` on `{y}` via fst marginal.
  -- Equivalently: outputDistribution {y} = ∫⁻ a, W a {y} ∂p. Since the integrand is
  -- > 0 pointwise (`W a {y} > 0`), and `p` is a probability measure (nonzero), the
  -- integral is > 0 — formally via `lintegral_pos_iff_support`.
  unfold outputDistribution
  rw [Measure.real]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  -- (jointDistribution p W).snd {y} ≠ 0.
  intro h
  -- jointDistribution = p ⊗ₘ W. snd {y} = ∫⁻ a, W a {y} ∂p.
  rw [jointDistribution_def] at h
  have h_snd : ((p ⊗ₘ W).snd) {y}
      = ∫⁻ a, W a {y} ∂p := by
    rw [Measure.snd_apply (measurableSet_singleton _)]
    -- Prod.snd ⁻¹' {y} = Set.univ ×ˢ {y}.
    have h_pre : (Prod.snd ⁻¹' ({y} : Set β) : Set (α × β)) = Set.univ ×ˢ {y} := by
      ext ⟨a, b⟩; simp
    rw [h_pre, Measure.compProd_apply_prod MeasurableSet.univ (measurableSet_singleton _)]
    rw [Measure.restrict_univ]
  rw [h_snd] at h
  -- ∫⁻ a, W a {y} ∂p = 0 ⇒ W a {y} = 0 a.e. But W x {y} > 0 for all x.
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe W (measurableSet_singleton _))] at h
  -- h : (fun a => W a {y}) =ᵐ[p] 0.
  -- Since α is finite and p {a} > 0 for all a, the ae-zero set is empty under p ⇒ everywhere.
  have h_some : ∃ a : α, (W a) {y} ≠ 0 := by
    -- Just pick any `a` (using `Nonempty α` from `hp_pos`).
    -- α nonempty: if not, then `p` has support ∅, but `p univ = 1`. Use Fintype + Nonempty.
    have hne : Nonempty α := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI := h
      -- p univ = 1 but univ : Set α is empty
      have hpu : p (Set.univ : Set α) = 1 := measure_univ
      have h_univ_empty : (Set.univ : Set α) = ∅ := by
        ext a; exact h.elim a
      rw [h_univ_empty, measure_empty] at hpu
      exact zero_ne_one hpu
    obtain ⟨a⟩ := hne
    refine ⟨a, ?_⟩
    have := hW_pos a y
    unfold Measure.real at this
    intro hz
    rw [hz, ENNReal.toReal_zero] at this
    exact lt_irrefl 0 this
  obtain ⟨a, ha⟩ := h_some
  -- The a.e. equality h forces W a {y} = 0 for p-almost every a. But p {a} > 0.
  have h_pt : ∀ᵐ a' ∂p, (fun a' => (W a') {y}) a' = 0 := h
  -- p {a} > 0 means {a} is not p-null, so the a.e. equality forces W a {y} = 0.
  have : (fun a' => (W a') {y}) a = 0 := by
    -- Since {a} has positive p-mass and the a.e. set has full measure, intersection nonempty.
    -- Actually simpler: use ae_iff and the singleton.
    by_contra hne
    have h_ae : (fun a' => (W a') {y}) =ᵐ[p] 0 := h_pt
    -- The set {a' | W a' {y} ≠ 0} has p-measure zero.
    have h_null : p {a' | (W a') {y} ≠ 0} = 0 := by
      have := h_ae
      rw [Filter.EventuallyEq, ae_iff] at this
      simpa using this
    -- But {a} ⊆ {a' | W a' {y} ≠ 0}, so p {a} ≤ 0.
    have h_sub : ({a} : Set α) ⊆ {a' | (W a') {y} ≠ 0} := by
      intro a' ha'
      simp only [Set.mem_singleton_iff] at ha'
      simp [ha', hne]
    have h_le : p {a} ≤ 0 := h_null ▸ measure_mono h_sub
    have : p.real {a} ≤ 0 := by
      unfold Measure.real
      exact ENNReal.toReal_le_of_le_ofReal le_rfl (le_trans h_le bot_le)
    linarith [hp_pos a]
  exact ha this

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Positivity of the joint marginal: `0 < (μ.map (jointSequence iidXs iidYs 0)).real {(x, y)}`.
Requires input + channel positivity. -/
lemma iidAmbient_joint_real_singleton_pos
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b}) (q : α × β) :
    0 < ((iidAmbientMeasure p W).map (jointSequence iidXs iidYs 0)).real {q} := by
  rw [iidAmbient_map_jointSequence]
  obtain ⟨x, y⟩ := q
  exact jointDistribution_singleton_pos p W hp_pos hW_pos x y

end Positivity

end InformationTheory.Shannon.ChannelCoding
