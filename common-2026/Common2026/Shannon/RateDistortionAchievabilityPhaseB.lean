import Common2026.Shannon.RateDistortionAchievability
import Common2026.Shannon.ChannelCodingAchievability
import Common2026.Shannon.AEP
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.StrongLaw

/-!
# Rate-distortion achievability — Phase B (joint-typical lossy encoder + distortion typical set)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)
Phase B MVP. Two pieces of infrastructure for the lossy compression chain.

## Phase B.1 — joint-typical lossy encoder

Symmetric counterpart to `ChannelCodingAchievability.jointTypicalDecoder` on the encoder
side of the lossy compression chain:

* `jointTypicalLossyEncoder` — given a codebook `c : Codebook M n β` and a source word
  `x : Fin n → α`, returns *some* (`Classical.choose`) message index `m` with
  `(x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε`. Falls back to `⟨0, hM⟩` if no such `m` exists.
* `lossyCodeOfCodebook` — bundles the joint-typical encoder + the codebook itself as
  decoder into a `LossyCode M n α β`.
* `jointTypicalLossyEncoder_spec_of_exists` / `_of_not_exists` — `dif_pos` / `dif_neg`
  characterisations of the two branches.

Note: unlike the channel-coding decoder side (`jointTypicalDecoder`), the lossy encoder
does **not** require uniqueness of the typical match — any one is fine because the
encoder's job is only to commit to a single index. Hence we use `Classical.choose`
of `∃ m, _` rather than `Classical.choose` of `∃! m, _`.

## Phase B.3 — distortion typical set

The intersection of `jointlyTypicalSet` with the empirical-distortion constraint
`blockDistortion d n x y ≤ 𝔼[d(X_0, Y_0)] + δ`:

* `expectedJointDistortion μ X Y d` — Bochner integral of `d(X, Y)` under `μ`.
* `distortionTypicalSet μ Xs Ys d n ε δ` — set of `(x, y)` jointly typical *and*
  whose empirical block distortion is within `δ` of the joint expectation.
* basic structure lemmas: subset to `jointlyTypicalSet`, membership iff,
  `MeasurableSet`, finiteness.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding (Codebook jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- **Joint-typical lossy encoder.** Given a codebook `c : Codebook M n β`,
returns the first (any) message index `m` whose codeword is jointly typical with the
source word `x`. Falls back to `⟨0, hM⟩` if no such `m` exists. -/
noncomputable def jointTypicalLossyEncoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    (Fin n → α) → Fin M := fun x =>
  haveI : Decidable (∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h
    else ⟨0, hM⟩

/-- Bundle a codebook + joint-typical lossy encoder into a `LossyCode`. The codebook
itself serves as the decoder. -/
noncomputable def lossyCodeOfCodebook
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    LossyCode M n α β where
  encoder := jointTypicalLossyEncoder μ Xs Ys hM ε c
  decoder := c

/-- If a typical match exists for `x`, the joint-typical lossy encoder returns one. -/
theorem jointTypicalLossyEncoder_spec_of_exists
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β)
    (x : Fin n → α)
    (h : ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε) :
    (x, c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
      ∈ jointlyTypicalSet μ Xs Ys n ε := by
  unfold jointTypicalLossyEncoder
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- If no typical match exists for `x`, the joint-typical lossy encoder returns the
fallback `⟨0, hM⟩`. -/
theorem jointTypicalLossyEncoder_spec_of_not_exists
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β)
    (x : Fin n → α)
    (h : ¬ ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε) :
    jointTypicalLossyEncoder μ Xs Ys hM ε c x = ⟨0, hM⟩ := by
  unfold jointTypicalLossyEncoder
  exact dif_neg h

/-! ## Phase B.3 — distortion typical set -/

/-- Expected per-symbol distortion `𝔼_μ[d(X, Y)]` as a real Bochner integral. The
bound used in `distortionTypicalSet` references this quantity at `i = 0`; under
stationary i.i.d. hypotheses it is independent of `i`. -/
noncomputable def expectedJointDistortion
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (d : DistortionFn α β) : ℝ :=
  ∫ ω, ((d (X ω) (Y ω) : NNReal) : ℝ) ∂μ

/-- **Distortion typical set.** Pairs `(x, y) ∈ (Fin n → α) × (Fin n → β)` that are
both (a) jointly typical in the entropy sense (`jointlyTypicalSet μ Xs Ys n ε`) and
(b) whose empirical block distortion is within `δ` of the joint expectation
`𝔼[d(X_0, Y_0)]`. The set used by Cover-Thomas 10.5 to bound the distortion on
encoder-success events. -/
noncomputable def distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    Set ((Fin n → α) × (Fin n → β)) :=
  jointlyTypicalSet μ Xs Ys n ε ∩
    {p | blockDistortion d n p.1 p.2
          ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ}

/-- Membership predicate for `distortionTypicalSet`, split into the two component
conditions. -/
theorem mem_distortionTypicalSet_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ)
    (x : Fin n → α) (y : Fin n → β) :
    (x, y) ∈ distortionTypicalSet μ Xs Ys d n ε δ ↔
      (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε ∧
      blockDistortion d n x y
        ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ := Iff.rfl

/-- `distortionTypicalSet ⊆ jointlyTypicalSet`. -/
theorem distortionTypicalSet_subset_jointlyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    distortionTypicalSet μ Xs Ys d n ε δ ⊆ jointlyTypicalSet μ Xs Ys n ε :=
  fun _ h => h.1

/-- Joint typicality follows from membership in `distortionTypicalSet`. -/
theorem mem_jointlyTypicalSet_of_mem_distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ)
    {p : (Fin n → α) × (Fin n → β)}
    (h : p ∈ distortionTypicalSet μ Xs Ys d n ε δ) :
    p ∈ jointlyTypicalSet μ Xs Ys n ε := h.1

/-- **B.2.1**: on `distortionTypicalSet`, the empirical block distortion is bounded
by the joint expectation plus `δ`. This is the structural fact that drives the
distortion bound on encoder-success events in Cover-Thomas 10.5 (10.85). -/
theorem blockDistortion_le_of_mem_distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ)
    {p : (Fin n → α) × (Fin n → β)}
    (h : p ∈ distortionTypicalSet μ Xs Ys d n ε δ) :
    blockDistortion d n p.1 p.2
      ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ := h.2

/-- `distortionTypicalSet` is finite (subset of a finite ambient `(Fin n → α) × (Fin n → β)`). -/
theorem distortionTypicalSet_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    (distortionTypicalSet μ Xs Ys d n ε δ).Finite :=
  Set.toFinite _

/-- `distortionTypicalSet` is measurable (subset of a finite ambient). -/
theorem measurableSet_distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    MeasurableSet (distortionTypicalSet μ Xs Ys d n ε δ) :=
  (distortionTypicalSet_finite μ Xs Ys d n ε δ).measurableSet

/-! ## Phase B.3 — WLLN on distortion (skeleton) -/

/-- Alphabet-side distortion `(a, b) ↦ (d a b : ℝ)`. Measurable on the finite product
alphabet `α × β`. -/
noncomputable def distortionRealFn (d : DistortionFn α β) : α × β → ℝ :=
  fun p => ((d p.1 p.2 : NNReal) : ℝ)

lemma measurable_distortionRealFn (d : DistortionFn α β) :
    Measurable (distortionRealFn d) := measurable_of_finite _

/-- Per-symbol distortion random variable `ω ↦ (d (Xs i ω) (Ys i ω) : ℝ)`. -/
noncomputable def distortionRV
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (d : DistortionFn α β) (i : ℕ) : Ω → ℝ :=
  fun ω => ((d (Xs i ω) (Ys i ω) : NNReal) : ℝ)

lemma distortionRV_eq_comp
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (d : DistortionFn α β) (i : ℕ) :
    distortionRV Xs Ys d i =
      distortionRealFn d ∘
        InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i := rfl

lemma measurable_distortionRV
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (d : DistortionFn α β) (i : ℕ) :
    Measurable (distortionRV Xs Ys d i) :=
  (measurable_distortionRealFn d).comp
    (InformationTheory.Shannon.ChannelCoding.measurable_jointSequence Xs Ys hXs hYs i)

/-- Distortion RVs are integrable on a finite alphabet under a probability measure. -/
lemma integrable_distortionRV
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (d : DistortionFn α β) (i : ℕ) :
    Integrable (distortionRV Xs Ys d i) μ := by
  have hZ : Measurable
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i) :=
    InformationTheory.Shannon.ChannelCoding.measurable_jointSequence Xs Ys hXs hYs i
  have hμmap : IsProbabilityMeasure
      (μ.map (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i)) :=
    Measure.isProbabilityMeasure_map hZ.aemeasurable
  have h_int : Integrable (distortionRealFn d)
      (μ.map (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i)) :=
    Integrable.of_finite
  simpa [distortionRV_eq_comp] using h_int.comp_measurable hZ

/-- The expectation of `distortionRV Xs Ys d 0` is `expectedJointDistortion μ (Xs 0) (Ys 0) d`. -/
lemma integral_distortionRV_zero
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (d : DistortionFn α β) :
    ∫ ω, distortionRV Xs Ys d 0 ω ∂μ
      = expectedJointDistortion μ (Xs 0) (Ys 0) d := rfl

/-- Composition lift of `IdentDistrib` from `jointSequence` to `distortionRV`. -/
lemma identDistrib_distortionRV
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (d : DistortionFn α β)
    (hidentZ : ∀ i, IdentDistrib
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i)
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys 0) μ μ) (i : ℕ) :
    IdentDistrib (distortionRV Xs Ys d i) (distortionRV Xs Ys d 0) μ μ := by
  simpa [distortionRV_eq_comp] using (hidentZ i).comp (measurable_distortionRealFn d)

/-- Composition lift of pairwise `IndepFun` from `jointSequence` to `distortionRV`. -/
lemma indepFun_distortionRV
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (d : DistortionFn α β)
    (hindepZ : Pairwise fun i j =>
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i ⟂ᵢ[μ]
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys j) :
    Pairwise fun i j =>
      distortionRV Xs Ys d i ⟂ᵢ[μ] distortionRV Xs Ys d j := by
  intro i j hij
  have h := hindepZ hij
  have hpf := measurable_distortionRealFn d
  simpa [distortionRV_eq_comp] using h.comp hpf hpf

/-- **WLLN on distortion — a.s. version**. The empirical block distortion
`(1/n) ∑ i, d(Xs i ω, Ys i ω)` converges a.s. to `𝔼[d(X_0, Y_0)]`. -/
theorem distortionEmpirical_tendsto_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (d : DistortionFn α β)
    (hindepZ : Pairwise fun i j =>
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i ⟂ᵢ[μ]
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys j)
    (hidentZ : ∀ i, IdentDistrib
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i)
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
      Filter.atTop
      (𝓝 (expectedJointDistortion μ (Xs 0) (Ys 0) d)) := by
  have hint : Integrable (distortionRV Xs Ys d 0) μ :=
    integrable_distortionRV μ Xs Ys hXs hYs d 0
  have hind := indepFun_distortionRV μ Xs Ys d hindepZ
  have hid := identDistrib_distortionRV μ Xs Ys d hidentZ
  have h_lln :=
    ProbabilityTheory.strong_law_ae_real (distortionRV Xs Ys d) hint hind hid
  have h_int_eq := integral_distortionRV_zero μ Xs Ys d
  filter_upwards [h_lln] with ω hω
  simpa [h_int_eq] using hω

/-- **WLLN on distortion — convergence in probability**. -/
theorem distortionEmpirical_inProbability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (d : DistortionFn α β)
    (hindepZ : Pairwise fun i j =>
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i ⟂ᵢ[μ]
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys j)
    (hidentZ : ∀ i, IdentDistrib
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i)
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys 0) μ μ)
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n : ℕ => μ {ω | δ ≤ |((∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
                                  - expectedJointDistortion μ (Xs 0) (Ys 0) d|})
      Filter.atTop
      (𝓝 0) := by
  set f : ℕ → Ω → ℝ :=
    fun n ω => (∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n with hf_def
  set g : Ω → ℝ := fun _ => expectedJointDistortion μ (Xs 0) (Ys 0) d with hg_def
  have h_meas_f : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_distortionRV Xs Ys hXs hYs d i
    have h_meas : Measurable (f n) := by
      change Measurable (fun ω => (∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
      exact h_sum_meas.div_const _
    exact h_meas.aestronglyMeasurable
  have h_ae :=
    distortionEmpirical_tendsto_ae μ Xs Ys hXs hYs d hindepZ hidentZ
  have h_ae' : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω)) := h_ae
  have h_inm : MeasureTheory.TendstoInMeasure μ f Filter.atTop g :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae h_meas_f h_ae'
  rw [MeasureTheory.tendstoInMeasure_iff_dist] at h_inm
  have h_target := h_inm δ hδ
  refine Filter.Tendsto.congr (fun n => ?_) h_target
  apply congrArg μ
  ext ω
  show δ ≤ dist (f n ω) (g ω) ↔ δ ≤ |f n ω - g ω|
  rw [Real.dist_eq]

/-- Bridge: empirical block distortion of `(jointRV Xs n ω, jointRV Ys n ω)` equals
the Cesàro mean of `distortionRV` over `Finset.range n`. -/
lemma blockDistortion_jointRV_eq
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (d : DistortionFn α β) (n : ℕ) (ω : Ω) :
    blockDistortion d n
      (InformationTheory.Shannon.jointRV Xs n ω)
      (InformationTheory.Shannon.jointRV Ys n ω)
    = (∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / (n : ℝ) := by
  show (1 / (n : ℝ)) *
      (∑ i : Fin n, ((d (Xs ↑i ω) (Ys ↑i ω) : NNReal) : ℝ))
    = (∑ i ∈ Finset.range n, ((d (Xs i ω) (Ys i ω) : NNReal) : ℝ)) / (n : ℝ)
  rw [Fin.sum_univ_eq_sum_range (fun i => ((d (Xs i ω) (Ys i ω) : NNReal) : ℝ))]
  ring

/-- **Distortion typical set probability → 1.** Combining `jointlyTypicalSet_prob_tendsto_one`
with the WLLN on `d ∘ (Xs, Ys)` (i.e. `distortionEmpirical_inProbability`) via a
union-bound on complements. This is the AEP-style bound needed in Cover-Thomas
10.5 to control the joint probability of typical + bounded-distortion events.

The proof uses inclusion `goodJ n ∩ (bigBad n)ᶜ ⊆ targetEvt n` (only one direction
of inclusion holds because `distortionTypicalSet` uses the one-sided bound
`blockDistortion ≤ E + δ` while `bigBad` uses the symmetric `|empirical - E| ≥ δ`).
The complement squeeze pattern from `ChannelCoding.jointlyTypicalSet_prob_tendsto_one`
discharges the combined `→ 1` limit. -/
theorem distortionTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i ⟂ᵢ[μ]
      InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys j)
    (hidentZ : ∀ i, IdentDistrib
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys i)
      (InformationTheory.Shannon.ChannelCoding.jointSequence Xs Ys 0) μ μ)
    (d : DistortionFn α β) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n : ℕ => μ {ω |
        (InformationTheory.Shannon.jointRV Xs n ω,
         InformationTheory.Shannon.jointRV Ys n ω) ∈
          distortionTypicalSet μ Xs Ys d n ε δ})
      Filter.atTop
      (𝓝 1) := by
  classical
  -- Single-axis events.
  set goodJ : ℕ → Set Ω := fun n =>
    {ω | (InformationTheory.Shannon.jointRV Xs n ω,
          InformationTheory.Shannon.jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}
  set bigBad : ℕ → Set Ω := fun n =>
    {ω | δ ≤ |((∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
                  - expectedJointDistortion μ (Xs 0) (Ys 0) d|}
  set targetEvt : ℕ → Set Ω := fun n =>
    {ω | (InformationTheory.Shannon.jointRV Xs n ω,
          InformationTheory.Shannon.jointRV Ys n ω) ∈
          distortionTypicalSet μ Xs Ys d n ε δ}
  -- Measurability of `goodJ n` and `bigBad n`.
  have h_meas_goodJ : ∀ n, MeasurableSet (goodJ n) := by
    intro n
    have h_set : MeasurableSet (jointlyTypicalSet μ Xs Ys n ε) :=
      InformationTheory.Shannon.ChannelCoding.measurableSet_jointlyTypicalSet
        μ Xs Ys n ε
    refine MeasurableSet.preimage h_set ?_
    exact ((InformationTheory.Shannon.measurable_jointRV Xs hXs n).prodMk
      (InformationTheory.Shannon.measurable_jointRV Ys hYs n))
  have h_meas_bigBad : ∀ n, MeasurableSet (bigBad n) := by
    intro n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_distortionRV Xs Ys hXs hYs d i
    have h_div : Measurable
        (fun ω => (∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / (n : ℝ)) :=
      h_sum_meas.div_const _
    have h_diff : Measurable
        (fun ω => ((∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
                    - expectedJointDistortion μ (Xs 0) (Ys 0) d) :=
      h_div.sub_const _
    have h_abs : Measurable
        (fun ω => |((∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
                    - expectedJointDistortion μ (Xs 0) (Ys 0) d|) :=
      _root_.continuous_abs.measurable.comp h_diff
    exact measurableSet_le measurable_const h_abs
  have h_meas_targetEvt : ∀ n, MeasurableSet (targetEvt n) := by
    intro n
    have h_set : MeasurableSet (distortionTypicalSet μ Xs Ys d n ε δ) :=
      measurableSet_distortionTypicalSet μ Xs Ys d n ε δ
    refine MeasurableSet.preimage h_set ?_
    exact ((InformationTheory.Shannon.measurable_jointRV Xs hXs n).prodMk
      (InformationTheory.Shannon.measurable_jointRV Ys hYs n))
  -- Key inclusion: goodJ ∩ (bigBad)ᶜ ⊆ targetEvt.
  have h_subset : ∀ n, goodJ n ∩ (bigBad n)ᶜ ⊆ targetEvt n := by
    intro n ω hω
    obtain ⟨hJ, hD⟩ := hω
    refine ⟨hJ, ?_⟩
    show blockDistortion d n
        (InformationTheory.Shannon.jointRV Xs n ω)
        (InformationTheory.Shannon.jointRV Ys n ω)
      ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ
    rw [blockDistortion_jointRV_eq Xs Ys d n ω]
    have h1 : |((∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
                - expectedJointDistortion μ (Xs 0) (Ys 0) d| < δ := by
      rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hD
      exact hD
    have h2 : ((∑ i ∈ Finset.range n, distortionRV Xs Ys d i ω) / n)
                - expectedJointDistortion μ (Xs 0) (Ys 0) d < δ :=
      lt_of_abs_lt h1
    linarith
  -- Convert μ(goodJ) → 1 to μ((goodJ)ᶜ) → 0.
  have h_goodJ_to_one :=
    InformationTheory.Shannon.ChannelCoding.jointlyTypicalSet_prob_tendsto_one
      μ Xs Ys hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ hε
  have h_badJ_to_zero : Filter.Tendsto (fun n => μ ((goodJ n)ᶜ)) Filter.atTop (𝓝 0) := by
    have h_id : ∀ n, μ ((goodJ n)ᶜ) = 1 - μ (goodJ n) := fun n => by
      rw [measure_compl (h_meas_goodJ n) (measure_ne_top μ _), measure_univ]
    refine Filter.Tendsto.congr (fun n => (h_id n).symm) ?_
    have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ (goodJ n)) Filter.atTop
        (𝓝 ((1 : ℝ≥0∞) - 1)) := h_cont.tendsto _ |>.comp h_goodJ_to_one
    simpa using h_step
  -- μ(bigBad) → 0 directly from distortionEmpirical_inProbability.
  have h_badD_to_zero : Filter.Tendsto (fun n => μ (bigBad n)) Filter.atTop (𝓝 0) :=
    distortionEmpirical_inProbability μ Xs Ys hXs hYs d hindepZ hidentZ hδ
  -- μ((targetEvt n)ᶜ) ≤ μ((goodJ n)ᶜ ∪ bigBad n) ≤ μ((goodJ n)ᶜ) + μ(bigBad n) → 0.
  have h_compl_sub : ∀ n, (targetEvt n)ᶜ ⊆ (goodJ n)ᶜ ∪ bigBad n := by
    intro n ω hω
    have h_target_sub : (goodJ n ∩ (bigBad n)ᶜ) ⊆ targetEvt n := h_subset n
    have h_compl_step : (targetEvt n)ᶜ ⊆ (goodJ n ∩ (bigBad n)ᶜ)ᶜ :=
      Set.compl_subset_compl.mpr h_target_sub
    have hω' : ω ∈ (goodJ n ∩ (bigBad n)ᶜ)ᶜ := h_compl_step hω
    rw [Set.compl_inter, compl_compl] at hω'
    exact hω'
  have h_bound_compl : ∀ n,
      μ ((targetEvt n)ᶜ) ≤ μ ((goodJ n)ᶜ) + μ (bigBad n) := fun n =>
    calc μ ((targetEvt n)ᶜ)
        ≤ μ ((goodJ n)ᶜ ∪ bigBad n) := measure_mono (h_compl_sub n)
      _ ≤ μ ((goodJ n)ᶜ) + μ (bigBad n) := measure_union_le _ _
  have h_sum_to_zero :
      Filter.Tendsto (fun n => μ ((goodJ n)ᶜ) + μ (bigBad n)) Filter.atTop (𝓝 0) := by
    have h := h_badJ_to_zero.add h_badD_to_zero
    simpa using h
  have h_compl_to_zero :
      Filter.Tendsto (fun n => μ ((targetEvt n)ᶜ)) Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_sum_to_zero (fun n => bot_le) h_bound_compl
  -- Final: μ(targetEvt n) = 1 - μ((targetEvt n)ᶜ) → 1 - 0 = 1.
  have h_id_target : ∀ n, μ (targetEvt n) = 1 - μ ((targetEvt n)ᶜ) := fun n => by
    rw [measure_compl (h_meas_targetEvt n) (measure_ne_top μ _), measure_univ]
    have h_le : μ (targetEvt n) ≤ 1 := prob_le_one
    exact (ENNReal.sub_sub_cancel (by simp) h_le).symm
  refine Filter.Tendsto.congr (fun n => (h_id_target n).symm) ?_
  have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
    ENNReal.continuous_sub_left (by simp)
  have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ ((targetEvt n)ᶜ)) Filter.atTop
      (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_compl_to_zero
  simpa using h_step

end InformationTheory.Shannon
