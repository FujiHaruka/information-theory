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

/-! ### Phase B.2.2 — Anti-direction (lower bound) joint-AEP indep probability

Cover-Thomas 10.5 (10.85) の核となる single-codeword typical-match probability の下界。
既存 `ChannelCoding.jointlyTypicalSet_indep_prob_le` の **anti-direction** mirror。

`jointlyTypicalSet_card_ge` は size lower bound (private helper)。
`jointlyTypicalSet_indep_prob_ge` は product law 下での JTS 確率下界 (公開)。

入力 hypothesis は **joint-law** 形 `μ.real {ω | (jX, jY) ∈ JTS} ≥ 1 - η` を取る。
これは `jointlyTypicalSet_prob_tendsto_one` (`ChannelCoding.lean:402`) が直接供給する形。
-/

/-- **Size lower bound on the jointly typical set** (mirror of
`jointlyTypicalSet_card_le`). If under joint law the event
"`(jointRV Xs n ω, jointRV Ys n ω) ∈ JTS`" has measure ≥ `1 - η`, then
`|JTS| ≥ (1 - η) · exp(n · (H(Z) - ε))`. -/
private theorem jointlyTypicalSet_card_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepZ_full : iIndepFun (fun i => ChannelCoding.jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (ChannelCoding.jointSequence Xs Ys i)
                      (ChannelCoding.jointSequence Xs Ys 0) μ μ)
    (hposZ : ∀ p : α × β,
      0 < (μ.map (ChannelCoding.jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε η : ℝ}
    (hμJTS : (1 - η) ≤ μ.real
      {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}) :
    (1 - η) * Real.exp ((n : ℝ) *
        (entropy μ (ChannelCoding.jointSequence Xs Ys 0) - ε))
      ≤ ((jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset.card : ℝ) := by
  classical
  set Zs : ℕ → Ω → α × β := ChannelCoding.jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    ChannelCoding.measurable_jointSequence Xs Ys hXs hYs i
  -- φ : (Fin n → α) × (Fin n → β) → Fin n → α × β reshapes pair into joint.
  let φ : (Fin n → α) × (Fin n → β) → (Fin n → α × β) :=
    fun p i => (p.1 i, p.2 i)
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    apply Prod.ext
    · funext i
      exact ((Prod.mk.injEq _ _ _ _).mp (congr_fun hpq i)).1
    · funext i
      exact ((Prod.mk.injEq _ _ _ _).mp (congr_fun hpq i)).2
  set JT : Finset ((Fin n → α) × (Fin n → β)) :=
    (ChannelCoding.jointlyTypicalSet_finite μ Xs Ys n ε).toFinset with hJT_def
  set H : ℝ := entropy μ (Zs 0) with hH_def
  set JTimg : Finset (Fin n → α × β) := JT.image φ with hJTimg_def
  have hJTimg_card : JTimg.card = JT.card :=
    Finset.card_image_of_injective _ hφ_inj
  -- Each q ∈ JTimg lies in typicalSet μ Zs n ε (third conjunct of JTS).
  have h_JTimg_sub_T : ∀ q ∈ JTimg, q ∈ typicalSet μ Zs n ε := by
    intro q hq
    rw [hJTimg_def, Finset.mem_image] at hq
    obtain ⟨⟨x, y⟩, hxy_mem, rfl⟩ := hq
    have hxy : (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε :=
      (Set.Finite.mem_toFinset _).mp hxy_mem
    exact hxy.2.2
  -- jointRV Zs n ω = φ (jointRV Xs n ω, jointRV Ys n ω).
  have h_jointRV_factor : ∀ ω,
      jointRV Zs n ω = φ (jointRV Xs n ω, jointRV Ys n ω) := by
    intro ω
    funext i
    rfl
  -- The joint event in Ω = preimage of (φ '' JTS) under jointRV Zs n.
  have h_event_eq : {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}
      = jointRV Zs n ⁻¹' (JTimg : Set (Fin n → α × β)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hJTimg_def, Finset.coe_image,
      Finset.mem_coe, Set.mem_image]
    constructor
    · intro h
      refine ⟨(jointRV Xs n ω, jointRV Ys n ω), ?_, ?_⟩
      · rw [hJT_def, Set.Finite.mem_toFinset]; exact h
      · exact (h_jointRV_factor ω).symm
    · rintro ⟨⟨x, y⟩, hxy_mem, hp_eq⟩
      rw [hJT_def, Set.Finite.mem_toFinset] at hxy_mem
      have h_φ_eq : φ (jointRV Xs n ω, jointRV Ys n ω) = φ (x, y) := by
        rw [← h_jointRV_factor ω]; exact hp_eq.symm
      have h_eq : (jointRV Xs n ω, jointRV Ys n ω) = (x, y) := hφ_inj h_φ_eq
      rw [h_eq]; exact hxy_mem
  -- The image is measurable (it lives in a finite ambient).
  have hJTimg_measurable : MeasurableSet (JTimg : Set (Fin n → α × β)) :=
    (Set.toFinite _).measurableSet
  -- Convert μ.real (joint event) into (μ.map jointRV Zs n).real (JTimg).
  have h_map : μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}
      = (μ.map (jointRV Zs n)).real (JTimg : Set (Fin n → α × β)) := by
    show (μ {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}).toReal
        = ((μ.map (jointRV Zs n)) (JTimg : Set _)).toReal
    rw [h_event_eq]
    congr 1
    exact (Measure.map_apply (measurable_jointRV Zs hZs n) hJTimg_measurable).symm
  -- (μ.map jointRV Zs n).real (↑JTimg) = ∑ q ∈ JTimg, μ.real {q}.
  have h_sum_decomp : (μ.map (jointRV Zs n)).real (JTimg : Set (Fin n → α × β))
      = ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q} :=
    (sum_measureReal_singleton (μ := μ.map (jointRV Zs n)) JTimg).symm
  -- Each singleton ≤ exp(-n(H - ε)) via typicalSet_prob_le on Zs.
  have h_each_le : ∀ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q}
      ≤ Real.exp (- (n : ℝ) * (H - ε)) := by
    intro q hq
    have hq_T : q ∈ typicalSet μ Zs n ε := h_JTimg_sub_T q hq
    exact InformationTheory.Shannon.typicalSet_prob_le μ Zs hZs hindepZ_full hidentZ
      hposZ n q hq_T
  have h_sum_le : ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q}
      ≤ (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := by
    calc ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q}
        ≤ ∑ _q ∈ JTimg, Real.exp (- (n : ℝ) * (H - ε)) := Finset.sum_le_sum h_each_le
      _ = (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h_combined : (1 - η) ≤ (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := by
    calc (1 - η)
        ≤ μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε} := hμJTS
      _ = (μ.map (jointRV Zs n)).real (JTimg : Set _) := h_map
      _ = ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q} := h_sum_decomp
      _ ≤ (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := h_sum_le
  -- Multiply by exp((n)(H-ε)) and cancel.
  have hexp_pos : 0 < Real.exp ((n : ℝ) * (H - ε)) := Real.exp_pos _
  have h_exp_cancel : Real.exp (- (n : ℝ) * (H - ε)) * Real.exp ((n : ℝ) * (H - ε)) = 1 := by
    rw [show -(n : ℝ) * (H - ε) = -((n : ℝ) * (H - ε)) from by ring, ← Real.exp_add]
    simp
  have h_mul := mul_le_mul_of_nonneg_right h_combined hexp_pos.le
  have h_rhs : (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε))
        * Real.exp ((n : ℝ) * (H - ε)) = (JTimg.card : ℝ) := by
    rw [mul_assoc, h_exp_cancel, mul_one]
  rw [h_rhs, hJTimg_card] at h_mul
  exact h_mul

/-- **Anti-direction (lower-bound) joint-AEP indep probability**.
The probability under the product measure `μX^n × μY^n` that `(X̃, Ỹ)` lies in
the jointly typical set is bounded **below** by `(1 - η) · exp(-n · (I + 3ε))`,
which is Cover-Thomas (10.85). Mirror of `jointlyTypicalSet_indep_prob_le`. -/
theorem jointlyTypicalSet_indep_prob_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => ChannelCoding.jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (ChannelCoding.jointSequence Xs Ys i)
                      (ChannelCoding.jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (ChannelCoding.jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε η : ℝ}
    (hμJTS : (1 - η) ≤ μ.real
      {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}) :
    (1 - η) * Real.exp ((n : ℝ) *
        (entropy μ (ChannelCoding.jointSequence Xs Ys 0)
         - entropy μ (Xs 0) - entropy μ (Ys 0) - 3 * ε))
      ≤ ((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real
          (jointlyTypicalSet μ Xs Ys n ε) := by
  classical
  set μX : Measure (Fin n → α) := μ.map (jointRV Xs n) with hμX_def
  set μY : Measure (Fin n → β) := μ.map (jointRV Ys n) with hμY_def
  set HX : ℝ := entropy μ (Xs 0) with hHX_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set HZ : ℝ := entropy μ (ChannelCoding.jointSequence Xs Ys 0) with hHZ_def
  set A : Set ((Fin n → α) × (Fin n → β)) := jointlyTypicalSet μ Xs Ys n ε with hA_def
  set Afin : Finset ((Fin n → α) × (Fin n → β)) :=
    (ChannelCoding.jointlyTypicalSet_finite μ Xs Ys n ε).toFinset with hAfin_def
  have hXmeas : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
  have hYmeas : Measurable (jointRV Ys n) := measurable_jointRV Ys hYs n
  haveI : IsProbabilityMeasure μX :=
    Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  haveI : IsProbabilityMeasure μY :=
    Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  haveI : IsProbabilityMeasure (μX.prod μY) := by
    have : IsFiniteMeasure μX := inferInstance
    have : IsFiniteMeasure μY := inferInstance
    infer_instance
  -- Step 1: rewrite (μX.prod μY).real A as a Finset sum over Afin.
  have h_sum_decomp :
      (μX.prod μY).real A
        = ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := by
    have h_real_eq : (μX.prod μY).real A = ∑ p ∈ Afin, (μX.prod μY).real {p} := by
      have h_coe : (Afin : Set _) = A :=
        (ChannelCoding.jointlyTypicalSet_finite μ Xs Ys n ε).coe_toFinset
      rw [← h_coe, ← sum_measureReal_singleton (μ := μX.prod μY) Afin]
    rw [h_real_eq]
    refine Finset.sum_congr rfl ?_
    intro p _
    have h_singleton_prod : ({p} : Set ((Fin n → α) × (Fin n → β)))
        = ({p.1} : Set (Fin n → α)) ×ˢ ({p.2} : Set (Fin n → β)) := by
      ext q
      simp [Prod.ext_iff]
    rw [h_singleton_prod]
    exact measureReal_prod_prod _ _
  -- Step 2: each summand bounded below by exp(-n(HX + ε)) · exp(-n(HY + ε)).
  have h_each_ge : ∀ p ∈ Afin,
      Real.exp (- (n : ℝ) * (HX + ε)) * Real.exp (- (n : ℝ) * (HY + ε))
        ≤ μX.real {p.1} * μY.real {p.2} := by
    intro p hp
    have hp_set : p ∈ A := (Set.Finite.mem_toFinset _).mp hp
    rcases hp_set with ⟨hxX, hyY, _hxyZ⟩
    have hbdX : Real.exp (- (n : ℝ) * (HX + ε)) ≤ μX.real {p.1} :=
      InformationTheory.Shannon.typicalSet_prob_ge μ Xs hXs hindepX_full hidentX
        hposX n p.1 hxX
    have hbdY : Real.exp (- (n : ℝ) * (HY + ε)) ≤ μY.real {p.2} :=
      InformationTheory.Shannon.typicalSet_prob_ge μ Ys hYs hindepY_full hidentY
        hposY n p.2 hyY
    have hY_exp_nn : 0 ≤ Real.exp (- (n : ℝ) * (HY + ε)) := (Real.exp_pos _).le
    have hX_exp_nn : 0 ≤ Real.exp (- (n : ℝ) * (HX + ε)) := (Real.exp_pos _).le
    have hX_nn : 0 ≤ μX.real {p.1} := measureReal_nonneg
    calc Real.exp (- (n : ℝ) * (HX + ε)) * Real.exp (- (n : ℝ) * (HY + ε))
        ≤ μX.real {p.1} * Real.exp (- (n : ℝ) * (HY + ε)) := by
          exact mul_le_mul_of_nonneg_right hbdX hY_exp_nn
      _ ≤ μX.real {p.1} * μY.real {p.2} := by
          exact mul_le_mul_of_nonneg_left hbdY hX_nn
  -- Step 3: lower bound the sum by card · C.
  set C : ℝ := Real.exp (- (n : ℝ) * (HX + ε)) * Real.exp (- (n : ℝ) * (HY + ε))
    with hC_def
  have hC_nn : 0 ≤ C := by
    simp only [hC_def]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have h_sum_ge : (Afin.card : ℝ) * C
      ≤ ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := by
    calc (Afin.card : ℝ) * C
        = ∑ _p ∈ Afin, C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := Finset.sum_le_sum h_each_ge
  -- Step 4: card lower bound via jointlyTypicalSet_card_ge.
  have h_card_ge : (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) ≤ (Afin.card : ℝ) := by
    have := jointlyTypicalSet_card_ge μ Xs Ys hXs hYs hindepZ_full hidentZ hposZ n
      (ε := ε) (η := η) hμJTS
    -- The goal uses Afin which is by hAfin_def equal to (jTS).toFinite.toFinset.
    convert this using 1
  -- Step 5: combine.
  have h_lhs_eq :
      (1 - η) * Real.exp ((n : ℝ) * ((HZ - HX - HY) - 3 * ε))
        = (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) * C := by
    have h_C_expand : C
        = Real.exp (- (n : ℝ) * (HX + ε) + - (n : ℝ) * (HY + ε)) := by
      rw [hC_def, ← Real.exp_add]
    rw [h_C_expand]
    rw [show (1 - η) * Real.exp ((n : ℝ) * (HZ - ε))
          * Real.exp (- (n : ℝ) * (HX + ε) + - (n : ℝ) * (HY + ε))
        = (1 - η) * (Real.exp ((n : ℝ) * (HZ - ε))
            * Real.exp (- (n : ℝ) * (HX + ε) + - (n : ℝ) * (HY + ε))) from by ring]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have h_card_mul_C : (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) * C
      ≤ (Afin.card : ℝ) * C := mul_le_mul_of_nonneg_right h_card_ge hC_nn
  calc (1 - η) * Real.exp ((n : ℝ) * ((HZ - HX - HY) - 3 * ε))
      = (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) * C := h_lhs_eq
    _ ≤ (Afin.card : ℝ) * C := h_card_mul_C
    _ ≤ ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := h_sum_ge
    _ = (μX.prod μY).real A := h_sum_decomp.symm

end InformationTheory.Shannon
