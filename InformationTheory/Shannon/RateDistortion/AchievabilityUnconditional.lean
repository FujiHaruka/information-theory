import InformationTheory.Shannon.RateDistortion.AchievabilityJointStrongTypicality
import InformationTheory.Shannon.StrongTypicality

/-!
# Rate-distortion achievability — strong-typical ⊆ distortion-typical inclusion

This file proves the "Piece C" inclusion of the unconditional rate-distortion
achievability programme (`docs/shannon/rate-distortion-achievability-unconditional-plan.md`):
a joint strongly-typical pair is distortion-typical,

  `jointStronglyTypicalSet μ Xs Ys n ε_join
      ⊆ distortionTypicalSet μ Xs Ys d n ε_dist δ_typ`.

Since `distortionTypicalSet = jointlyTypicalSet ∩ {blockDistortion ≤ 𝔼[d] + δ}`
(`AchievabilityJointTypicalEncoder.lean`), the inclusion factors into two parts:

* (i) `jointStronglyTypicalSet ⊆ jointlyTypicalSet` — strong (per-symbol type
  deviation) typicality implies weak (entropy) typicality, via the existing
  strong-to-weak bridge `stronglyTypicalSet_subset_typicalSet` on each of the
  X-, Y-, and joint axes;
* (ii) on a strongly-typical pair, the empirical block distortion stays within
  `ε_join · ∑ d` of the expected joint distortion, because
  `|typeCount/n − q| ≤ ε_join` at every letter.

The `ε_join ↔ ε_dist` bounds (i) and the distortion slack `δ_typ ≥ ε_join · ∑ d`
(ii) are exposed as explicit hypotheses: they are the slack quantities the caller
selects in the surrounding achievability wrapper, not the analytic core.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.),
  Wiley, 2006. Theorem 10.5.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Filter Real
open InformationTheory.Shannon.ChannelCoding
  (jointSequence jointSequence_apply measurable_jointSequence jointlyTypicalSet
   mem_jointlyTypicalSet_iff)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-! ## Part (ii): empirical block distortion stays in the distortion band -/

/-- Method-of-types regrouping: summing a per-symbol statistic over the
coordinates of `z : Fin m → T` equals summing over the alphabet weighted by the
empirical type counts. -/
private lemma sum_comp_eq_typeCount_mul {T : Type*} [Fintype T] [DecidableEq T] {m : ℕ}
    (z : Fin m → T) (f : T → ℝ) :
    ∑ i, f (z i) = ∑ p : T, (typeCount z p : ℝ) * f p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin m)))
        (t := (Finset.univ : Finset T)) (g := z) (fun i _ ↦ Finset.mem_univ _) f]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

private lemma expectedJointDistortion_eq_sum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (d : DistortionFn α β) :
    expectedJointDistortion μ (Xs 0) (Ys 0) d
      = ∑ p : α × β,
          (μ.map (jointSequence Xs Ys 0)).real {p} * ((d p.1 p.2 : NNReal) : ℝ) := by
  have hZ0 : Measurable (jointSequence Xs Ys 0) := measurable_jointSequence Xs Ys hXs hYs 0
  have hmap : IsProbabilityMeasure (μ.map (jointSequence Xs Ys 0)) :=
    Measure.isProbabilityMeasure_map hZ0.aemeasurable
  have h1 : expectedJointDistortion μ (Xs 0) (Ys 0) d
      = ∫ p, ((d p.1 p.2 : NNReal) : ℝ) ∂(μ.map (jointSequence Xs Ys 0)) := by
    rw [show expectedJointDistortion μ (Xs 0) (Ys 0) d
          = ∫ ω, ((d (jointSequence Xs Ys 0 ω).1 (jointSequence Xs Ys 0 ω).2
                    : NNReal) : ℝ) ∂μ from rfl]
    exact (integral_map hZ0.aemeasurable
      (measurable_of_finite (fun p : α × β ↦ ((d p.1 p.2 : NNReal) : ℝ))).aestronglyMeasurable).symm
  rw [h1, integral_fintype (μ := μ.map (jointSequence Xs Ys 0)) Integrable.of_finite]
  simp only [smul_eq_mul]

theorem blockDistortion_le_of_mem_jointStronglyTypicalSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (d : DistortionFn α β) {n : ℕ} (hn : 0 < n) {ε_join : ℝ} (hε_join : 0 ≤ ε_join)
    {x : Fin n → α} {y : Fin n → β}
    (hxy : (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε_join) :
    blockDistortion d n x y
      ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d
          + ε_join * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) := by
  classical
  set z : Fin n → α × β := fun i ↦ (x i, y i) with hz_def
  set q : α × β → ℝ := fun p ↦ (μ.map (jointSequence Xs Ys 0)).real {p} with hq_def
  set g : α × β → ℝ := fun p ↦ ((d p.1 p.2 : NNReal) : ℝ) with hg_def
  rw [mem_jointStronglyTypicalSet_iff, mem_stronglyTypicalSet_iff] at hxy
  -- hxy : ∀ p, |(typeCount z p : ℝ)/n - q p| ≤ ε_join
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Step A: blockDistortion = ∑ p, (typeCount z p / n) * g p.
  have hbd : blockDistortion d n x y
      = ∑ p : α × β, ((typeCount z p : ℝ) / n) * g p := by
    rw [blockDistortion, sum_comp_eq_typeCount_mul z g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    ring
  -- Step B: expectedJointDistortion = ∑ p, q p * g p.
  have hexp : expectedJointDistortion μ (Xs 0) (Ys 0) d = ∑ p : α × β, q p * g p :=
    expectedJointDistortion_eq_sum μ Xs Ys hXs hYs d
  rw [hbd, hexp]
  -- Step C: deviation bound.
  have h_dev : (∑ p : α × β, ((typeCount z p : ℝ) / n) * g p)
      - (∑ p : α × β, q p * g p) ≤ ε_join * ∑ p : α × β, g p := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ p : α × β, (((typeCount z p : ℝ) / n) * g p - q p * g p)
        = ∑ p : α × β, ((typeCount z p : ℝ) / n - q p) * g p := by
          refine Finset.sum_congr rfl fun p _ ↦ ?_; ring
      _ ≤ ∑ p : α × β, |((typeCount z p : ℝ) / n - q p)| * g p := by
          refine Finset.sum_le_sum fun p _ ↦ ?_
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (NNReal.coe_nonneg _)
      _ ≤ ∑ p : α × β, ε_join * g p := by
          refine Finset.sum_le_sum fun p _ ↦ ?_
          exact mul_le_mul_of_nonneg_right (hxy p) (NNReal.coe_nonneg _)
      _ = ε_join * ∑ p : α × β, g p := by rw [Finset.mul_sum]
  linarith [h_dev]

/-! ## Part (i): joint strong typicality implies joint (weak) typicality -/

theorem jointStronglyTypicalSet_subset_jointlyTypicalSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {n : ℕ} (hn : 0 < n) {ε_join ε_dist : ℝ} (hε_join : 0 ≤ ε_join)
    (h_bound_X : (Fintype.card β : ℝ) * ε_join * logSumAbs μ Xs < ε_dist)
    (h_bound_Y : (Fintype.card α : ℝ) * ε_join * logSumAbs μ Ys < ε_dist)
    (h_bound_Z : ε_join * logSumAbs μ (jointSequence Xs Ys) < ε_dist) :
    jointStronglyTypicalSet μ Xs Ys n ε_join ⊆ jointlyTypicalSet μ Xs Ys n ε_dist := by
  rintro ⟨x, y⟩ hp
  rw [mem_jointlyTypicalSet_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- X-typical
    have hxX : x ∈ stronglyTypicalSet μ Xs n ((Fintype.card β : ℝ) * ε_join) :=
      jointStronglyTypicalSet_implies_X_stronglyTypical μ Xs Ys hXs hYs hmarg_X hn hε_join x y hp
    exact stronglyTypicalSet_subset_typicalSet μ Xs hXs hn h_bound_X hxX
  · -- Y-typical
    have hyY : y ∈ stronglyTypicalSet μ Ys n ((Fintype.card α : ℝ) * ε_join) :=
      jointStronglyTypicalSet_implies_Y_stronglyTypical μ Xs Ys hXs hYs hmarg_Y hn hε_join x y hp
    exact stronglyTypicalSet_subset_typicalSet μ Ys hYs hn h_bound_Y hyY
  · -- joint-typical
    have hZ : (fun i ↦ (x i, y i)) ∈ stronglyTypicalSet μ (jointSequence Xs Ys) n ε_join := by
      rw [mem_jointStronglyTypicalSet_iff] at hp; exact hp
    have hZmeas : ∀ i, Measurable (jointSequence Xs Ys i) := measurable_jointSequence Xs Ys hXs hYs
    exact stronglyTypicalSet_subset_typicalSet μ (jointSequence Xs Ys) hZmeas hn h_bound_Z hZ

/-! ## Piece C: joint strong typicality implies distortion typicality -/

/-- **Piece C** (rate-distortion unconditional achievability). A joint strongly
typical pair is distortion typical:

  `jointStronglyTypicalSet μ Xs Ys n ε_join
      ⊆ distortionTypicalSet μ Xs Ys d n ε_dist δ_typ`.

The `ε_join ↔ ε_dist` bounds (`h_bound_X/Y/Z`) and the distortion slack
`δ_typ ≥ ε_join · ∑ d` (`h_dist_slack`) are the caller-supplied slack conditions
of the surrounding achievability wrapper; the analytic content — strong-to-weak
typicality and the empirical-distortion deviation bound — is proved here. -/
theorem jts_subset_dts_of_dist_slack
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    (d : DistortionFn α β) {n : ℕ} (hn : 0 < n)
    {ε_join ε_dist δ_typ : ℝ} (hε_join : 0 ≤ ε_join)
    (h_bound_X : (Fintype.card β : ℝ) * ε_join * logSumAbs μ Xs < ε_dist)
    (h_bound_Y : (Fintype.card α : ℝ) * ε_join * logSumAbs μ Ys < ε_dist)
    (h_bound_Z : ε_join * logSumAbs μ (jointSequence Xs Ys) < ε_dist)
    (h_dist_slack : ε_join * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ_typ) :
    jointStronglyTypicalSet μ Xs Ys n ε_join
      ⊆ distortionTypicalSet μ Xs Ys d n ε_dist δ_typ := by
  rintro ⟨x, y⟩ hp
  refine ⟨?_, ?_⟩
  · exact jointStronglyTypicalSet_subset_jointlyTypicalSet μ Xs Ys hXs hYs hmarg_X hmarg_Y hn
      hε_join h_bound_X h_bound_Y h_bound_Z hp
  · change blockDistortion d n x y ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ
    have hb := blockDistortion_le_of_mem_jointStronglyTypicalSet μ Xs Ys hXs hYs d hn hε_join hp
    linarith [hb, h_dist_slack]

end InformationTheory.Shannon
