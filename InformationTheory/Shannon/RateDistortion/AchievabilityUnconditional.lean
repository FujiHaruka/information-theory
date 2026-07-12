import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.RateDistortion.AchievabilityJointStrongTypicality
import InformationTheory.Shannon.RateDistortion.AchievabilityStrongTypicality
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
   mem_jointlyTypicalSet_iff iidXs iidYs measurable_iidXs measurable_iidYs
   pmfToMeasure pmfToMeasure_isProbabilityMeasure pmfToMeasure_real_singleton)
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

/-! ## Piece B: marginal-preserving full-support perturbation

The strong-typicality achievability theorem requires a strictly-positive optimal
joint pmf. Starting from a minimizer `qStar ∈ RDConstraint P_X d D` (which may sit
on the boundary of the simplex), we perturb it toward the product `P_X ⊗ uniform_β`,

  `q'(a, b) := (1 - λ) · qStar(a, b) + λ · P_X(a) / |β|`.

For a full-support source `P_X` and `0 < λ ≤ 1` this is strictly positive
everywhere, keeps the source marginal equal to `P_X`, and — by continuity in `λ`
at `λ = 0` — keeps mutual information below `R` and expected distortion within
`ε/4` of the constraint value. -/

/-- Marginal-preserving perturbation of a joint pmf `qStar` toward the product
`P_X ⊗ uniform_β`: `q'(a,b) := (1-λ)·qStar(a,b) + λ·P_X(a)/|β|`. For `0 < λ ≤ 1`
and a full-support source `P_X`, this is strictly positive at every point while
keeping the source marginal equal to `P_X`. -/
noncomputable def rdPerturb (qStar : α × β → ℝ) (P_X : α → ℝ) (lam : ℝ) :
    α × β → ℝ :=
  fun p ↦ (1 - lam) * qStar p + lam * (P_X p.1 / (Fintype.card β : ℝ))

/-- Continuity gateway: a continuous scalar `g` with `g 0 < c` stays `< c` on a
right-neighborhood `(0, λ₀]` of `0` (with `λ₀ ≤ 1`). Used to transport the strict
inequalities `I(qStar) < R` and `𝔼[d](qStar) < D + ε/4` from `λ = 0` to small
positive `λ` along the perturbation path. -/
private lemma exists_lam_forall_lt_of_continuous
    {g : ℝ → ℝ} (hg : Continuous g) {c : ℝ} (h0 : g 0 < c) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam, 0 < lam → lam ≤ lam₀ → g lam < c := by
  have hopen : IsOpen {x : ℝ | g x < c} := isOpen_lt hg continuous_const
  have hmem : (0 : ℝ) ∈ {x : ℝ | g x < c} := h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  refine ⟨min (δ / 2) 1, lt_min (by linarith) one_pos, min_le_right _ _, ?_⟩
  intro lam hlam_pos hlam_le
  have hlt : lam < δ := by
    have h1 : lam ≤ δ / 2 := le_trans hlam_le (min_le_left _ _)
    linarith
  have hmem' : lam ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hlam_pos]
    exact hlt
  exact hball hmem'

lemma rdPerturb_mem_stdSimplex
    {qStar : α × β → ℝ} {P_X : α → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hqStar : qStar ∈ stdSimplex ℝ (α × β))
    (hP_X : P_X ∈ stdSimplex ℝ α) :
    rdPerturb qStar P_X lam ∈ stdSimplex ℝ (α × β) := by
  have hc : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcne : (Fintype.card β : ℝ) ≠ 0 := ne_of_gt hc
  refine ⟨fun p ↦ ?_, ?_⟩
  · -- non-negativity: convex combination of non-negative terms
    have h1 : (0 : ℝ) ≤ 1 - lam := by linarith
    have hterm1 : 0 ≤ (1 - lam) * qStar p := mul_nonneg h1 (hqStar.1 p)
    have hterm2 : 0 ≤ lam * (P_X p.1 / (Fintype.card β : ℝ)) :=
      mul_nonneg hlam0 (div_nonneg (hP_X.1 p.1) (le_of_lt hc))
    exact add_nonneg hterm1 hterm2
  · -- total mass 1
    unfold rdPerturb
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hsum_P : ∑ p : α × β, P_X p.1 / (Fintype.card β : ℝ) = 1 := by
      rw [Fintype.sum_prod_type]
      have hinner : ∀ a, ∑ _b : β, P_X a / (Fintype.card β : ℝ) = P_X a := by
        intro a
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc',
          mul_div_cancel_left₀ _ hcne]
      rw [Finset.sum_congr rfl (fun a _ ↦ hinner a)]
      exact hP_X.2
    rw [hqStar.2, hsum_P]; ring

lemma rdPerturb_pos
    {qStar : α × β → ℝ} {P_X : α → ℝ} {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hqStar : qStar ∈ stdSimplex ℝ (α × β))
    (hP_supp : ∀ a, 0 < P_X a) (p : α × β) :
    0 < rdPerturb qStar P_X lam p := by
  have hc : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold rdPerturb
  -- (1-λ)·qStar p ≥ 0 supports the strictly-positive uniform term λ·P_X(a)/|β|.
  have h1 : (0 : ℝ) ≤ 1 - lam := by linarith
  have hterm1 : 0 ≤ (1 - lam) * qStar p := mul_nonneg h1 (hqStar.1 p)
  have hterm2 : 0 < lam * (P_X p.1 / (Fintype.card β : ℝ)) :=
    mul_pos hlam0 (div_pos (hP_supp p.1) hc)
  linarith

lemma rdPerturb_marginalFst
    {qStar : α × β → ℝ} {P_X : α → ℝ} {lam : ℝ}
    (hmarg : marginalFst qStar = P_X) :
    marginalFst (rdPerturb qStar P_X lam) = P_X := by
  have hc : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  funext a
  have hmarg_a : (∑ b, qStar (a, b)) = P_X a := congrFun hmarg a
  -- ∑_b [(1-λ)·qStar(a,b) + λ·P_X(a)/|β|] = (1-λ)·P_X(a) + λ·P_X(a) = P_X(a)
  show ∑ b, ((1 - lam) * qStar (a, b) + lam * (P_X a / (Fintype.card β : ℝ))) = P_X a
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hmarg_a, mul_div_assoc', mul_div_cancel_left₀ _ hc]
  ring

/-- The perturbation path `λ ↦ rdPerturb qStar P_X λ` is continuous (affine in `λ`
at every coordinate, hence continuous into the product topology on `α × β → ℝ`). -/
private lemma continuous_rdPerturb (qStar : α × β → ℝ) (P_X : α → ℝ) :
    Continuous (fun lam : ℝ ↦ (rdPerturb qStar P_X lam : α × β → ℝ)) := by
  apply continuous_pi
  intro p
  show Continuous (fun lam : ℝ ↦ (1 - lam) * qStar p + lam * (P_X p.1 / (Fintype.card β : ℝ)))
  fun_prop

private lemma rdPerturb_zero (qStar : α × β → ℝ) (P_X : α → ℝ) :
    rdPerturb qStar P_X 0 = qStar := by
  funext p; simp [rdPerturb]

lemma rdPerturb_mutualInfo_lt
    {qStar : α × β → ℝ} {P_X : α → ℝ} {R : ℝ}
    (hI : mutualInfoPmf qStar < R) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam, 0 < lam → lam ≤ lam₀ → mutualInfoPmf (rdPerturb qStar P_X lam) < R := by
  have hcont : Continuous (fun lam : ℝ ↦ mutualInfoPmf (rdPerturb qStar P_X lam)) :=
    continuous_mutualInfoPmf.comp (continuous_rdPerturb qStar P_X)
  have hg0 : mutualInfoPmf (rdPerturb qStar P_X 0) < R := by
    rw [rdPerturb_zero]; exact hI
  exact exists_lam_forall_lt_of_continuous hcont hg0

lemma rdPerturb_expectedDist_le
    {qStar : α × β → ℝ} {P_X : α → ℝ} {d : DistortionFn α β} {D ε : ℝ}
    (hE : expectedDistortionPmf d qStar ≤ D) (hε : 0 < ε) :
    ∃ lam₁ : ℝ, 0 < lam₁ ∧ lam₁ ≤ 1 ∧
      ∀ lam, 0 < lam → lam ≤ lam₁ →
        expectedDistortionPmf d (rdPerturb qStar P_X lam) ≤ D + ε / 4 := by
  have hcont : Continuous (fun lam : ℝ ↦ expectedDistortionPmf d (rdPerturb qStar P_X lam)) :=
    (continuous_expectedDistortionPmf d).comp (continuous_rdPerturb qStar P_X)
  have hg0 : expectedDistortionPmf d (rdPerturb qStar P_X 0) < D + ε / 4 := by
    rw [rdPerturb_zero]; linarith
  obtain ⟨lam₁, h1, h2, h3⟩ := exists_lam_forall_lt_of_continuous hcont hg0
  exact ⟨lam₁, h1, h2, fun lam hlp hle ↦ le_of_lt (h3 lam hlp hle)⟩

/-! ## Piece A: existence of consistent slack parameters

Given a strictly-positive joint pmf `q'` with `mutualInfoPmf q' < R` and expected
distortion within `ε/4` of the constraint, we select the five slack parameters
`ε_X, ε_join, ε_dist, δ_kl, δ_typ` (plus the KL floor `qZ_min`) that simultaneously
satisfy every hypothesis of `rate_distortion_achievability_strong` (with the
relaxation `D ↦ D + ε/4`, `ε' ↦ ε/2`) and the side conditions of Piece C
(`jts_subset_dts_of_dist_slack`). All quantities are finite constants determined
by `q'`; the selection is pure real arithmetic, not an analytic wall. -/

/-- **Piece A** (rate-distortion unconditional achievability). Slack existence:
selects `ε_X, ε_join, ε_dist, δ_kl, δ_typ, qZ_min` satisfying the rate gap,
distortion budget, strong-to-weak `ε`-bounds and the KL-floor domination. -/
lemma rdSlack_exists
    {d : DistortionFn α β} {D R ε : ℝ}
    {q' : α × β → ℝ} (hq'_simp : q' ∈ stdSimplex ℝ (α × β))
    (hq'_pos : ∀ p : α × β, 0 < q' p)
    (hI' : mutualInfoPmf q' < R)
    (hE' : expectedDistortionPmf d q' ≤ D + ε / 4)
    (hε : 0 < ε) :
    ∃ ε_X ε_join ε_dist δ_kl δ_typ qZ_min : ℝ,
      0 < ε_X ∧ 0 < ε_join ∧ 0 < ε_dist ∧ 0 < δ_kl ∧ 0 ≤ δ_typ ∧
      ε_X < ε_join ∧
      mutualInfoPmf q'
          + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient q')
                (iidYs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient q') (iidXs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient q')
                  (jointSequence (α := α) (β := β) iidXs iidYs)
              + δ_kl) < R ∧
      expectedDistortionPmf d q' + δ_typ ≤ D + ε / 4 + ε / 2 / 2 ∧
      ε_join * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ_typ ∧
      (Fintype.card β : ℝ) * ε_join * logSumAbs (rdAmbient q')
          (iidXs (α := α) (β := β)) < ε_dist ∧
      (Fintype.card α : ℝ) * ε_join * logSumAbs (rdAmbient q')
          (iidYs (α := α) (β := β)) < ε_dist ∧
      ε_join * logSumAbs (rdAmbient q')
          (jointSequence (α := α) (β := β) iidXs iidYs) < ε_dist ∧
      0 < qZ_min ∧
      (∀ p : α × β, qZ_min ≤ (pmfToMeasure (α := α × β) q').real {p}) ∧
      8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
        ≤ δ_kl * qZ_min := by
  classical
  -- KL floor `qZ_min := inf' over p of (pmfToMeasure q').real {p}`.
  set qZ_min : ℝ := Finset.univ.inf' Finset.univ_nonempty
      (fun p : α × β ↦ (pmfToMeasure (α := α × β) q').real {p}) with hqZ_def
  -- Finite constants.
  set Na : ℝ := (Fintype.card α : ℝ) with hNa_def
  set Nb : ℝ := (Fintype.card β : ℝ) with hNb_def
  set L_X : ℝ := logSumAbs (rdAmbient q') (iidXs (α := α) (β := β)) with hLX_def
  set L_Y : ℝ := logSumAbs (rdAmbient q') (iidYs (α := α) (β := β)) with hLY_def
  set L_Z : ℝ := logSumAbs (rdAmbient q')
      (jointSequence (α := α) (β := β) iidXs iidYs) with hLZ_def
  set S : ℝ := ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) with hS_def
  -- Derived positive constants.
  set K : ℝ := 8 * Na * Nb / qZ_min with hK_def
  set C_rate : ℝ := Na * |L_Y| + |L_X| + |L_Z| + 1 with hCrate_def
  -- Slack parameters.
  set ε_X : ℝ := min (min 1 ((R - mutualInfoPmf q') / (2 * (C_rate + K))))
      (ε / (8 * (S + 1))) with hεX_def
  set ε_join : ℝ := 2 * ε_X with hεjoin_def
  set δ_kl : ℝ := K * ε_X ^ 2 with hδkl_def
  set δ_typ : ℝ := ε_join * S with hδtyp_def
  set ε_dist : ℝ := Nb * ε_join * |L_X| + Na * ε_join * |L_Y| + ε_join * |L_Z| + 1
    with hεdist_def
  -- Make all quantities opaque atoms so `linarith`/`nlinarith` do not unfold the
  -- large `min`/`div`/`inf'` definitions; every property below is re-derived from
  -- the `_def` equations by `rw`.
  clear_value qZ_min Na Nb L_X L_Y L_Z S K C_rate ε_X ε_join δ_kl δ_typ ε_dist
  have hqZ_min_pos : 0 < qZ_min := by
    rw [hqZ_def, Finset.lt_inf'_iff]
    exact fun p _ ↦ pmfToMeasure_real_singleton_pos hq'_simp hq'_pos p
  have hqZ_min_le : ∀ p : α × β, qZ_min ≤ (pmfToMeasure (α := α × β) q').real {p} := by
    intro p; rw [hqZ_def]; exact Finset.inf'_le _ (Finset.mem_univ p)
  have hNa_pos : 0 < Na := by rw [hNa_def]; exact_mod_cast Fintype.card_pos
  have hNb_pos : 0 < Nb := by rw [hNb_def]; exact_mod_cast Fintype.card_pos
  have hS_nn : 0 ≤ S := by
    rw [hS_def]; exact Finset.sum_nonneg (fun p _ ↦ NNReal.coe_nonneg _)
  have hG_pos : 0 < R - mutualInfoPmf q' := by linarith only [hI']
  have hK_pos : 0 < K := by
    rw [hK_def]
    exact div_pos (mul_pos (mul_pos (by norm_num) hNa_pos) hNb_pos) hqZ_min_pos
  have hCrate_pos : 0 < C_rate := by
    rw [hCrate_def]
    have h1 : 0 ≤ Na * |L_Y| := mul_nonneg hNa_pos.le (abs_nonneg _)
    have h2 : 0 ≤ |L_X| := abs_nonneg _
    have h3 : 0 ≤ |L_Z| := abs_nonneg _
    linarith only [h1, h2, h3]
  have hCK_pos : 0 < C_rate + K := by linarith only [hCrate_pos, hK_pos]
  have hSp1_pos : 0 < 8 * (S + 1) := by linarith only [hS_nn]
  have hεX_pos : 0 < ε_X := by
    rw [hεX_def]
    exact lt_min (lt_min one_pos (div_pos hG_pos (by linarith only [hCK_pos])))
      (div_pos hε hSp1_pos)
  have hεX_le1 : ε_X ≤ 1 := by
    rw [hεX_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hεX_le_gap : ε_X ≤ (R - mutualInfoPmf q') / (2 * (C_rate + K)) := by
    rw [hεX_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεX_le_dist : ε_X ≤ ε / (8 * (S + 1)) := by
    rw [hεX_def]; exact min_le_right _ _
  have hεjoin_pos : 0 < ε_join := by rw [hεjoin_def]; linarith only [hεX_pos]
  have hδkl_pos : 0 < δ_kl := by
    rw [hδkl_def]; exact mul_pos hK_pos (pow_pos hεX_pos 2)
  have hδtyp_nn : 0 ≤ δ_typ := by
    rw [hδtyp_def]; exact mul_nonneg hεjoin_pos.le hS_nn
  have hεdist_pos : 0 < ε_dist := by
    rw [hεdist_def]
    have t1 : 0 ≤ Nb * ε_join * |L_X| :=
      mul_nonneg (mul_nonneg hNb_pos.le hεjoin_pos.le) (abs_nonneg _)
    have t2 : 0 ≤ Na * ε_join * |L_Y| :=
      mul_nonneg (mul_nonneg hNa_pos.le hεjoin_pos.le) (abs_nonneg _)
    have t3 : 0 ≤ ε_join * |L_Z| := mul_nonneg hεjoin_pos.le (abs_nonneg _)
    linarith only [t1, t2, t3]
  have hεX_lt_join : ε_X < ε_join := by rw [hεjoin_def]; linarith only [hεX_pos]
  -- Distortion budget: δ_typ ≤ ε/4.
  have hδtyp_le : δ_typ ≤ ε / 4 := by
    rw [hδtyp_def, hεjoin_def]
    have h8 : 8 * (S + 1) * ε_X ≤ ε := by
      calc 8 * (S + 1) * ε_X = ε_X * (8 * (S + 1)) := by ring
        _ ≤ (ε / (8 * (S + 1))) * (8 * (S + 1)) :=
            mul_le_mul_of_nonneg_right hεX_le_dist hSp1_pos.le
        _ = ε := by field_simp
    have hexp : 8 * (S + 1) * ε_X = 8 * (ε_X * S) + 8 * ε_X := by ring
    have hrel : 8 * (ε_X * S) = 4 * (2 * ε_X * S) := by ring
    linarith only [h8, hexp, hrel, hεX_pos.le]
  -- KL-floor domination (equality).
  have hδkl_dom : 8 * Na * Nb * ε_X ^ 2 ≤ δ_kl * qZ_min := by
    have heq : δ_kl * qZ_min = 8 * Na * Nb * ε_X ^ 2 := by
      rw [hδkl_def, hK_def]; field_simp
    linarith only [heq]
  -- Rate gap.
  have h_rate_gap : mutualInfoPmf q'
      + (Na * ε_X * L_Y + ε_X * L_X + ε_X * L_Z + δ_kl) < R := by
    have hc1 : Na * ε_X * L_Y ≤ Na * ε_X * |L_Y| :=
      mul_le_mul_of_nonneg_left (le_abs_self L_Y) (mul_nonneg hNa_pos.le hεX_pos.le)
    have hc2 : ε_X * L_X ≤ ε_X * |L_X| :=
      mul_le_mul_of_nonneg_left (le_abs_self L_X) hεX_pos.le
    have hc3 : ε_X * L_Z ≤ ε_X * |L_Z| :=
      mul_le_mul_of_nonneg_left (le_abs_self L_Z) hεX_pos.le
    have hδkl_le : δ_kl ≤ K * ε_X := by
      rw [hδkl_def]
      have hsq : ε_X ^ 2 ≤ ε_X := by nlinarith only [hεX_pos.le, hεX_le1]
      exact mul_le_mul_of_nonneg_left hsq hK_pos.le
    have hCrate_ge : Na * |L_Y| + |L_X| + |L_Z| ≤ C_rate := by
      rw [hCrate_def]; exact le_add_of_nonneg_right zero_le_one
    have hle_Crate : ε_X * (Na * |L_Y| + |L_X| + |L_Z|) ≤ ε_X * C_rate :=
      mul_le_mul_of_nonneg_left hCrate_ge hεX_pos.le
    have hmain : ε_X * C_rate + ε_X * K ≤ (R - mutualInfoPmf q') / 2 := by
      have h1 : ε_X * (C_rate + K)
          ≤ (R - mutualInfoPmf q') / (2 * (C_rate + K)) * (C_rate + K) :=
        mul_le_mul_of_nonneg_right hεX_le_gap hCK_pos.le
      have h2 : (R - mutualInfoPmf q') / (2 * (C_rate + K)) * (C_rate + K)
          = (R - mutualInfoPmf q') / 2 := by
        rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt hCK_pos)]
      rw [h2] at h1
      have h3 : ε_X * C_rate + ε_X * K = ε_X * (C_rate + K) := by ring
      rw [h3]; exact h1
    have hring1 : Na * ε_X * |L_Y| + ε_X * |L_X| + ε_X * |L_Z|
        = ε_X * (Na * |L_Y| + |L_X| + |L_Z|) := by ring
    have hring2 : K * ε_X = ε_X * K := by ring
    linarith only [hc1, hc2, hc3, hδkl_le, hle_Crate, hmain, hG_pos, hring1, hring2]
  -- Assemble.
  refine ⟨ε_X, ε_join, ε_dist, δ_kl, δ_typ, qZ_min,
    hεX_pos, hεjoin_pos, hεdist_pos, hδkl_pos, hδtyp_nn, hεX_lt_join,
    h_rate_gap, ?_, ?_, ?_, ?_, ?_, hqZ_min_pos, hqZ_min_le, hδkl_dom⟩
  · -- distortion budget slack: E' + δ_typ ≤ D + ε/4 + ε/2/2
    linarith only [hE', hδtyp_le]
  · -- h_dist_slack: ε_join * S ≤ δ_typ
    exact le_of_eq hδtyp_def.symm
  · -- bound_X: Nb * ε_join * L_X < ε_dist
    rw [hεdist_def]
    have h1 : Nb * ε_join * L_X ≤ Nb * ε_join * |L_X| :=
      mul_le_mul_of_nonneg_left (le_abs_self L_X) (mul_nonneg hNb_pos.le hεjoin_pos.le)
    have t2 : 0 ≤ Na * ε_join * |L_Y| :=
      mul_nonneg (mul_nonneg hNa_pos.le hεjoin_pos.le) (abs_nonneg _)
    have t3 : 0 ≤ ε_join * |L_Z| := mul_nonneg hεjoin_pos.le (abs_nonneg _)
    linarith only [h1, t2, t3]
  · -- bound_Y: Na * ε_join * L_Y < ε_dist
    rw [hεdist_def]
    have h1 : Na * ε_join * L_Y ≤ Na * ε_join * |L_Y| :=
      mul_le_mul_of_nonneg_left (le_abs_self L_Y) (mul_nonneg hNa_pos.le hεjoin_pos.le)
    have t1 : 0 ≤ Nb * ε_join * |L_X| :=
      mul_nonneg (mul_nonneg hNb_pos.le hεjoin_pos.le) (abs_nonneg _)
    have t3 : 0 ≤ ε_join * |L_Z| := mul_nonneg hεjoin_pos.le (abs_nonneg _)
    linarith only [h1, t1, t3]
  · -- bound_Z: ε_join * L_Z < ε_dist
    rw [hεdist_def]
    have h1 : ε_join * L_Z ≤ ε_join * |L_Z| :=
      mul_le_mul_of_nonneg_left (le_abs_self L_Z) hεjoin_pos.le
    have t1 : 0 ≤ Nb * ε_join * |L_X| :=
      mul_nonneg (mul_nonneg hNb_pos.le hεjoin_pos.le) (abs_nonneg _)
    have t2 : 0 ≤ Na * ε_join * |L_Y| :=
      mul_nonneg (mul_nonneg hNa_pos.le hεjoin_pos.le) (abs_nonneg _)
    linarith only [h1, t1, t2]

/-! ## Source-law bridge -/

/-- The source-side marginal of the i.i.d. ambient built from `q` equals the
`pmfToMeasure` of the source pmf `P_X`, provided `marginalFst q = P_X`. This lets
the achievability conclusion be stated over `pmfToMeasure P_X` rather than the
internal perturbed ambient. -/
lemma rdAmbient_iidXs_eq_pmfToMeasure_source
    {q : α × β → ℝ} (hq : q ∈ stdSimplex ℝ (α × β))
    {P_X : α → ℝ} (hP : P_X ∈ stdSimplex ℝ α) (hmarg : marginalFst q = P_X) :
    (rdAmbient q).map (iidXs (α := α) (β := β) 0) = pmfToMeasure (α := α) P_X := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α) P_X) :=
    pmfToMeasure_isProbabilityMeasure hP
  haveI : IsProbabilityMeasure ((rdAmbient q).map (iidXs (α := α) (β := β) 0)) :=
    rdAmbient_iidXs_isProbabilityMeasure q hq
  refine Measure.ext_of_singleton (fun a ↦ ?_)
  have hL : ((rdAmbient q).map (iidXs (α := α) (β := β) 0)).real {a} = P_X a := by
    rw [rdAmbient_map_iidXs q hq, pmfToMeasure_map_fst_real_singleton hq a, hmarg]
  have hR : (pmfToMeasure (α := α) P_X).real {a} = P_X a :=
    pmfToMeasure_real_singleton hP a
  have heq_real := hL.trans hR.symm
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp heq_real

/-! ## Wrapper: unconditional operational achievability -/

/-- **Rate-distortion theorem** (achievability, unconditional operational form).

For a full-support source `P_X` with a feasible constraint set and any rate
`R > R(D)`, for every `ε > 0` there is a block length `N` such that every `n ≥ N`
admits a rate-`R` lossy code whose expected block distortion is at most `D + ε`.

Unlike `rate_distortion_achievability_strong`, this form carries no slack, no
strict-positivity of an optimal pmf, and no strong-to-weak inclusion hypothesis:
they are all discharged internally via a marginal-preserving full-support
perturbation (`rdPerturb`), the strong-to-distortion inclusion
(`jts_subset_dts_of_dist_slack`), and the slack selection (`rdSlack_exists`).

`hP_supp : ∀ a, 0 < P_X a` is a regularity precondition, not load-bearing: it is
required only so the marginal-preserving perturbation toward `P_X ⊗ uniform_β`
lands strictly positive; the operational content is proved internally. -/
@[entry_point]
theorem rate_distortion_achievability_operational
    (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α) (hP_supp : ∀ a, 0 < P_X a)
    (d : DistortionFn α β) {D : ℝ}
    (h_ne : (RDConstraint P_X d D).Nonempty)
    {R : ℝ} (hR : rateDistortionFunctionPmf P_X d D < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (_hM_ub : (M : ℝ) ≤ Real.exp ((n : ℝ) * R) + 1)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion (pmfToMeasure (α := α) P_X) d ≤ D + ε := by
  classical
  -- Step 1: attain a minimizer `qStar₀ ∈ RDConstraint P_X d D`.
  obtain ⟨qStar₀, hqStar₀_mem, hqStar₀_min⟩ :=
    rateDistortionFunctionPmf_attained P_X d D h_ne
  have hqStar₀_simp : qStar₀ ∈ stdSimplex ℝ (α × β) := hqStar₀_mem.1
  have hmarg₀ : marginalFst qStar₀ = P_X := hqStar₀_mem.2.1
  have hE₀ : expectedDistortionPmf d qStar₀ ≤ D := hqStar₀_mem.2.2
  have hI₀ : mutualInfoPmf qStar₀ < R := by
    have hle : mutualInfoPmf qStar₀ ≤ rateDistortionFunctionPmf P_X d D := by
      refine le_csInf ⟨_, Set.mem_image_of_mem _ hqStar₀_mem⟩ ?_
      rintro _ ⟨q, hq, rfl⟩
      exact hqStar₀_min hq
    linarith
  -- Step 2: marginal-preserving full-support perturbation.
  obtain ⟨lam₀, hlam₀_pos, hlam₀_le1, hlam₀_prop⟩ :=
    rdPerturb_mutualInfo_lt (P_X := P_X) hI₀
  obtain ⟨lam₁, hlam₁_pos, hlam₁_le1, hlam₁_prop⟩ :=
    rdPerturb_expectedDist_le (P_X := P_X) hE₀ hε
  set lam := min lam₀ lam₁ with hlam_def
  have hlam_pos : 0 < lam := lt_min hlam₀_pos hlam₁_pos
  have hlam_le1 : lam ≤ 1 := le_trans (min_le_left _ _) hlam₀_le1
  have hlam_le_lam₀ : lam ≤ lam₀ := min_le_left _ _
  have hlam_le_lam₁ : lam ≤ lam₁ := min_le_right _ _
  set q' := rdPerturb qStar₀ P_X lam with hq'_def
  have hq'_simp : q' ∈ stdSimplex ℝ (α × β) :=
    rdPerturb_mem_stdSimplex hlam_pos.le hlam_le1 hqStar₀_simp hP_pmf
  haveI hq'_prob : IsProbabilityMeasure (rdAmbient q') :=
    rdAmbient_isProbabilityMeasure q' hq'_simp
  have hq'_pos : ∀ p, 0 < q' p := rdPerturb_pos hlam_pos hlam_le1 hqStar₀_simp hP_supp
  have hmarg_q' : marginalFst q' = P_X := rdPerturb_marginalFst hmarg₀
  have hI'_lt_R : mutualInfoPmf q' < R := hlam₀_prop lam hlam_pos hlam_le_lam₀
  have hE'_le : expectedDistortionPmf d q' ≤ D + ε / 4 :=
    hlam₁_prop lam hlam_pos hlam_le_lam₁
  have hq'_mem : q' ∈ RDConstraint P_X d (D + ε / 4) := ⟨hq'_simp, hmarg_q', hE'_le⟩
  -- Step 3: select slack parameters (Piece A).
  obtain ⟨ε_X, ε_join, ε_dist, δ_kl, δ_typ, qZ_min,
      hε_X_pos, hε_join_pos, hε_dist_pos, hδ_kl_pos, hδ_typ_nn, hε_X_lt_ε_join,
      h_rate_gap, h_slack, h_dist_slack, h_bound_X, h_bound_Y, h_bound_Z,
      hqZ_min_pos, hqZ_min_le, hδ_kl_dominates⟩ :=
    rdSlack_exists hq'_simp hq'_pos hI'_lt_R hE'_le hε
  -- Step 4: the strong-to-distortion inclusion (Piece C).
  have hmarg_X : ((rdAmbient q').map
          (jointSequence (α := α) (β := β) iidXs iidYs 0)).map Prod.fst
        = (rdAmbient q').map (iidXs (α := α) (β := β) 0) := by
    rw [rdAmbient_map_jointSequence q' hq'_simp, rdAmbient_map_iidXs q' hq'_simp]
  have hmarg_Y : ((rdAmbient q').map
          (jointSequence (α := α) (β := β) iidXs iidYs 0)).map Prod.snd
        = (rdAmbient q').map (iidYs (α := α) (β := β) 0) := by
    rw [rdAmbient_map_jointSequence q' hq'_simp, rdAmbient_map_iidYs q' hq'_simp]
  have h_jts_subset_dts : ∀ {n : ℕ}, 0 < n → ∀ (x : Fin n → α) (y : Fin n → β),
      (x, y) ∈ jointStronglyTypicalSet (rdAmbient q') iidXs iidYs n ε_join →
      (x, y) ∈ distortionTypicalSet (rdAmbient q') iidXs iidYs d n ε_dist δ_typ :=
    fun {n} hn x y hmem =>
      jts_subset_dts_of_dist_slack (rdAmbient q') iidXs iidYs
        measurable_iidXs measurable_iidYs hmarg_X hmarg_Y d hn hε_join_pos.le
        h_bound_X h_bound_Y h_bound_Z h_dist_slack hmem
  -- Step 5: apply the strong theorem with the D-relaxation.
  obtain ⟨N, hN⟩ := rate_distortion_achievability_strong (P_X_pmf := P_X) d
    (D := D + ε / 4) q' hq'_mem hq'_pos (R := R) hI'_lt_R (ε' := ε / 2) (by linarith)
    ε_X ε_join ε_dist δ_kl δ_typ
    hε_X_pos hε_join_pos hε_dist_pos hδ_kl_pos hδ_typ_nn hε_X_lt_ε_join
    h_rate_gap h_slack h_dist_slack h_jts_subset_dts
    qZ_min hqZ_min_pos hqZ_min_le hδ_kl_dominates
  -- Step 6: bridge the source law and weaken the distortion budget.
  have h_src : (rdAmbient q').map (iidXs (α := α) (β := β) 0)
      = pmfToMeasure (α := α) P_X :=
    rdAmbient_iidXs_eq_pmfToMeasure_source hq'_simp hP_pmf hmarg_q'
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, hM_lb, hM_ub, c, hc⟩ := hN n hn
  rw [h_src] at hc
  exact ⟨M, hM_lb, hM_ub, c, by linarith⟩

end InformationTheory.Shannon
