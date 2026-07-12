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

end InformationTheory.Shannon
