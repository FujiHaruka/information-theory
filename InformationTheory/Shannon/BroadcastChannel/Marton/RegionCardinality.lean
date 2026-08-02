import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Marton.CardinalityBound
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

/-!
# Broadcast channel — capping the outer auxiliary alphabet of Marton's inner bound

`exists_bcAuxAlphabet_card_le_martonWeightedSumAllWeights` caps the outer auxiliary alphabet one
weighted sum at a time: for every weighting of the three information terms there is a law on an
alphabet of at most `martonAuxBound α` letters doing at least as well.  This file turns that
family of scalar statements into one statement about the region, by reading the weights off a
separating functional: the closed convex hull of Marton's inner bound is unchanged when the union
is restricted to those indices.

The inner auxiliary alphabet is left alone.  Its cardinality is not bounded here, and the
dependence between the two auxiliaries is the term the weighted sum enters with a nonpositive
sign, so nothing in the argument caps it.

## Main definitions

* `martonRegionUnionOuterBounded W` — the union defining Marton's inner bound, restricted to the
  indices whose outer auxiliary alphabet carries at most `martonAuxBound α` letters.

## Main statements

* `closure_convexHull_martonRegionUnion_eq_outerBounded` — the closed convex hull of Marton's
  inner bound is unchanged by that restriction.
* `martonRegionUnionOuterBounded_isLowerSet` / `martonRegionUnionOuterBounded_nonempty` /
  `martonRegionUnionOuterBounded_subset_union` — the restricted union is a nonempty lower set,
  as the unrestricted union is, and it sits inside the unrestricted one.
* `IsLowerSet.convexHull` — the convex hull of a lower set of the plane is a lower set.
* `exists_nonneg_weights_separating_of_isLowerSet` — a point outside a nonempty closed convex
  lower set of the plane is separated from it by a functional with nonnegative coefficients.
* `martonInfoV₁V₂_nonneg` — the dependence between the two auxiliaries is nonnegative, which is
  the hypothesis under which a rate weighting is attained at a vertex of the quadrilateral.

## Implementation notes

The separating functional is produced by `geometric_hahn_banach_closed_point`, whose weights are
signed.  Two facts turn them into the nonnegative weights the cardinality bound asks for: the
region is a lower set, so a functional with a negative coefficient is unbounded below on it and
cannot separate; and a lower set stays one under convex hulls and closures.

The weights of the cardinality bound multiply the three information terms, whereas a separating
functional multiplies the two rate coordinates.  `exists_weights_dominating` converts between the
two: it reads a rate weighting into an information weighting that dominates it on the
quadrilateral and is attained at one of its vertices, which is where the nonnegativity of the
auxiliary dependence is used.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open Set MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel

universe u

/-! ## Lower sets of the plane and their separating functionals -/

section Separation

theorem _root_.IsLowerSet.convexHull {s : Set (ℝ × ℝ)} (hs : IsLowerSet s) :
    IsLowerSet (convexHull ℝ s) := by
  intro a b hba ha
  obtain ⟨d, hd0, rfl⟩ : ∃ d : ℝ × ℝ, 0 ≤ d ∧ b = a - d :=
    ⟨a - b, ⟨by simpa using (Prod.le_def.mp hba).1, by simpa using (Prod.le_def.mp hba).2⟩,
      by abel⟩
  have hshift : ∀ x : ℝ × ℝ, x - d ≤ x := fun x ↦
    Prod.le_def.mpr ⟨by simpa using hd0.1, by simpa using hd0.2⟩
  have hconv : Convex ℝ {x : ℝ × ℝ | x - d ∈ _root_.convexHull ℝ s} := by
    intro x hx y hy p q hp hq hpq
    have hpd : p • d + q • d = d := by rw [← add_smul, hpq, one_smul]
    change p • x + q • y - d ∈ _root_.convexHull ℝ s
    have hrw : p • (x - d) + q • (y - d) = p • x + q • y - d := by
      rw [smul_sub, smul_sub,
        show p • x - p • d + (q • y - q • d) = p • x + q • y - (p • d + q • d) from by abel, hpd]
    rw [← hrw]
    exact (convex_convexHull ℝ s) hx hy hp hq hpq
  have hsub : s ⊆ {x : ℝ × ℝ | x - d ∈ _root_.convexHull ℝ s} := fun x hx ↦
    subset_convexHull ℝ s (hs (hshift x) hx)
  exact convexHull_min hsub hconv ha

theorem exists_nonneg_weights_separating_of_isLowerSet
    {S : Set (ℝ × ℝ)} (hconv : Convex ℝ S) (hclosed : IsClosed S) (hlower : IsLowerSet S)
    (hne : S.Nonempty) {p : ℝ × ℝ} (hp : p ∉ S) :
    ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
      ∀ x ∈ S, μ₁ * x.1 + μ₂ * x.2 < μ₁ * p.1 + μ₂ * p.2 := by
  obtain ⟨f, u, hfS, hfp⟩ := geometric_hahn_banach_closed_point hconv hclosed hp
  refine ⟨f (1, 0), f (0, 1), ?_, ?_, ?_⟩
  · by_contra hneg
    push Not at hneg
    obtain ⟨x, hx⟩ := hne
    have key : ∀ t : ℝ, 0 ≤ t → f (x.1 - t, x.2) < u := fun t ht ↦
      hfS _ (hlower (by exact ⟨by simpa using sub_le_self x.1 ht, le_rfl⟩) hx)
    have hval : ∀ t : ℝ, f (x.1 - t, x.2) = f x - t * f (1, 0) := by
      intro t
      have : ((x.1 - t : ℝ), (x.2 : ℝ)) = x - t • ((1 : ℝ), (0 : ℝ)) := by
        simp [Prod.ext_iff]
      rw [this, map_sub, map_smul, smul_eq_mul]
    have hc : 0 < -f (1, 0) := by linarith
    have hnum : 0 < u - f x + 1 := by have := hfS x hx; linarith
    set t : ℝ := (u - f x + 1) / (-f (1, 0)) with ht_def
    have ht0 : 0 ≤ t := le_of_lt (div_pos hnum hc)
    have hne0 : f (1, 0) ≠ 0 := by linarith
    have htm : t * f (1, 0) = -(u - f x + 1) := by
      rw [ht_def, div_mul_eq_mul_div, div_eq_iff (by simpa using hne0)]; ring
    have hbig := key t ht0
    rw [hval, htm] at hbig
    linarith
  · by_contra hneg
    push Not at hneg
    obtain ⟨x, hx⟩ := hne
    have key : ∀ t : ℝ, 0 ≤ t → f (x.1, x.2 - t) < u := fun t ht ↦
      hfS _ (hlower (by exact ⟨le_rfl, by simpa using sub_le_self x.2 ht⟩) hx)
    have hval : ∀ t : ℝ, f (x.1, x.2 - t) = f x - t * f (0, 1) := by
      intro t
      have : ((x.1 : ℝ), (x.2 - t : ℝ)) = x - t • ((0 : ℝ), (1 : ℝ)) := by
        simp [Prod.ext_iff]
      rw [this, map_sub, map_smul, smul_eq_mul]
    have hc : 0 < -f (0, 1) := by linarith
    have hnum : 0 < u - f x + 1 := by have := hfS x hx; linarith
    set t : ℝ := (u - f x + 1) / (-f (0, 1)) with ht_def
    have ht0 : 0 ≤ t := le_of_lt (div_pos hnum hc)
    have hne0 : f (0, 1) ≠ 0 := by linarith
    have htm : t * f (0, 1) = -(u - f x + 1) := by
      rw [ht_def, div_mul_eq_mul_div, div_eq_iff (by simpa using hne0)]; ring
    have hbig := key t ht0
    rw [hval, htm] at hbig
    linarith
  · intro x hx
    have hval : ∀ y : ℝ × ℝ, f y = y.1 * f (1, 0) + y.2 * f (0, 1) := by
      intro y
      have : y = y.1 • ((1 : ℝ), (0 : ℝ)) + y.2 • ((0 : ℝ), (1 : ℝ)) := by
        simp
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp
    have h1 := hfS x hx
    rw [hval] at h1
    rw [hval] at hfp
    nlinarith [h1, hfp]

private lemma exists_weights_dominating (μ₁ μ₂ : ℝ) (h1 : 0 ≤ μ₁) (h2 : 0 ≤ μ₂) :
    ∃ a b c : ℝ, 0 ≤ b ∧ 0 ≤ c ∧
      (∀ I₁ I₂ I₁₂ x y : ℝ, x ≤ I₁ → y ≤ I₂ → x + y ≤ I₁ + I₂ - I₁₂ →
         μ₁ * x + μ₂ * y ≤ a * I₁ + b * I₂ + c * (I₁ + I₂ - I₁₂)) ∧
      (∀ I₁ I₂ I₁₂ : ℝ, 0 ≤ I₁₂ → ∃ x y : ℝ, x ≤ I₁ ∧ y ≤ I₂ ∧ x + y ≤ I₁ + I₂ - I₁₂ ∧
         μ₁ * x + μ₂ * y = a * I₁ + b * I₂ + c * (I₁ + I₂ - I₁₂)) := by
  rcases le_total μ₂ μ₁ with h | h
  · refine ⟨μ₁ - μ₂, 0, μ₂, le_rfl, h2, ?_, ?_⟩
    · intro I₁ I₂ I₁₂ x y hx _ hsum
      linarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr h),
        mul_le_mul_of_nonneg_left hsum h2]
    · exact fun I₁ I₂ I₁₂ h₁₂ ↦
        ⟨I₁, I₂ - I₁₂, le_rfl, by linarith, by linarith, by ring⟩
  · refine ⟨0, μ₂ - μ₁, μ₁, sub_nonneg.mpr h, h1, ?_, ?_⟩
    · intro I₁ I₂ I₁₂ x y _ hy hsum
      linarith [mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr h),
        mul_le_mul_of_nonneg_left hsum h1]
    · exact fun I₁ I₂ I₁₂ h₁₂ ↦
        ⟨I₁ - I₁₂, I₂, by linarith, le_rfl, by linarith, by ring⟩

end Separation

/-! ## The union over the outer auxiliary alphabets of bounded cardinality -/

section Info

variable {α β₁ β₂ V₁ V₂ : Type*}
  [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
  [Fintype V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]

theorem martonInfoV₁V₂_nonneg (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    0 ≤ martonInfoV₁V₂ pV K W := by
  have hX : Measurable (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := measurable_fst
  have hY : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) := measurable_fst.comp measurable_snd
  rw [martonInfoV₁V₂,
    entropy_pair_eq_entropy_add_condEntropy (martonJointDistribution pV K W) _ _ hX hY]
  have := entropy_ge_condEntropy (martonJointDistribution pV K W)
    (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) hY hX
  linarith

end Info

section OuterBounded

variable {α : Type u} {β₁ β₂ : Type*} [Fintype α] [MeasurableSpace α]
  [Fintype β₁] [MeasurableSpace β₁] [Fintype β₂] [MeasurableSpace β₂]

/-- The union defining `martonRegionUnion`, restricted to the indices whose outer auxiliary
alphabet carries at most `martonAuxBound α` letters.  The inner auxiliary alphabet still
ranges over every cardinality: the weighted sum that the cardinality bound optimizes reads the
dependence between the two auxiliaries with a nonpositive weight, so it caps the outer alphabet
only. -/
noncomputable def martonRegionUnionOuterBounded (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (_ : k₁ < martonAuxBound α) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K), martonRegion pV K W)

lemma martonRegionUnionOuterBounded_isLowerSet (W : BCChannel α β₁ β₂) :
    IsLowerSet (martonRegionUnionOuterBounded W) :=
  IsLowerSet.closure (isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦
    isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦
      isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦ martonRegion_isLowerSet _ _ _)

lemma martonRegion_subset_outerBounded_of_bcAux (k₁ k₂ : ℕ) (hk₁ : k₁ < martonAuxBound α)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂)) [IsProbabilityMeasure pV]
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) : martonRegion pV K W ⊆ martonRegionUnionOuterBounded W := by
  refine subset_trans ?_ subset_closure
  exact Set.subset_iUnion_of_subset k₁ (Set.subset_iUnion_of_subset hk₁
    (Set.subset_iUnion_of_subset k₂ (Set.subset_iUnion_of_subset pV
      (Set.subset_iUnion_of_subset inferInstance (Set.subset_iUnion_of_subset K
        (Set.subset_iUnion_of_subset inferInstance subset_rfl))))))

lemma martonRegionUnionOuterBounded_subset_union (W : BCChannel α β₁ β₂) :
    martonRegionUnionOuterBounded W ⊆ martonRegionUnion W := by
  refine closure_mono ?_
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun _ ↦ Set.iUnion_subset fun k₂ ↦
    Set.iUnion_subset fun pV ↦ Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun K ↦
      Set.iUnion_subset fun hK ↦ ?_
  exact Set.subset_iUnion_of_subset k₁ (Set.subset_iUnion_of_subset k₂
    (Set.subset_iUnion_of_subset pV (Set.subset_iUnion_of_subset hpV
      (Set.subset_iUnion_of_subset K (Set.subset_iUnion_of_subset hK subset_rfl)))))

section Nonemptiness

variable [Nonempty α]

lemma martonRegionUnionOuterBounded_nonempty (W : BCChannel α β₁ β₂) :
    (martonRegionUnionOuterBounded W).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (bcAuxAlphabet.{u} 0 × bcAuxAlphabet.{u} 0))
  exact (martonRegion_nonempty (Measure.dirac v₀) (Kernel.const _ (Measure.dirac x₀)) W).mono
    (martonRegion_subset_outerBounded_of_bcAux 0 0 Fintype.card_pos _ _ W)

end Nonemptiness

end OuterBounded

/-! ## The cardinality bound on the region -/

section Cardinality

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

lemma martonRegion_subset_closure_convexHull_outerBounded (k₁ k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂)) [IsProbabilityMeasure pV]
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegion pV K W ⊆ closure (convexHull ℝ (martonRegionUnionOuterBounded W)) := by
  have hclosed : IsClosed (closure (convexHull ℝ (martonRegionUnionOuterBounded W))) :=
    isClosed_closure
  have hconv : Convex ℝ (closure (convexHull ℝ (martonRegionUnionOuterBounded W))) :=
    (convex_convexHull ℝ _).closure
  have hlower : IsLowerSet (closure (convexHull ℝ (martonRegionUnionOuterBounded W))) :=
    (martonRegionUnionOuterBounded_isLowerSet W).convexHull.closure
  have hne : (closure (convexHull ℝ (martonRegionUnionOuterBounded W))).Nonempty :=
    (martonRegionUnionOuterBounded_nonempty W).mono ((subset_convexHull ℝ _).trans subset_closure)
  intro p hp
  by_contra hpS
  obtain ⟨μ₁, μ₂, h1, h2, hsep⟩ :=
    exists_nonneg_weights_separating_of_isLowerSet hconv hclosed hlower hne hpS
  obtain ⟨a, b, c, hb, hc, hdom, hvert⟩ := exists_weights_dominating μ₁ μ₂ h1 h2
  have hdis : pV.fst ⊗ₘ pV.condKernel = pV := pV.disintegrate pV.condKernel
  obtain ⟨k, hk, q', hq', κ', hκ', K', hK', hle⟩ :=
    exists_bcAuxAlphabet_card_le_martonWeightedSumAllWeights pV.fst pV.condKernel K W a b c hb hc
  rw [hdis] at hle
  haveI := hq'
  haveI := hκ'
  haveI := hK'
  obtain ⟨x, y, hx, hy, hxy, heq⟩ :=
    hvert (martonInfo₁ (q' ⊗ₘ κ') K' W) (martonInfo₂ (q' ⊗ₘ κ') K' W)
      (martonInfoV₁V₂ (q' ⊗ₘ κ') K' W) (martonInfoV₁V₂_nonneg (q' ⊗ₘ κ') K' W)
  have hz : (x, y) ∈ closure (convexHull ℝ (martonRegionUnionOuterBounded W)) :=
    (martonRegion_subset_outerBounded_of_bcAux k k₂ hk (q' ⊗ₘ κ') K' W).trans
      ((subset_convexHull ℝ _).trans subset_closure) ⟨hx, hy, hxy⟩
  have hsepz : μ₁ * x + μ₂ * y < μ₁ * p.1 + μ₂ * p.2 := hsep (x, y) hz
  obtain ⟨hp₁, hp₂, hpsum⟩ := hp
  have hdomp := hdom (martonInfo₁ pV K W) (martonInfo₂ pV K W) (martonInfoV₁V₂ pV K W)
    p.1 p.2 hp₁ hp₂ hpsum
  linarith

/-- The closed convex hull of Marton's inner bound is unchanged when the outer auxiliary alphabet
is capped at `martonAuxBound α` letters, the size of the channel input alphabet.  No cap is placed
on the inner auxiliary alphabet.

Only the closed convex hull is unchanged: a point of the uncapped union lies in the closed convex
hull of the capped one, not necessarily in the capped union itself, which is not claimed to be
convex.  Capping the outer alphabet alone leaves the union ranging over every cardinality of the
inner one, so it is not a union over finitely many indices.
@audit:ok -/
@[entry_point]
theorem closure_convexHull_martonRegionUnion_eq_outerBounded (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] :
    closure (convexHull ℝ (martonRegionUnion W))
      = closure (convexHull ℝ (martonRegionUnionOuterBounded W)) := by
  refine subset_antisymm ?_
    (closure_mono (convexHull_mono (martonRegionUnionOuterBounded_subset_union W)))
  refine closure_minimal (convexHull_min ?_ (convex_convexHull ℝ _).closure) isClosed_closure
  refine closure_minimal ?_ isClosed_closure
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun K ↦ Set.iUnion_subset fun hK ↦ ?_
  haveI := hpV
  haveI := hK
  exact martonRegion_subset_closure_convexHull_outerBounded k₁ k₂ pV K W

end Cardinality

end InformationTheory.Shannon.BroadcastChannel.Marton
