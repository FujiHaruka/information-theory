import InformationTheory.Shannon.BroadcastChannel.Superposition.FullSupport

/-!
# Broadcast channel — the UV outer region of a less noisy channel is achievable

The UV outer region is indexed by five-tuple laws whose auxiliaries range over a countable
alphabet, the superposition inner bound by achievability pairs over a finite one.  Truncating the
first auxiliary at a level `m` moves a law of the outer region onto a finite alphabet at a cost
the tail alone carries, and perturbing the achievability pair it yields toward the uniform law
repairs that pair's support at a cost any positive slack covers.

The truncation leaves the corner slot of the first receiver alone, because that slot reads the
second auxiliary, so the whole cost of the truncation is charged to the second rate once, and the
same subtraction pays for the sum-rate constraint as well.  The perturbation slack is subtracted
from both rates.  Neither cost depends on the other, so both vanish along one sequence of indices,
and the inner bound is a closure, which recovers the rate pair itself from the shifted ones.
Combined with the outer bound and with the achievability of the inner one, this describes the
capacity region of a less noisy broadcast channel by a single-letter expression.  Positive mass on
every output pair is asked for by the achievability step alone; the inclusion of the outer region
in the inner bound needs nothing beyond the less noisy hypothesis.

## Main statements

* `bc_lessNoisy_capacity_eq_uv` — the single-letter characterization: the capacity region of a
  less noisy broadcast channel whose transition law gives every output pair positive mass is its
  UV outer region `bcOuterRegionUV`.
* `bc_lessNoisy_superposition_eq_capacity` — the same capacity region read off the superposition
  inner bound instead of the outer bound.
* `bc_lessNoisy_uv_subset_superposition` — the inclusion the two equalities rest on: the UV
  outer region of a less noisy channel is contained in the superposition inner bound over the
  full-support achievability pairs.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open scoped ENNReal Topology

universe u

/-! ## The reverse inclusion -/

section Converse

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [StandardBorelSpace α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
    [StandardBorelSpace β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
    [StandardBorelSpace β₂]

omit [StandardBorelSpace α] [StandardBorelSpace β₁] [StandardBorelSpace β₂] in
theorem uvInfo₂_toReal_sub_slack_le (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    (m : ℕ) :
    (uvInfo₂ ν).toReal - (uvQuantizeSlack ν m).toReal
      ≤ (uvInfo₂ (uvQuantizeLaw.{u} ν m)).toReal := by
  have hs := uvQuantizeSlack_ne_top ν m
  have hfin := uvInfo₂_ne_top (uvQuantizeLaw.{u} ν m)
  have h := ENNReal.toReal_le_add (uvInfo₂_le_uvQuantizeLaw_add_slack.{u} ν m) hfin hs
  linarith

omit [StandardBorelSpace β₂] in
theorem uvInfoSum₂_toReal_sub_slack_le (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    (m : ℕ) :
    (uvInfoSum₂ ν).toReal - (uvQuantizeSlack ν m).toReal
      ≤ (uvInfoSum₂ (uvQuantizeLaw.{u} ν m)).toReal := by
  have hs := uvQuantizeSlack_ne_top ν m
  have hfin := uvInfoSum₂_ne_top (uvQuantizeLaw.{u} ν m)
  have hle := ENNReal.toReal_le_add (uvInfoSum₂_le_uvQuantizeLaw_add_slack.{u} W h m) hfin hs
  linarith

theorem sub_mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (hln : IsBCLessNoisy W) {ν : Measure (ℕ × ℕ × α × β₁ × β₂)}
    [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) {p : ℝ × ℝ} (hp : p ∈ uvRegion ν)
    (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ((p.1 - δ, p.2 - (uvQuantizeSlack ν m).toReal - δ) : ℝ × ℝ)
      ∈ bcSuperpositionRegionNoSumRate.{u} W := by
  obtain ⟨hb₁, hb₂, hs₂, -⟩ := hp
  have hlaw : IsUVChannelLaw W (uvQuantizeLaw.{u} ν m) := uvQuantizeLaw_isUVChannelLaw W h m
  have h₁ : p.1 ≤ (uvInfo₁ (uvQuantizeLaw.{u} ν m)).toReal := by
    rw [uvInfo₁_uvQuantizeLaw ν m]; exact hb₁
  have h₂ : p.2 - (uvQuantizeSlack ν m).toReal ≤ (uvInfo₂ (uvQuantizeLaw.{u} ν m)).toReal := by
    linarith [uvInfo₂_toReal_sub_slack_le.{u} ν m]
  have hsum : p.1 + (p.2 - (uvQuantizeSlack ν m).toReal)
      ≤ (uvInfoSum₂ (uvQuantizeLaw.{u} ν m)).toReal := by
    linarith [uvInfoSum₂_toReal_sub_slack_le.{u} W h m]
  exact sub_mem_bcSuperpositionRegionNoSumRate_of_lessNoisy_of_isUVChannelLaw W hln hlaw hδ
    h₁ h₂ hsum

theorem mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (hln : IsBCLessNoisy W) {ν : Measure (ℕ × ℕ × α × β₁ × β₂)}
    [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) {p : ℝ × ℝ} (hp : p ∈ uvRegion ν) :
    p ∈ bcSuperpositionRegionNoSumRate.{u} W := by
  have ht : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hslack : Tendsto (fun m : ℕ ↦ (uvQuantizeSlack ν m).toReal) atTop (𝓝 0) := by
    have hcomp :=
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp (tendsto_uvQuantizeSlack ν)
    simpa [Function.comp_def] using hcomp
  have h1 : Tendsto (fun k : ℕ ↦ p.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 p.1) := by
    simpa using tendsto_const_nhds.sub ht
  have h2 : Tendsto (fun k : ℕ ↦ p.2 - (uvQuantizeSlack ν k).toReal - 1 / ((k : ℝ) + 1))
      atTop (𝓝 p.2) := by
    simpa using (tendsto_const_nhds.sub hslack).sub ht
  exact (bcSuperpositionRegionNoSumRate_isClosed W).mem_of_tendsto (h1.prodMk_nhds h2)
    (Eventually.of_forall fun k ↦
      sub_mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion W hln h hp k (by positivity))

/-- The UV outer region of a less noisy broadcast channel is contained in the superposition inner
bound over the full-support achievability pairs.  The channel needs no support hypothesis here:
the inclusion compares two single-letter regions, and positive mass on every output pair is asked
for only where the inner bound is turned into codes
(`bcSuperpositionRegionNoSumRate_subset_capacity`). -/
@[entry_point]
theorem bc_lessNoisy_uv_subset_superposition (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) :
    bcOuterRegionUV W ⊆ bcSuperpositionRegionNoSumRate.{u} W := by
  refine closure_minimal ?_ (bcSuperpositionRegionNoSumRate_isClosed W)
  refine Set.iUnion_subset fun ν ↦ Set.iUnion_subset fun hν ↦ fun p hp ↦ ?_
  exact mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion W hln hν hp

end Converse

/-! ## The capacity region of a less noisy channel -/

section Equality

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [StandardBorelSpace α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
    [StandardBorelSpace β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
    [StandardBorelSpace β₂]

/-- The capacity region of a less noisy broadcast channel whose transition law gives every output
pair positive mass is its UV outer region `bcOuterRegionUV`, a single-letter expression in the
four information slots of a five-tuple law. -/
@[entry_point]
theorem bc_lessNoisy_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W := by
  classical
  exact Set.Subset.antisymm (bc_capacity_subset_uv W)
    ((bc_lessNoisy_uv_subset_superposition.{u} W hln).trans
      (bcSuperpositionRegionNoSumRate_subset_capacity W hW hln))

theorem bc_lessNoisy_superposition_eq_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcSuperpositionRegionNoSumRate.{u} W = bcCapacityRegion W := by
  classical
  exact Set.Subset.antisymm (bcSuperpositionRegionNoSumRate_subset_capacity W hW hln)
    ((bc_capacity_subset_uv W).trans (bc_lessNoisy_uv_subset_superposition.{u} W hln))

end Equality

end InformationTheory.Shannon.BroadcastChannel
