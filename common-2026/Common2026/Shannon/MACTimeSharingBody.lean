import Common2026.Draft.Shannon.MACCornerPoint

/-!
# MAC time-sharing convex-hull body discharge (W9-S6, T3-B)

This file is the **body discharge layer** for the reverse inclusion
`IsMACTimeSharingHyp` published as a hypothesis pass-through in
`Common2026/Shannon/MACCornerPoint.lean` (wave7, T3-B).

## Context

`MACCornerPoint.lean` published (forward direction, fully discharged):

* `mac_region_time_sharing` — convex closure of `InMACCapacityRegion`
  under any mixing weight `α ∈ [0,1]`.
* `mac_pentagon_subset_region` — pentagon ⊆ capacity region (the *easy*
  inclusion: all five vertices satisfy the three corner-point
  inequalities, so by convexity the whole hull does).

…and routed the **reverse inclusion** (capacity region ⊆ pentagon) through
the pass-through predicate

```
IsMACTimeSharingHyp R₁ R₂ I₁ I₂ Iboth : Prop :=
  InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth → (R₁, R₂) ∈ macPentagonRegion I₁ I₂ Iboth
```

## Scope (this file)

We **discharge the reverse-inclusion body** under the geometric
hypotheses that make it true. The corner-point predicate
`InMACCapacityRegion` only requires the three *upper* bounds
`R₁ ≤ I₁`, `R₂ ≤ I₂`, `R₁ + R₂ ≤ Iboth`; it does **not** by itself
constrain a rate pair to the (first-quadrant) pentagon — e.g. the point
`(-1, 0)` satisfies all three bounds but lies outside any pentagon hull
of non-negative vertices. The honest content of the time-sharing
discharge is therefore:

> a rate pair satisfying the three corner-point bounds **and** the two
> non-negativity bounds `0 ≤ R₁`, `0 ≤ R₂` is a convex combination of the
> five pentagon vertices, i.e. lies in `macPentagonRegion`.

Cover–Thomas §15.3.2 / Theorem 15.3.6: the achievable region is the
*convex hull* of the corner points (time-sharing two codes for fractions
`α` and `1-α` of the channel uses produces the convex combination of
their rate pairs). We give the explicit Carathéodory-style decomposition.

### Main results

* `macTimeShareRatePair` — the convex-combination (time-sharing) rate
  pair of two achievable pairs at mixing weight `α`.
* `mac_timeShare_ratePair_mem` — its membership in `InMACCapacityRegion`
  (re-exporting `mac_region_time_sharing` in the explicit
  rate-pair shape).
* `macPentagonRegion_combo_mem` — convexity combinator for the pentagon
  hull (combine two hull points by any `α ∈ [0,1]`).
* `mac_segment_pt_mem` — a point on the segment between two pentagon
  vertices (given the segment fraction) lies in the hull.
* `mac_point_mem_pentagon_of_bounds` — the **geometric core**: a rate
  pair satisfying the five bounds (three corner + two non-negativity)
  lies in `macPentagonRegion`, via an explicit two-level segment
  decomposition (`(R₁,0)` on the bottom edge, then the vertical lift to
  the upper boundary, case-split on the position relative to the
  sum-saturating corner).
* `mac_time_sharing_hyp_of_nonneg` — **discharge of
  `IsMACTimeSharingHyp`** under non-negativity + the pentagon's geometric
  side conditions.
* `mac_capacity_region_is_pentagon_of_nonneg` — pentagon = capacity
  region (intersected with the first quadrant), the fully-discharged
  reverse-inclusion publish.

## 撤退ライン

* The literal `IsMACTimeSharingHyp R₁ R₂ I₁ I₂ Iboth` (with **no**
  non-negativity hypothesis) is **false** for general `R₁, R₂` (negative
  rates satisfy the corner bounds but escape the first-quadrant
  pentagon). We therefore discharge it *under* `0 ≤ R₁`, `0 ≤ R₂`; this
  is the mathematically correct content of the closure theorem (rates are
  `Real.log Mₖ / n ≥ 0`). The non-negativity is the standard implicit
  hypothesis on Cover–Thomas rates and is supplied at the call site.
* The per-code time-sharing *construction* (an explicit time-division
  `MACCode` that interleaves two codes block-wise) is recorded at the
  rate-pair level only (`macTimeShareRatePair` + its membership); the
  block-interleaving code construction with its error-probability
  analysis is a separate achievability discharge and is **not** built
  here.
-/

namespace InformationTheory.Shannon

open scoped BigOperators

set_option linter.unusedSectionVars false

/-! ## Section 1 — Time-sharing rate pair (rate-level scheme) -/

section TimeShareRatePair

/-- **Time-sharing rate pair.** Mixing two achievable rate pairs
`(R₁a, R₂a)` and `(R₁b, R₂b)` for fractions `α` and `1-α` of the channel
uses yields the convex-combination rate pair
`(α R₁a + (1-α) R₁b, α R₂a + (1-α) R₂b)`. This is the rate-level shadow of
the block-interleaving time-division code (Cover–Thomas §15.3.2). -/
def macTimeShareRatePair (α R₁a R₂a R₁b R₂b : ℝ) : ℝ × ℝ :=
  (α * R₁a + (1 - α) * R₁b, α * R₂a + (1 - α) * R₂b)

@[simp] lemma macTimeShareRatePair_fst (α R₁a R₂a R₁b R₂b : ℝ) :
    (macTimeShareRatePair α R₁a R₂a R₁b R₂b).1 = α * R₁a + (1 - α) * R₁b := rfl

@[simp] lemma macTimeShareRatePair_snd (α R₁a R₂a R₁b R₂b : ℝ) :
    (macTimeShareRatePair α R₁a R₂a R₁b R₂b).2 = α * R₂a + (1 - α) * R₂b := rfl

/-- At `α = 1` the time-sharing pair is the first scheme. -/
@[simp] lemma macTimeShareRatePair_one (R₁a R₂a R₁b R₂b : ℝ) :
    macTimeShareRatePair 1 R₁a R₂a R₁b R₂b = (R₁a, R₂a) := by
  simp [macTimeShareRatePair]

/-- At `α = 0` the time-sharing pair is the second scheme. -/
@[simp] lemma macTimeShareRatePair_zero (R₁a R₂a R₁b R₂b : ℝ) :
    macTimeShareRatePair 0 R₁a R₂a R₁b R₂b = (R₁b, R₂b) := by
  simp [macTimeShareRatePair]

/-- **Time-sharing rate pair is achievable.** Re-export of
`mac_region_time_sharing` in the explicit `macTimeShareRatePair` shape:
the time-shared pair of two corner-point-achievable pairs is itself
corner-point achievable. -/
theorem mac_timeShare_ratePair_mem
    (R₁a R₂a R₁b R₂b I₁ I₂ Iboth : ℝ)
    (hA : InMACCapacityRegion R₁a R₂a I₁ I₂ Iboth)
    (hB : InMACCapacityRegion R₁b R₂b I₁ I₂ Iboth)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    InMACCapacityRegion
        (macTimeShareRatePair α R₁a R₂a R₁b R₂b).1
        (macTimeShareRatePair α R₁a R₂a R₁b R₂b).2
        I₁ I₂ Iboth := by
  simpa [macTimeShareRatePair] using
    mac_region_time_sharing R₁a R₂a R₁b R₂b I₁ I₂ Iboth hA hB hα0 hα1

end TimeShareRatePair

/-! ## Section 2 — Convex-hull combinators for the pentagon -/

section PentagonCombo

/-- **Pentagon convexity combinator.** The pentagon hull is convex, so any
mixing `α • a + (1-α) • b` of two hull points (with `α ∈ [0,1]`) is again
in the hull. -/
theorem macPentagonRegion_combo_mem
    (I₁ I₂ Iboth : ℝ) {a b : ℝ × ℝ}
    (ha : a ∈ macPentagonRegion I₁ I₂ Iboth)
    (hb : b ∈ macPentagonRegion I₁ I₂ Iboth)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α • a + (1 - α) • b ∈ macPentagonRegion I₁ I₂ Iboth := by
  have hconv : Convex ℝ (macPentagonRegion I₁ I₂ Iboth) :=
    convex_convexHull ℝ _
  have hβ : 0 ≤ 1 - α := by linarith
  have hsum : α + (1 - α) = 1 := by ring
  exact (convex_iff_add_mem.1 hconv) ha hb hα0 hβ hsum

/-- **Pentagon point-combo (componentwise form).** A rate pair whose two
coordinates are the `α`-convex combinations of the coordinates of two
pentagon points is itself in the pentagon. This is the `ℝ × ℝ`
component-level repackaging of `macPentagonRegion_combo_mem`, convenient
for building points by explicit coordinate arithmetic. -/
theorem macPentagonRegion_combo_coord_mem
    (I₁ I₂ Iboth : ℝ) {a b : ℝ × ℝ}
    (ha : a ∈ macPentagonRegion I₁ I₂ Iboth)
    (hb : b ∈ macPentagonRegion I₁ I₂ Iboth)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (α * a.1 + (1 - α) * b.1, α * a.2 + (1 - α) * b.2)
      ∈ macPentagonRegion I₁ I₂ Iboth := by
  have h := macPentagonRegion_combo_mem I₁ I₂ Iboth ha hb hα0 hα1
  have hfst : (α • a + (1 - α) • b).1 = α * a.1 + (1 - α) * b.1 := by
    simp [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  have hsnd : (α • a + (1 - α) • b).2 = α * a.2 + (1 - α) * b.2 := by
    simp [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have heq : α • a + (1 - α) • b
      = (α * a.1 + (1 - α) * b.1, α * a.2 + (1 - α) * b.2) := by
    apply Prod.ext <;> simp [hfst, hsnd]
  rwa [heq] at h

end PentagonCombo

/-! ## Section 3 — Segment-fraction point membership -/

section SegmentFraction

/-- **Segment-fraction point membership.** If `A` and `B` both lie in the
pentagon hull, then for any segment fraction `s ∈ [0,1]` the point
`((1-s) A₁ + s B₁, (1-s) A₂ + s B₂)` lies in the hull. (This is
`macPentagonRegion_combo_coord_mem` with `α := 1 - s`, reading the convex
combination as "start at `A`, move fraction `s` toward `B`".) -/
theorem mac_segment_pt_mem
    (I₁ I₂ Iboth : ℝ) {A B : ℝ × ℝ}
    (hA : A ∈ macPentagonRegion I₁ I₂ Iboth)
    (hB : B ∈ macPentagonRegion I₁ I₂ Iboth)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((1 - s) * A.1 + s * B.1, (1 - s) * A.2 + s * B.2)
      ∈ macPentagonRegion I₁ I₂ Iboth := by
  have hα0 : 0 ≤ 1 - s := by linarith
  have hα1 : (1 - s) ≤ 1 := by linarith
  have h := macPentagonRegion_combo_coord_mem I₁ I₂ Iboth hA hB hα0 hα1
  -- `1 - (1 - s) = s`
  have hrw : (1 : ℝ) - (1 - s) = s := by ring
  rwa [hrw] at h

end SegmentFraction

/-! ## Section 4 — Geometric core: bounded point ⊆ pentagon -/

section GeometricCore

/-- **Bottom-edge point.** For `0 ≤ R₁ ≤ I₁`, the point `(R₁, 0)` lies on
the segment `(0,0)–(I₁,0)`, hence in the pentagon. -/
theorem mac_bottom_edge_mem
    (I₁ I₂ Iboth R₁ : ℝ)
    (hR₁0 : 0 ≤ R₁) (hR₁I : R₁ ≤ I₁) :
    (R₁, (0 : ℝ)) ∈ macPentagonRegion I₁ I₂ Iboth := by
  rcases eq_or_lt_of_le hR₁0 with hR₁eq | hR₁pos
  · -- R₁ = 0 : the origin vertex.
    rw [← hR₁eq]
    exact macPentagonRegion_zero_zero_mem I₁ I₂ Iboth
  · -- 0 < R₁ ≤ I₁ : segment fraction `s = R₁ / I₁`.
    have hI₁pos : 0 < I₁ := lt_of_lt_of_le hR₁pos hR₁I
    have hA := macPentagonRegion_zero_zero_mem I₁ I₂ Iboth
    have hB := macPentagonRegion_user1_cap_mem I₁ I₂ Iboth
    have h := mac_segment_pt_mem I₁ I₂ Iboth hA hB
      (s := R₁ / I₁) (by positivity)
      ((div_le_one hI₁pos).2 hR₁I)
    -- The segment point equals `(R₁, 0)`.
    have heq : ((1 - R₁ / I₁) * (0, (0 : ℝ)).1 + R₁ / I₁ * (I₁, (0 : ℝ)).1,
        (1 - R₁ / I₁) * (0, (0 : ℝ)).2 + R₁ / I₁ * (I₁, (0 : ℝ)).2)
        = (R₁, (0 : ℝ)) := by
      rw [Prod.mk.injEq]
      constructor <;> field_simp <;> ring
    rwa [heq] at h

/-- **Top point below the corner (left horizontal top edge).** For
`0 ≤ R₁ ≤ Iboth - I₂` the point `(R₁, I₂)` lies on the top-left edge
`(0,I₂)–(Iboth-I₂,I₂)`, hence in the pentagon. -/
theorem mac_top_left_mem
    (I₁ I₂ Iboth R₁ : ℝ)
    (hR₁0 : 0 ≤ R₁) (hR₁ub : R₁ ≤ Iboth - I₂)
    (_h_corner₂_nn : 0 ≤ Iboth - I₂) :
    (R₁, I₂) ∈ macPentagonRegion I₁ I₂ Iboth := by
  rcases eq_or_lt_of_le hR₁0 with hR₁eq | hR₁pos
  · -- R₁ = 0 : the user-2 cap vertex `(0, I₂)`.
    rw [← hR₁eq]
    exact macPentagonRegion_user2_cap_mem I₁ I₂ Iboth
  · -- 0 < R₁ ≤ Iboth - I₂.
    have hd_pos : 0 < Iboth - I₂ := lt_of_lt_of_le hR₁pos hR₁ub
    have hA := macPentagonRegion_user2_cap_mem I₁ I₂ Iboth
    have hB := macPentagonRegion_corner₂_mem I₁ I₂ Iboth
    have h := mac_segment_pt_mem I₁ I₂ Iboth hA hB
      (s := R₁ / (Iboth - I₂)) (by positivity)
      ((div_le_one hd_pos).2 hR₁ub)
    have heq : ((1 - R₁ / (Iboth - I₂)) * ((0 : ℝ), I₂).1
          + R₁ / (Iboth - I₂) * (Iboth - I₂, I₂).1,
        (1 - R₁ / (Iboth - I₂)) * ((0 : ℝ), I₂).2
          + R₁ / (Iboth - I₂) * (Iboth - I₂, I₂).2)
        = (R₁, I₂) := by
      rw [Prod.mk.injEq]
      constructor <;> field_simp <;> ring
    rwa [heq] at h

/-- **Top point past the corner (sum-saturating top edge).** For
`Iboth - I₂ ≤ R₁ ≤ I₁` the point `(R₁, Iboth - R₁)` lies on the
sum-saturating edge `(I₁, Iboth-I₁)–(Iboth-I₂, I₂)`, hence in the
pentagon. -/
theorem mac_top_right_mem
    (I₁ I₂ Iboth R₁ : ℝ)
    (hR₁lb : Iboth - I₂ ≤ R₁) (hR₁ub : R₁ ≤ I₁)
    (_h_corner₂_sub : Iboth - I₂ ≤ I₁) :
    (R₁, Iboth - R₁) ∈ macPentagonRegion I₁ I₂ Iboth := by
  rcases eq_or_lt_of_le hR₁ub with hR₁eq | hR₁lt
  · -- R₁ = I₁ : the first sum-saturating corner `(I₁, Iboth - I₁)`.
    rw [hR₁eq]
    exact macPentagonRegion_corner₁_mem I₁ I₂ Iboth
  · -- Iboth - I₂ ≤ R₁ < I₁ : segment from corner₁ toward corner₂.
    -- denominator `I₁ - (Iboth - I₂) > 0`.
    have hden : 0 < I₁ - (Iboth - I₂) := by linarith
    have hA := macPentagonRegion_corner₁_mem I₁ I₂ Iboth
    have hB := macPentagonRegion_corner₂_mem I₁ I₂ Iboth
    -- fraction `s = (I₁ - R₁) / (I₁ - (Iboth - I₂))`, in `[0, 1]`.
    have hs0 : 0 ≤ (I₁ - R₁) / (I₁ - (Iboth - I₂)) := by
      apply div_nonneg <;> linarith
    have hs1 : (I₁ - R₁) / (I₁ - (Iboth - I₂)) ≤ 1 := by
      rw [div_le_one hden]; linarith
    have h := mac_segment_pt_mem I₁ I₂ Iboth hA hB hs0 hs1
    have heq : ((1 - (I₁ - R₁) / (I₁ - (Iboth - I₂))) * (I₁, Iboth - I₁).1
          + (I₁ - R₁) / (I₁ - (Iboth - I₂)) * (Iboth - I₂, I₂).1,
        (1 - (I₁ - R₁) / (I₁ - (Iboth - I₂))) * (I₁, Iboth - I₁).2
          + (I₁ - R₁) / (I₁ - (Iboth - I₂)) * (Iboth - I₂, I₂).2)
        = (R₁, Iboth - R₁) := by
      rw [Prod.mk.injEq]
      constructor <;> field_simp <;> ring
    rwa [heq] at h

/-- **Geometric core — bounded rate pair lies in the pentagon.** A rate
pair `(R₁, R₂)` satisfying the three corner-point bounds together with the
two non-negativity bounds is a convex combination of the five pentagon
vertices.

The decomposition is a two-level segment lift: `(R₁, R₂)` lies on the
vertical segment from the bottom-edge point `(R₁, 0)` up to the upper
boundary point at horizontal position `R₁`, the latter being `(R₁, I₂)`
when `R₁ ≤ Iboth - I₂` (left horizontal top edge) and `(R₁, Iboth - R₁)`
otherwise (sum-saturating edge). -/
theorem mac_point_mem_pentagon_of_bounds
    (I₁ I₂ Iboth R₁ R₂ : ℝ)
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (hR₁I : R₁ ≤ I₁) (hR₂I : R₂ ≤ I₂)
    (hsum : R₁ + R₂ ≤ Iboth)
    (_h_corner₁_sub : Iboth - I₁ ≤ I₂)
    (h_corner₂_sub : Iboth - I₂ ≤ I₁)
    (h_corner₂_nn : 0 ≤ Iboth - I₂) :
    (R₁, R₂) ∈ macPentagonRegion I₁ I₂ Iboth := by
  -- The bottom-edge point `(R₁, 0)` is always in the pentagon.
  have hbot := mac_bottom_edge_mem I₁ I₂ Iboth R₁ hR₁0 hR₁I
  rcases le_or_gt R₁ (Iboth - I₂) with hcase | hcase
  · -- Left horizontal top edge : upper point `(R₁, I₂)`.
    have htop := mac_top_left_mem I₁ I₂ Iboth R₁ hR₁0 hcase h_corner₂_nn
    rcases eq_or_lt_of_le hR₂0 with hR₂eq | hR₂pos
    · -- R₂ = 0 : the bottom-edge point itself.
      rw [← hR₂eq]; exact hbot
    · -- 0 < R₂ ≤ I₂ : vertical lift, fraction `s = R₂ / I₂`.
      have hI₂pos : 0 < I₂ := lt_of_lt_of_le hR₂pos hR₂I
      have h := mac_segment_pt_mem I₁ I₂ Iboth hbot htop
        (s := R₂ / I₂) (by positivity) ((div_le_one hI₂pos).2 hR₂I)
      have heq : ((1 - R₂ / I₂) * (R₁, (0 : ℝ)).1 + R₂ / I₂ * (R₁, I₂).1,
          (1 - R₂ / I₂) * (R₁, (0 : ℝ)).2 + R₂ / I₂ * (R₁, I₂).2)
          = (R₁, R₂) := by
        rw [Prod.mk.injEq]
        constructor <;> field_simp <;> ring
      rwa [heq] at h
  · -- Sum-saturating top edge : upper point `(R₁, Iboth - R₁)`.
    have htop := mac_top_right_mem I₁ I₂ Iboth R₁ (le_of_lt hcase) hR₁I h_corner₂_sub
    -- height available above `R₁` : `Iboth - R₁ ≥ R₂ ≥ 0`.
    have hheight : R₂ ≤ Iboth - R₁ := by linarith
    rcases eq_or_lt_of_le hR₂0 with hR₂eq | hR₂pos
    · rw [← hR₂eq]; exact hbot
    · have hd_pos : 0 < Iboth - R₁ := lt_of_lt_of_le hR₂pos hheight
      have h := mac_segment_pt_mem I₁ I₂ Iboth hbot htop
        (s := R₂ / (Iboth - R₁)) (by positivity) ((div_le_one hd_pos).2 hheight)
      have heq : ((1 - R₂ / (Iboth - R₁)) * (R₁, (0 : ℝ)).1
            + R₂ / (Iboth - R₁) * (R₁, Iboth - R₁).1,
          (1 - R₂ / (Iboth - R₁)) * (R₁, (0 : ℝ)).2
            + R₂ / (Iboth - R₁) * (R₁, Iboth - R₁).2)
          = (R₁, R₂) := by
        rw [Prod.mk.injEq]
        constructor <;> field_simp <;> ring
      rwa [heq] at h

end GeometricCore

/-! ## Section 5 — `IsMACTimeSharingHyp` discharge + pentagon = region -/

section Discharge

/-- **Discharge of `IsMACTimeSharingHyp` under non-negativity.** Given the
two non-negativity bounds and the pentagon's geometric side conditions,
the time-sharing decomposition predicate holds: every corner-point
achievable pair lies in the pentagon hull. -/
theorem mac_time_sharing_hyp_of_nonneg
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (h_corner₁_sub : Iboth - I₁ ≤ I₂)
    (h_corner₂_sub : Iboth - I₂ ≤ I₁)
    (h_corner₂_nn : 0 ≤ Iboth - I₂) :
    IsMACTimeSharingHyp R₁ R₂ I₁ I₂ Iboth := by
  intro h_region
  exact mac_point_mem_pentagon_of_bounds I₁ I₂ Iboth R₁ R₂ hR₁0 hR₂0
    h_region.bound₁ h_region.bound₂ h_region.boundSum
    h_corner₁_sub h_corner₂_sub h_corner₂_nn

/-- **Capacity region ⊆ pentagon (discharged form).** Every corner-point
achievable pair with non-negative rates lies in the pentagon hull — the
reverse inclusion, now with the time-sharing hypothesis discharged. -/
theorem mac_capacity_region_subset_pentagon_of_nonneg
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (h_region : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth)
    (h_corner₁_sub : Iboth - I₁ ≤ I₂)
    (h_corner₂_sub : Iboth - I₂ ≤ I₁)
    (h_corner₂_nn : 0 ≤ Iboth - I₂) :
    (R₁, R₂) ∈ macPentagonRegion I₁ I₂ Iboth :=
  mac_time_sharing_hyp_of_nonneg R₁ R₂ I₁ I₂ Iboth hR₁0 hR₂0
    h_corner₁_sub h_corner₂_sub h_corner₂_nn h_region

/-- **Pentagon = capacity region ∩ first quadrant (fully discharged).**
Under the pentagon's geometric side conditions, the pentagon hull is
exactly the set of corner-point achievable pairs with non-negative rates.
Both inclusions are now discharged: `⊇` is `mac_pentagon_subset_region`
(restricted), and `⊆` adds the non-negativity that pentagon membership
forces (vertices are first-quadrant). -/
theorem mac_capacity_region_is_pentagon_of_nonneg
    (I₁ I₂ Iboth : ℝ)
    (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂)
    (h_cut_ub : Iboth ≤ I₁ + I₂)
    (h_corner₁_sub : Iboth - I₁ ≤ I₂)
    (h_corner₂_sub : Iboth - I₂ ≤ I₁)
    (h_corner₁_nn : 0 ≤ Iboth - I₁)
    (h_corner₂_nn : 0 ≤ Iboth - I₂) :
    macPentagonRegion I₁ I₂ Iboth
      = { p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2
            ∧ InMACCapacityRegion p.1 p.2 I₁ I₂ Iboth } := by
  apply Set.eq_of_subset_of_subset
  · -- pentagon ⊆ {nonneg ∧ in region}
    have hI_sum_nn : (0 : ℝ) ≤ Iboth := by linarith
    -- non-negativity of the first coordinate on the pentagon.
    have hnn1 : macPentagonRegion I₁ I₂ Iboth ⊆ { p : ℝ × ℝ | 0 ≤ p.1 } := by
      refine convexHull_min ?_ ?_
      · intro v hv
        simp only [macPentagonVertices, Finset.coe_insert,
          Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with hv | hv | hv | hv | hv <;> rw [hv] <;>
          simp only [Set.mem_setOf_eq] <;> linarith
      · intro x hx y hy a b ha hb _
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have : (a • x + b • y).1 = a * x.1 + b * y.1 := by
          simp [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [this]; positivity
    -- non-negativity of the second coordinate on the pentagon.
    have hnn2 : macPentagonRegion I₁ I₂ Iboth ⊆ { p : ℝ × ℝ | 0 ≤ p.2 } := by
      refine convexHull_min ?_ ?_
      · intro v hv
        simp only [macPentagonVertices, Finset.coe_insert,
          Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with hv | hv | hv | hv | hv <;> rw [hv] <;>
          simp only [Set.mem_setOf_eq] <;> linarith
      · intro x hx y hy a b ha hb _
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have : (a • x + b • y).2 = a * x.2 + b * y.2 := by
          simp [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [this]; positivity
    have hreg := mac_pentagon_subset_region I₁ I₂ Iboth hI₁ hI₂ h_cut_ub
      h_corner₁_sub h_corner₂_sub h_corner₁_nn h_corner₂_nn
    intro p hp
    exact ⟨hnn1 hp, hnn2 hp, hreg hp⟩
  · rintro p ⟨hp1, hp2, hp_reg⟩
    have := mac_capacity_region_subset_pentagon_of_nonneg p.1 p.2 I₁ I₂ Iboth
      hp1 hp2 hp_reg h_corner₁_sub h_corner₂_sub h_corner₂_nn
    simpa using this

end Discharge

end InformationTheory.Shannon
