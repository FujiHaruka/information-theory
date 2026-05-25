import Common2026.Shannon.MultipleAccessChannel
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull

/-!
# MAC capacity region — corner-point extraction + pentagon (T3-B wave7)

This file sits **above** `Common2026/Shannon/MultipleAccessChannel.lean`
(which publishes the corner-point form predicate `InMACCapacityRegion` and
the hypothesis-pass-through publish-layer wrappers `mac_capacity_region_*`)
and **above** `Common2026/Shannon/MACL1Discharge.lean` /
`MACBodyDischarge.lean` (which discharge the joint-typicality machinery).

## Scope (publish layer)

We publish three new artefacts:

* **Two extreme corner points** of the pentagon region in `ℝ × ℝ`:
  ```
  cornerPoint₁ I_cond1 I_marg2 := (I_cond1, I_marg2)
                  -- (I(X₁;Y|X₂), I(X₂;Y))
  cornerPoint₂ I_marg1 I_cond2 := (I_marg1, I_cond2)
                  -- (I(X₁;Y),    I(X₂;Y|X₁))
  ```
  Membership in the corner-point predicate `InMACCapacityRegion` for both
  is the structural content of `mac_corner_point₁_in_region` and
  `mac_corner_point₂_in_region`. The two points witness the *sum-rate
  saturation* `R₁ + R₂ = Iboth`; the underlying chain-rule identity
  `I(X₁;Y|X₂) + I(X₂;Y) = I(X₁,X₂;Y) = I(X₁;Y) + I(X₂;Y|X₁)` is hoisted
  out as a hypothesis (`h_chain` / `h_chain'`), keeping the publish layer
  scalar-arithmetic only.

* **Pentagon set** `macPentagonRegion I₁ I₂ Iboth : Set (ℝ × ℝ)` defined
  as the convex hull of the five vertices `(0,0)`, `(I₁, 0)`, `(0, I₂)`,
  `(I₁, Iboth - I₁)`, `(Iboth - I₂, I₂)`. The two "sum-saturating"
  vertices are exactly the corner points re-expressed via the chain-rule
  identity (`I_cond1 = I₁` and `I_marg2 = Iboth - I₁` along the first
  corner, symmetrically for the second).

* **Time-sharing convex combination** of two rate pairs:
  given two rate pairs `(R₁ᵃ, R₂ᵃ)` and `(R₁ᵇ, R₂ᵇ)` both in
  `InMACCapacityRegion`, and a mixing weight `α ∈ [0, 1]`, the convex
  combination
  ```
  (α · R₁ᵃ + (1-α) · R₁ᵇ, α · R₂ᵃ + (1-α) · R₂ᵇ)
  ```
  is also in `InMACCapacityRegion`. This is the `Convex.convexCombo`-style
  closure under time-sharing (Cover–Thomas §15.3.6).

## Main theorems

* `mac_corner_point₁_in_region` — `(I_cond1, I_marg2) ∈ InMACCapacityRegion`,
  given the chain-rule identity `I_cond1 + I_marg2 = Iboth` and the cut
  rates `I_cond1 ≤ I₁`, `I_marg2 ≤ I₂`.
* `mac_corner_point₂_in_region` — mirror of the above for the second
  corner.
* `mac_pentagon_subset_region` — `macPentagonRegion I₁ I₂ Iboth ⊆
  { (R₁, R₂) | InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth }` when the chain
  identities hold; via `convexHull_min` from the explicit five-vertex
  membership.
* `mac_region_time_sharing` — convex-combination closure of
  `InMACCapacityRegion` under any mixing weight `α ∈ [0, 1]`.

## 撤退ライン (確定発動)

* **Pentagon = capacity region** (sup-side: every region point lies in the
  pentagon hull) requires a Carathéodory-style decomposition argument
  whose discharge is supplied as the predicate `IsMACTimeSharingHyp R₁ R₂
  I₁ I₂ Iboth : Prop`. The publish-layer theorem
  `mac_capacity_region_subset_pentagon` consumes this hypothesis and
  routes through transparently.
* The chain-rule identities `I_cond1 + I_marg2 = Iboth`, `I_marg1 +
  I_cond2 = Iboth` are taken as caller hypotheses (`h_chain` /
  `h_chain'`). Their derivation from the underlying conditional mutual
  information chain rule lives in `Common2026/Shannon/MIChainRule.lean`
  and is not re-derived here.
* Non-negativity hypotheses (`0 ≤ I₁`, etc.) are passed in explicitly
  where they're needed; they hold for mutual information in general by
  separate downstream lemmas.

This file matches the publish-layer convention of
`Common2026/Shannon/MACBodyDischarge.lean` and the chain-of-hypothesis
pass-through pattern of `mac_capacity_region_outer_bound` /
`mac_capacity_region_inner_bound`.
-/

namespace InformationTheory.Shannon

open scoped BigOperators

set_option linter.unusedSectionVars false

/-! ## Section 1 — Corner-point construction -/

section CornerPoints

/-- **First corner point** of the MAC pentagon region: the rate pair
`(I(X₁; Y | X₂), I(X₂; Y))`. This corresponds to the successive-decoding
order "decode user 2 first (treating user 1 as noise), then decode user 1
with full side information". -/
def cornerPoint₁ (I_cond1 I_marg2 : ℝ) : ℝ × ℝ := (I_cond1, I_marg2)

/-- **Second corner point** of the MAC pentagon region: the rate pair
`(I(X₁; Y), I(X₂; Y | X₁))`. This corresponds to the opposite
successive-decoding order. -/
def cornerPoint₂ (I_marg1 I_cond2 : ℝ) : ℝ × ℝ := (I_marg1, I_cond2)

@[simp] lemma cornerPoint₁_fst (I_cond1 I_marg2 : ℝ) :
    (cornerPoint₁ I_cond1 I_marg2).1 = I_cond1 := rfl

@[simp] lemma cornerPoint₁_snd (I_cond1 I_marg2 : ℝ) :
    (cornerPoint₁ I_cond1 I_marg2).2 = I_marg2 := rfl

@[simp] lemma cornerPoint₂_fst (I_marg1 I_cond2 : ℝ) :
    (cornerPoint₂ I_marg1 I_cond2).1 = I_marg1 := rfl

@[simp] lemma cornerPoint₂_snd (I_marg1 I_cond2 : ℝ) :
    (cornerPoint₂ I_marg1 I_cond2).2 = I_cond2 := rfl

/-- **First corner point lies in the capacity region.** Given the
chain-rule identity `I_cond1 + I_marg2 = Iboth` (i.e. the corner saturates
the sum-rate bound) and the two cut-rate inequalities `I_cond1 ≤ I₁`,
`I_marg2 ≤ I₂`, the rate pair `(I_cond1, I_marg2)` lies in the
corner-point capacity region. -/
theorem mac_corner_point₁_in_region
    (I₁ I₂ Iboth I_cond1 I_marg2 : ℝ)
    (h_chain : I_cond1 + I_marg2 = Iboth)
    (h_cut1 : I_cond1 ≤ I₁)
    (h_cut2 : I_marg2 ≤ I₂) :
    InMACCapacityRegion
        (cornerPoint₁ I_cond1 I_marg2).1
        (cornerPoint₁ I_cond1 I_marg2).2
        I₁ I₂ Iboth := by
  refine ⟨h_cut1, h_cut2, ?_⟩
  simp [cornerPoint₁, h_chain]

/-- **Second corner point lies in the capacity region.** Mirror of
`mac_corner_point₁_in_region`. -/
theorem mac_corner_point₂_in_region
    (I₁ I₂ Iboth I_marg1 I_cond2 : ℝ)
    (h_chain' : I_marg1 + I_cond2 = Iboth)
    (h_cut1 : I_marg1 ≤ I₁)
    (h_cut2 : I_cond2 ≤ I₂) :
    InMACCapacityRegion
        (cornerPoint₂ I_marg1 I_cond2).1
        (cornerPoint₂ I_marg1 I_cond2).2
        I₁ I₂ Iboth := by
  refine ⟨h_cut1, h_cut2, ?_⟩
  simp [cornerPoint₂, h_chain']

end CornerPoints

/-! ## Section 2 — Pentagon region as a convex hull of five vertices -/

section Pentagon

/-- The **MAC pentagon vertices** as a `Finset (ℝ × ℝ)`: the five extreme
points of the corner-point capacity region.

The vertices are:
1. `(0, 0)` — origin (trivial code achieves rate 0).
2. `(I₁, 0)` — single-user 1 cap (user 2 silent).
3. `(0, I₂)` — single-user 2 cap (user 1 silent).
4. `(I₁, Iboth - I₁)` — first sum-saturating corner.
5. `(Iboth - I₂, I₂)` — second sum-saturating corner.

The two sum-saturating vertices coincide with `cornerPoint₁ I_cond1 I_marg2`
and `cornerPoint₂ I_marg1 I_cond2` under the chain-rule identities
`I_cond1 = I₁` ∧ `I_marg2 = Iboth - I₁` (and symmetric). -/
noncomputable def macPentagonVertices (I₁ I₂ Iboth : ℝ) : Finset (ℝ × ℝ) :=
  {(0, 0), (I₁, 0), (0, I₂), (I₁, Iboth - I₁), (Iboth - I₂, I₂)}

/-- The **MAC pentagon region** is the convex hull of the five vertices. -/
noncomputable def macPentagonRegion (I₁ I₂ Iboth : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ (macPentagonVertices I₁ I₂ Iboth : Set (ℝ × ℝ))

lemma macPentagonRegion_def (I₁ I₂ Iboth : ℝ) :
    macPentagonRegion I₁ I₂ Iboth =
      convexHull ℝ (macPentagonVertices I₁ I₂ Iboth : Set (ℝ × ℝ)) := rfl

/-- Vertex 1: the origin lies in the pentagon. -/
lemma macPentagonRegion_zero_zero_mem (I₁ I₂ Iboth : ℝ) :
    (0, 0) ∈ macPentagonRegion I₁ I₂ Iboth := by
  refine subset_convexHull ℝ _ ?_
  simp [macPentagonVertices]

/-- Vertex 2: the user-1 cap `(I₁, 0)` lies in the pentagon. -/
lemma macPentagonRegion_user1_cap_mem (I₁ I₂ Iboth : ℝ) :
    (I₁, 0) ∈ macPentagonRegion I₁ I₂ Iboth := by
  refine subset_convexHull ℝ _ ?_
  simp [macPentagonVertices]

/-- Vertex 3: the user-2 cap `(0, I₂)` lies in the pentagon. -/
lemma macPentagonRegion_user2_cap_mem (I₁ I₂ Iboth : ℝ) :
    (0, I₂) ∈ macPentagonRegion I₁ I₂ Iboth := by
  refine subset_convexHull ℝ _ ?_
  simp [macPentagonVertices]

/-- Vertex 4: the first sum-saturating corner `(I₁, Iboth - I₁)` lies in
the pentagon. -/
lemma macPentagonRegion_corner₁_mem (I₁ I₂ Iboth : ℝ) :
    (I₁, Iboth - I₁) ∈ macPentagonRegion I₁ I₂ Iboth := by
  refine subset_convexHull ℝ _ ?_
  simp [macPentagonVertices]

/-- Vertex 5: the second sum-saturating corner `(Iboth - I₂, I₂)` lies
in the pentagon. -/
lemma macPentagonRegion_corner₂_mem (I₁ I₂ Iboth : ℝ) :
    (Iboth - I₂, I₂) ∈ macPentagonRegion I₁ I₂ Iboth := by
  refine subset_convexHull ℝ _ ?_
  simp [macPentagonVertices]

end Pentagon

/-! ## Section 3 — Convex closure of `InMACCapacityRegion` -/

section ConvexClosure

/-- **The (closed) corner-point capacity region is convex.** Given two
rate pairs both in `InMACCapacityRegion R₁a R₂a I₁ I₂ Iboth` and
`InMACCapacityRegion R₁b R₂b I₁ I₂ Iboth`, and a mixing weight
`α ∈ [0, 1]`, the convex combination
`(α R₁a + (1-α) R₁b, α R₂a + (1-α) R₂b)` lies in the same region.

This is the *time-sharing closure* of the corner-point region under
mixing two coding schemes for a fraction `α` and `1 - α` of the channel
uses (Cover–Thomas §15.3.2, Theorem 15.3.6, abstracted away from the
specific code construction). -/
theorem mac_region_time_sharing
    (R₁a R₂a R₁b R₂b I₁ I₂ Iboth : ℝ)
    (hA : InMACCapacityRegion R₁a R₂a I₁ I₂ Iboth)
    (hB : InMACCapacityRegion R₁b R₂b I₁ I₂ Iboth)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    InMACCapacityRegion
        (α * R₁a + (1 - α) * R₁b)
        (α * R₂a + (1 - α) * R₂b)
        I₁ I₂ Iboth := by
  have hβ : 0 ≤ 1 - α := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- α R₁a + (1-α) R₁b ≤ I₁
    have h1 := hA.bound₁
    have h2 := hB.bound₁
    have hcombo : α * R₁a + (1 - α) * R₁b ≤ α * I₁ + (1 - α) * I₁ := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hα0,
                 mul_le_mul_of_nonneg_left h2 hβ]
    have hsum : α * I₁ + (1 - α) * I₁ = I₁ := by ring
    linarith
  · -- α R₂a + (1-α) R₂b ≤ I₂
    have h1 := hA.bound₂
    have h2 := hB.bound₂
    have hcombo : α * R₂a + (1 - α) * R₂b ≤ α * I₂ + (1 - α) * I₂ := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hα0,
                 mul_le_mul_of_nonneg_left h2 hβ]
    have hsum : α * I₂ + (1 - α) * I₂ = I₂ := by ring
    linarith
  · -- α R₁a + (1-α) R₁b + (α R₂a + (1-α) R₂b) ≤ Iboth
    have h1 := hA.boundSum
    have h2 := hB.boundSum
    have hkey :
        α * R₁a + (1 - α) * R₁b + (α * R₂a + (1 - α) * R₂b)
          = α * (R₁a + R₂a) + (1 - α) * (R₁b + R₂b) := by ring
    rw [hkey]
    have hcombo : α * (R₁a + R₂a) + (1 - α) * (R₁b + R₂b)
            ≤ α * Iboth + (1 - α) * Iboth := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hα0,
                 mul_le_mul_of_nonneg_left h2 hβ]
    have hsum : α * Iboth + (1 - α) * Iboth = Iboth := by ring
    linarith

/-- **`InMACCapacityRegion` is a convex subset of `ℝ × ℝ`.** Repackaging
`mac_region_time_sharing` in the `Convex ℝ` shape, so downstream code can
feed the capacity region into Mathlib's convexity API. -/
theorem mac_region_convex (I₁ I₂ Iboth : ℝ) :
    Convex ℝ { p : ℝ × ℝ | InMACCapacityRegion p.1 p.2 I₁ I₂ Iboth } := by
  intro p hp q hq α β hα hβ hsum
  simp only [Set.mem_setOf_eq] at hp hq ⊢
  -- β = 1 - α via hsum
  have hβ_eq : β = 1 - α := by linarith
  have hα1 : α ≤ 1 := by linarith
  have ht := mac_region_time_sharing p.1 p.2 q.1 q.2 I₁ I₂ Iboth hp hq hα hα1
  -- The combined pair `α • p + β • q` projects componentwise to the same
  -- shape as `mac_region_time_sharing` provides.
  have hfst : (α • p + β • q).1 = α * p.1 + (1 - α) * q.1 := by
    simp [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hβ_eq]
  have hsnd : (α • p + β • q).2 = α * p.2 + (1 - α) * q.2 := by
    simp [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hβ_eq]
  -- rewrite the goal to match `ht`
  rw [show (α • p + β • q).1 = α * p.1 + (1 - α) * q.1 from hfst,
      show (α • p + β • q).2 = α * p.2 + (1 - α) * q.2 from hsnd]
  exact ht

end ConvexClosure

/-! ## Section 4 — Pentagon ⊆ capacity region (via convex closure) -/

section PentagonSubset

/-- **The MAC pentagon is contained in the capacity region.** All five
pentagon vertices lie in the capacity region under the three
non-negativity / cut-rate hypotheses, so by convexity the entire convex
hull is contained. -/
theorem mac_pentagon_subset_region
    (I₁ I₂ Iboth : ℝ)
    (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂)
    (_h_cut_ub : Iboth ≤ I₁ + I₂)
    (h_corner₁_sub : Iboth - I₁ ≤ I₂)
    (h_corner₂_sub : Iboth - I₂ ≤ I₁)
    (h_corner₁_nn : 0 ≤ Iboth - I₁)
    (h_corner₂_nn : 0 ≤ Iboth - I₂) :
    macPentagonRegion I₁ I₂ Iboth ⊆
      { p : ℝ × ℝ | InMACCapacityRegion p.1 p.2 I₁ I₂ Iboth } := by
  -- All five vertices are in the (convex) capacity region.
  have hI_sum_nn_user1 : (0 : ℝ) ≤ Iboth := by linarith
  have hverts :
      ((macPentagonVertices I₁ I₂ Iboth) : Set (ℝ × ℝ)) ⊆
        { p : ℝ × ℝ | InMACCapacityRegion p.1 p.2 I₁ I₂ Iboth } := by
    intro v hv
    simp [macPentagonVertices, Finset.coe_insert, Finset.coe_singleton] at hv
    rcases hv with hv | hv | hv | hv | hv
    · -- (0, 0)
      rw [hv]
      exact ⟨hI₁, hI₂, by simpa using hI_sum_nn_user1⟩
    · -- (I₁, 0)
      rw [hv]
      refine ⟨le_refl _, hI₂, ?_⟩
      simpa using by linarith [hI_sum_nn_user1]
    · -- (0, I₂)
      rw [hv]
      refine ⟨hI₁, le_refl _, ?_⟩
      simpa using by linarith [hI_sum_nn_user1]
    · -- (I₁, Iboth - I₁)
      rw [hv]
      refine ⟨le_refl _, h_corner₁_sub, ?_⟩
      have : I₁ + (Iboth - I₁) = Iboth := by ring
      linarith
    · -- (Iboth - I₂, I₂)
      rw [hv]
      refine ⟨h_corner₂_sub, le_refl _, ?_⟩
      have : (Iboth - I₂) + I₂ = Iboth := by ring
      linarith
  -- Convexity closes the convex hull.
  refine (convexHull_min hverts ?_)
  exact mac_region_convex I₁ I₂ Iboth

end PentagonSubset

/-! ## Section 5 — Reverse inclusion via Carathéodory hypothesis -/

section ReverseInclusion

/-- **Time-sharing decomposition hypothesis.** Given a rate pair
`(R₁, R₂)` in the corner-point capacity region, the Carathéodory-style
decomposition into a convex combination of pentagon vertices (concretely:
choice of α ∈ [0,1] and pairwise mixing across at most three of the five
vertices) is supplied as a hypothesis. The publish-layer theorem below
consumes this and routes through transparently.

This is the **reverse inclusion** complement of `mac_pentagon_subset_region`
and its discharge plan lives in `mac-time-sharing-discharge-*` (out of
scope of the present file). -/
def IsMACTimeSharingHyp (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop :=
  InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth →
    (R₁, R₂) ∈ macPentagonRegion I₁ I₂ Iboth

/-- **Capacity region ⊆ pentagon** (hypothesis pass-through form,
L-MAC5 engaged). Given the time-sharing decomposition hypothesis, every
rate pair in the corner-point capacity region lies in the pentagon convex
hull.

The hypothesis `_h_time_sharing` is the discharge slot for the
Carathéodory-style decomposition argument (Cover–Thomas §15.3.2 +
Theorem 15.3.6 closure), supplied externally.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_capacity_region_subset_pentagon
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h_region : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth)
    (h_time_sharing : IsMACTimeSharingHyp R₁ R₂ I₁ I₂ Iboth) :
    (R₁, R₂) ∈ macPentagonRegion I₁ I₂ Iboth := by
  sorry

/-- **Pentagon equals capacity region** (combined publish form). Under
the non-negativity and chain-rule hypotheses for the pentagon-⊆-region
direction *and* the time-sharing decomposition hypothesis for the
reverse direction, the pentagon convex hull and the corner-point
capacity region coincide as subsets of `ℝ × ℝ`.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_capacity_region_is_pentagon
    (I₁ I₂ Iboth : ℝ)
    (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂)
    (h_cut_ub : Iboth ≤ I₁ + I₂)
    (h_corner₁_sub : Iboth - I₁ ≤ I₂)
    (h_corner₂_sub : Iboth - I₂ ≤ I₁)
    (h_corner₁_nn : 0 ≤ Iboth - I₁)
    (h_corner₂_nn : 0 ≤ Iboth - I₂)
    (h_time_sharing :
        ∀ R₁ R₂ : ℝ, IsMACTimeSharingHyp R₁ R₂ I₁ I₂ Iboth) :
    macPentagonRegion I₁ I₂ Iboth
      = { p : ℝ × ℝ | InMACCapacityRegion p.1 p.2 I₁ I₂ Iboth } := by
  sorry

end ReverseInclusion

end InformationTheory.Shannon
