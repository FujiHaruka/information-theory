import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Marton.SupportReduction
import InformationTheory.Shannon.WynerZiv.ConditionalEntropyConvexity
import Mathlib.Analysis.Convex.Function

/-!
# Convexity of the auxiliary-weight objective

Fix a family of conditional laws `k u : V × Z → ℝ` indexed by an auxiliary alphabet `U`, a
coefficient vector `w : U → ℝ`, a constant `c` and a nonnegative scalar `t`.  The objective
attached to a weight vector `q : U → ℝ` is `c`, plus the linear form `∑ u, q u * w u`, plus `t`
times the negated conditional entropy `-H(V | Z)` of the mixture `∑ u, q u * k u`.  A general
coefficient is needed because the entropy differences a cardinality bound has to control come
with weights of their own, including the degenerate weight `0`.  This is the shape the elementary
cardinality argument for the Marton inner bound optimizes: with the conditional law held fixed, the
entropy terms split into a part that is affine in the weights and a single genuinely convex part.

Convexity of the entropy part is `convexOn_negCondEntropy`, stated for the joint law directly and
transported to the weights along the linear aggregation `q ↦ ∑ u, q u * k u`.  The resulting
objective is convex on the nonnegative orthant, so it can be fed to
`exists_support_card_le_of_convexOn`: the weights can be replaced by weights supported on at most
`Fintype.card X` indices, keeping the induced law on `X` and not decreasing the objective.

Exchanging the roles of the two coordinates of the conditional law turns the same convexity
statement into convexity of `-H(Z | V)`, so a second slot with its own nonnegative coefficient can
be carried alongside the first one.  Both negated conditional entropies of a pair are therefore
available at once, which is what the weighted sum of the region informations needs when the weight
of the second region inequality is not zero.

## Main definitions

* `auxWeightObjective` — the scalar objective as a function of the weight vector.
* `auxWeightObjectiveTwoSlot` — the objective carrying a second convex slot, the negated
  conditional entropy of the mixture with the two coordinates exchanged.

## Main statements

* `convexOn_auxWeightObjective` — the objective is convex on the nonnegative orthant.
* `exists_support_card_le_auxWeightObjective` — the weights can be replaced by weights supported
  on at most `Fintype.card X` indices without decreasing the objective.
* `exists_support_card_le_auxWeightObjective_add_aggregate` — the same conclusion for the
  objective carrying an additional term that reads the weights only through the aggregate.
* `convexOn_auxWeightObjectiveTwoSlot` — the two-slot objective is convex on the nonnegative
  orthant.
* `exists_support_card_le_auxWeightObjectiveTwoSlot_add_aggregate` — support reduction for the
  two-slot objective carrying an additional term that reads the weights only through the
  aggregate.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

variable {U V Z X : Type*} [Fintype U] [Fintype V] [Fintype Z] [Fintype X]

lemma convex_setOf_nonneg {ι : Type*} : Convex ℝ {q : ι → ℝ | 0 ≤ q} := by
  intro x hx y hy a b ha hb _ i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem convexOn_negCondEntropy :
    ConvexOn ℝ {r : V × Z → ℝ | 0 ≤ r}
      (fun r ↦ (∑ z, Real.negMulLog (∑ v, r (v, z))) - ∑ p : V × Z, Real.negMulLog (r p)) := by
  refine ⟨convex_setOf_nonneg, fun r₁ h₁ r₂ h₂ a b ha hb hab ↦ ?_⟩
  -- The per-atom core below carries measurable-space arguments that its statement never uses;
  -- discharging them locally keeps them off the signatures in this file.
  letI : MeasurableSpace V := ⊤
  letI : MeasurableSpace Z := ⊤
  have key := negMulLog_marginal_gap_le_joint_gap r₁ r₂ h₁ h₂ a b ha hb hab
  have hflip : ∀ g : V × Z → ℝ, ∑ z, ∑ v, g (v, z) = ∑ p : V × Z, g p := by
    intro g; rw [Finset.sum_comm]; exact (Fintype.sum_prod_type (f := g)).symm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hflip fun p ↦ Real.negMulLog (r₁ p), ← hflip fun p ↦ Real.negMulLog (r₂ p),
    ← hflip fun p ↦ Real.negMulLog (a * r₁ p + b * r₂ p)]
  linarith [key]

theorem convexOn_negCondEntropy_mixture (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) :
    ConvexOn ℝ {q : U → ℝ | 0 ≤ q}
      (fun q ↦ (∑ z, Real.negMulLog (∑ v, ∑ u, q u * k u (v, z)))
        - ∑ p : V × Z, Real.negMulLog (∑ u, q u * k u p)) := by
  classical
  let L : (U → ℝ) →ₗ[ℝ] (V × Z → ℝ) :=
    { toFun := fun q p ↦ ∑ u, q u * k u p
      map_add' := fun q₁ q₂ ↦ by
        funext p; simp only [Pi.add_apply, add_mul]; exact Finset.sum_add_distrib
      map_smul' := fun t q ↦ by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hsub : {q : U → ℝ | 0 ≤ q} ⊆ (⇑L) ⁻¹' {r : V × Z → ℝ | 0 ≤ r} :=
    fun q hq p ↦ Finset.sum_nonneg fun u _ ↦ mul_nonneg (hq u) (hk u p)
  exact (convexOn_negCondEntropy.comp_linearMap (E := (U → ℝ)) L).subset hsub convex_setOf_nonneg

theorem convexOn_negCondEntropy_mixture_transpose (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) :
    ConvexOn ℝ {q : U → ℝ | 0 ≤ q}
      (fun q ↦ (∑ v, Real.negMulLog (∑ z, ∑ u, q u * k u (v, z)))
        - ∑ p : V × Z, Real.negMulLog (∑ u, q u * k u p)) := by
  refine (convexOn_negCondEntropy_mixture (V := Z) (Z := V) (fun u p ↦ k u (p.2, p.1))
    fun u p ↦ hk u (p.2, p.1)).congr fun q _ ↦ ?_
  dsimp only
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm Z V)
    (fun p : Z × V ↦ Real.negMulLog (∑ u, q u * k u (p.2, p.1)))
    (fun p : V × Z ↦ Real.negMulLog (∑ u, q u * k u p)) fun p ↦ rfl

lemma convexOn_sum_mul (w : U → ℝ) :
    ConvexOn ℝ {q : U → ℝ | 0 ≤ q} (fun q ↦ ∑ u, q u * w u) := by
  refine ⟨convex_setOf_nonneg, fun q₁ _ q₂ _ a b _ _ _ ↦ le_of_eq ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, Finset.mul_sum]
  exact Finset.sum_add_distrib

/-- The scalar objective attached to a family of conditional laws `k`, a coefficient vector `w`,
a constant `c` and a scalar `t`.  Its value at a weight vector `q` is `c`, plus the linear form
`∑ u, q u * w u`, plus `t` times the negated conditional entropy of the mixture
`∑ u, q u * k u`. -/
noncomputable def auxWeightObjective (k : U → V × Z → ℝ) (w : U → ℝ) (c t : ℝ) (q : U → ℝ) : ℝ :=
  c + (∑ u, q u * w u)
    + t * ((∑ z, Real.negMulLog (∑ v, ∑ u, q u * k u (v, z)))
      - ∑ p : V × Z, Real.negMulLog (∑ u, q u * k u p))

/-- The auxiliary-weight objective is convex on the nonnegative orthant, for a nonnegative
coefficient on the entropy part. -/
@[entry_point]
theorem convexOn_auxWeightObjective (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) (w : U → ℝ)
    (c t : ℝ) (ht : 0 ≤ t) : ConvexOn ℝ {q : U → ℝ | 0 ≤ q} (auxWeightObjective k w c t) :=
  ((convexOn_const c convex_setOf_nonneg).add (convexOn_sum_mul w)).add
    (by simpa only [smul_eq_mul] using (convexOn_negCondEntropy_mixture k hk).smul ht)

/-- A nonnegative weight vector can be replaced by one supported on at most `Fintype.card X`
indices, keeping the aggregate `fun x ↦ ∑ u, q u * A u x` and not decreasing the
auxiliary-weight objective, provided every row `A u` sums to one. -/
@[entry_point]
theorem exists_support_card_le_auxWeightObjective (A : U → X → ℝ) (hA : ∀ u, ∑ x, A u x = 1)
    (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) (w : U → ℝ) (c t : ℝ) (ht : 0 ≤ t) (q : U → ℝ)
    (hq : 0 ≤ q) :
    ∃ q' : U → ℝ, 0 ≤ q' ∧ (∀ x, ∑ u, q' u * A u x = ∑ u, q u * A u x) ∧
      auxWeightObjective k w c t q ≤ auxWeightObjective k w c t q' ∧
      {u | q' u ≠ 0}.ncard ≤ Fintype.card X :=
  exists_support_card_le_of_convexOn A hA (auxWeightObjective k w c t)
    (convexOn_auxWeightObjective k hk w c t ht) q hq

/-- Support reduction for the auxiliary-weight objective still applies when the objective carries
an additional term `g` that reads the weights only through the aggregate
`fun x ↦ ∑ u, q u * A u x`.  Nothing is assumed about `g`, because the reduced weights leave the
aggregate unchanged. -/
@[entry_point]
theorem exists_support_card_le_auxWeightObjective_add_aggregate (A : U → X → ℝ)
    (hA : ∀ u, ∑ x, A u x = 1) (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) (w : U → ℝ) (c t : ℝ)
    (ht : 0 ≤ t) (g : (X → ℝ) → ℝ) (q : U → ℝ) (hq : 0 ≤ q) :
    ∃ q' : U → ℝ, 0 ≤ q' ∧ (∀ x, ∑ u, q' u * A u x = ∑ u, q u * A u x) ∧
      auxWeightObjective k w c t q + g (fun x ↦ ∑ u, q u * A u x)
        ≤ auxWeightObjective k w c t q' + g (fun x ↦ ∑ u, q' u * A u x) ∧
      {u | q' u ≠ 0}.ncard ≤ Fintype.card X :=
  exists_support_card_le_of_convexOn_add_aggregate A hA (auxWeightObjective k w c t)
    (convexOn_auxWeightObjective k hk w c t ht) g q hq

/-- The scalar objective carrying, on top of `auxWeightObjective`, a second convex slot with
coefficient `s`: the negated conditional entropy of the mixture `∑ u, q u * k u` with the roles of
the two coordinates exchanged.  Both slots mix the same family of conditional laws `k`, so the
weighted sum of the region informations of the Marton inner bound is an instance of this shape for
the whole range of weights, not only for those making the second slot vanish. -/
noncomputable def auxWeightObjectiveTwoSlot (k : U → V × Z → ℝ) (w : U → ℝ) (c t s : ℝ)
    (q : U → ℝ) : ℝ :=
  auxWeightObjective k w c t q
    + s * ((∑ v, Real.negMulLog (∑ z, ∑ u, q u * k u (v, z)))
      - ∑ p : V × Z, Real.negMulLog (∑ u, q u * k u p))

/-- The two-slot objective is convex on the nonnegative orthant, for nonnegative coefficients on
the two entropy parts. -/
@[entry_point]
theorem convexOn_auxWeightObjectiveTwoSlot (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) (w : U → ℝ)
    (c t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ConvexOn ℝ {q : U → ℝ | 0 ≤ q} (auxWeightObjectiveTwoSlot k w c t s) :=
  (convexOn_auxWeightObjective k hk w c t ht).add
    (by simpa only [smul_eq_mul] using (convexOn_negCondEntropy_mixture_transpose k hk).smul hs)

/-- Support reduction also applies to the two-slot objective carrying an additional term `g` that
reads the weights only through the aggregate `fun x ↦ ∑ u, q u * A u x`, provided both entropy
coefficients are nonnegative. -/
@[entry_point]
theorem exists_support_card_le_auxWeightObjectiveTwoSlot_add_aggregate (A : U → X → ℝ)
    (hA : ∀ u, ∑ x, A u x = 1) (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) (w : U → ℝ)
    (c t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (g : (X → ℝ) → ℝ) (q : U → ℝ) (hq : 0 ≤ q) :
    ∃ q' : U → ℝ, 0 ≤ q' ∧ (∀ x, ∑ u, q' u * A u x = ∑ u, q u * A u x) ∧
      auxWeightObjectiveTwoSlot k w c t s q + g (fun x ↦ ∑ u, q u * A u x)
        ≤ auxWeightObjectiveTwoSlot k w c t s q' + g (fun x ↦ ∑ u, q' u * A u x) ∧
      {u | q' u ≠ 0}.ncard ≤ Fintype.card X :=
  exists_support_card_le_of_convexOn_add_aggregate A hA (auxWeightObjectiveTwoSlot k w c t s)
    (convexOn_auxWeightObjectiveTwoSlot k hk w c t s ht hs) g q hq

end InformationTheory.Shannon.BroadcastChannel.Marton
