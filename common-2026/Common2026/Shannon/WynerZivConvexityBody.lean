import Common2026.Meta.EntryPoint
import Common2026.Shannon.WynerZivDischarge

/-!
# Wyner–Ziv L-WZ3 **full convexity** discharge under factorization predicate
# (T3-D continuation, Cover–Thomas 15.9 凸性)

`WynerZivDischarge.lean` discharged the *D-antitone* half of L-WZ3 plus the
affine build blocks (`wzMarginalXY` additivity / homogeneity, `stdSimplex`
convexity re-export). It deferred the **full convexity** of `R_WZ(D)` to a
follow-up plan: the Markov cross-product constraint
`q(x,y,u) · Σ q(x,y',u') = q(x,y,u') · Σ q(x,y',u)` is quadratic, so the
"convex hull of two feasible points is feasible" argument breaks at the
constraint level.

The standard route — and the one Cover–Thomas (§15.9) actually take — is to
*re-parameterise* the constraint by an **affine factorisation predicate**:

```
q(x, y, u) = κ(u | x) · P_XY(x, y)
```

where `κ : α → U → ℝ` is a transition kernel (per-row non-negativity and
per-row sum 1). On the factorised manifold:

* the Markov chain `U − X − Y` holds *automatically* (the joint factors
  `Y` out of the `U`-coupling, so `q(x,y,u)/q_X(x) = κ(u|x)` is `y`-free),
* the `(X,Y)`-marginal recovers `P_XY` (when `P_XY` is itself a pmf),
* the `stdSimplex` membership reduces to the kernel's row-stochasticity,
* and the joint is **affine in `κ`** — convex combinations of two kernels
  yield another valid kernel, hence a feasible point at convex
  combinations of `D`-budgets.

This file discharges L-WZ3 *full convexity* on this re-parameterised
manifold: the **factorisable constraint set** is convex (in the joint pmf
`q`), and under the standard Cover–Thomas convexity-of-objective hypothesis
on the kernel (Lemma 15.9 of CT — `I(X;U) − I(Y;U)` is convex in `κ`), the
rate function inherits convexity in `D`.

## Scope

* `IsWynerZivFactorizable U P_XY q` — the affine predicate
  "`q(x,y,u) = κ(u|x) · P_XY(x,y)` for some row-stochastic kernel `κ`".
* `IsWynerZivFactorizable_*` — kernel-level structural lemmas:
  Markov chain, `(X,Y)`-marginal, `stdSimplex` membership.
* `IsWynerZivFactorizable_convex_combination` — convex combinations preserve
  the predicate (the *core* affine result).
* `WynerZivFactorizableConstraint` — the factorisable refinement of
  `WynerZivConstraint`.
* `WynerZivFactorizableConstraint_convex_in_q` — the refinement is convex
  in the joint-pmf coordinate.
* `wynerZivRateFactorizable` — the rate function restricted to factorisable
  joints (the form Cover–Thomas convexity directly addresses).
* `wynerZivRateFactorizable_convex_of_objective_convex` — under the
  hypothesis that the Wyner–Ziv objective is convex in `q` on factorisable
  joints (Cover–Thomas Lemma 15.9), `R_WZ_fact(D)` is convex in `D`.

## 撤退ライン

* The Cover–Thomas Lemma 15.9 itself (convexity of `I(X;U) − I(Y;U)` in
  the kernel `κ`, on factorisable joints) is **not discharged here**. It
  is published as a *hypothesis* (`h_obj_convex`) on the convexity
  theorem, mirroring the upstream `WynerZiv.lean` pattern of carrying
  L-WZ statements as pass-through hypotheses on the Phase-D wrapper.
  Its independent discharge is a separate seed
  (`wyner-ziv-objective-convexity-discharge-*`).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## §1 Factorisation predicate -/

section FactorisationPredicate

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Affine factorisation predicate.** The joint pmf `q : α × β × U → ℝ` is
*Wyner–Ziv factorisable* over the source `P_XY : α × β → ℝ` if there exists
a transition kernel `κ : α → U → ℝ` (per-row non-negative and per-row sum
`1`) such that

```
q(x, y, u) = κ(u | x) · P_XY(x, y).
```

This is the *affine* re-parameterisation underlying Cover–Thomas §15.9; the
quadratic Markov cross-product constraint is automatically satisfied (see
`IsWynerZivFactorizable_markov` below). -/
def IsWynerZivFactorizable
    (P_XY : α × β → ℝ) (q : α × β × U → ℝ) : Prop :=
  ∃ κ : α → U → ℝ,
    (∀ x u, 0 ≤ κ x u)
    ∧ (∀ x, ∑ u, κ x u = 1)
    ∧ (∀ x y u, q (x, y, u) = κ x u * P_XY (x, y))

/-- Membership unfold for `IsWynerZivFactorizable`. -/
lemma IsWynerZivFactorizable_iff
    (P_XY : α × β → ℝ) (q : α × β × U → ℝ) :
    IsWynerZivFactorizable U P_XY q ↔
      ∃ κ : α → U → ℝ,
        (∀ x u, 0 ≤ κ x u)
        ∧ (∀ x, ∑ u, κ x u = 1)
        ∧ (∀ x y u, q (x, y, u) = κ x u * P_XY (x, y)) := Iff.rfl

end FactorisationPredicate

/-! ## §2 Structural consequences on factorisable joints -/

section FactorisableStructure

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Markov chain holds automatically on factorisable joints.** The
quadratic cross-product equation collapses to a kernel-level identity that
is trivially symmetric in `u, u'`. -/
lemma IsWynerZivFactorizable_markov
    (P_XY : α × β → ℝ) {q : α × β × U → ℝ}
    (hq : IsWynerZivFactorizable U P_XY q) :
    wzMarkovCrossEq U q := by
  rcases hq with ⟨κ, _hκnn, _hκsum, hκeq⟩
  intro x y u u'
  -- Goal: q(x,y,u) · Σ q(x,y',u') = q(x,y,u') · Σ q(x,y',u).
  -- Each side factors as κ(x,u) · κ(x,u') · P_XY(x,y) · Σ P_XY(x,y').
  have h_lhs :
      q (x, y, u) * (∑ y', q (x, y', u'))
        = κ x u * κ x u' * P_XY (x, y) * (∑ y', P_XY (x, y')) := by
    rw [hκeq]
    have : (∑ y', q (x, y', u')) = κ x u' * (∑ y', P_XY (x, y')) := by
      simp_rw [hκeq]
      rw [← Finset.mul_sum]
    rw [this]; ring
  have h_rhs :
      q (x, y, u') * (∑ y', q (x, y', u))
        = κ x u' * κ x u * P_XY (x, y) * (∑ y', P_XY (x, y')) := by
    rw [hκeq]
    have : (∑ y', q (x, y', u)) = κ x u * (∑ y', P_XY (x, y')) := by
      simp_rw [hκeq]
      rw [← Finset.mul_sum]
    rw [this]; ring
  rw [h_lhs, h_rhs]; ring

/-- **`(X, Y)`-marginal of a factorisable joint recovers `P_XY`** (when the
kernel `κ` is row-stochastic). -/
lemma IsWynerZivFactorizable_marginalXY
    (P_XY : α × β → ℝ) {q : α × β × U → ℝ}
    (hq : IsWynerZivFactorizable U P_XY q) :
    wzMarginalXY U q = P_XY := by
  rcases hq with ⟨κ, _hκnn, hκsum, hκeq⟩
  funext p
  unfold wzMarginalXY
  -- Goal: Σ_u q(p.1, p.2, u) = P_XY p.
  -- Each term factors: q(p.1, p.2, u) = κ(p.1, u) · P_XY p.
  have h_rewrite : ∀ u, q (p.1, p.2, u) = κ p.1 u * P_XY p := by
    intro u
    rw [hκeq p.1 p.2 u]
  calc (∑ u, q (p.1, p.2, u))
      = ∑ u, κ p.1 u * P_XY p := by
        refine Finset.sum_congr rfl ?_
        intro u _; exact h_rewrite u
    _ = (∑ u, κ p.1 u) * P_XY p := by rw [← Finset.sum_mul]
    _ = 1 * P_XY p := by rw [hκsum p.1]
    _ = P_XY p := by rw [one_mul]

/-- **Factorisable joints are non-negative pointwise** (when `P_XY` is). -/
lemma IsWynerZivFactorizable_nonneg
    (P_XY : α × β → ℝ) (h_pmf_nn : ∀ p, 0 ≤ P_XY p)
    {q : α × β × U → ℝ}
    (hq : IsWynerZivFactorizable U P_XY q) :
    ∀ p, 0 ≤ q p := by
  rcases hq with ⟨κ, hκnn, _hκsum, hκeq⟩
  intro p
  -- p = (x, y, u); split via product structure.
  obtain ⟨x, y, u⟩ := p
  rw [hκeq x y u]
  exact mul_nonneg (hκnn x u) (h_pmf_nn (x, y))

/-- **Total mass of a factorisable joint equals total mass of `P_XY`.** When
`P_XY` is a pmf (total mass `1`), the joint is also total-mass `1`. -/
lemma IsWynerZivFactorizable_sum
    (P_XY : α × β → ℝ) {q : α × β × U → ℝ}
    (hq : IsWynerZivFactorizable U P_XY q) :
    ∑ p, q p = ∑ p, P_XY p := by
  rcases hq with ⟨κ, _hκnn, hκsum, hκeq⟩
  -- Split the triple-product sum α × (β × U) via Fintype.sum_prod_type.
  rw [Fintype.sum_prod_type (f := q)]
  -- Goal: ∑ x, ∑ p : β × U, q (x, p) = ∑ p, P_XY p.
  -- Re-shape RHS via Fintype.sum_prod_type for P_XY.
  rw [show (∑ p, P_XY p) = ∑ x, ∑ y, P_XY (x, y) from
        Fintype.sum_prod_type (f := P_XY)]
  refine Finset.sum_congr rfl ?_
  intro x _
  -- ∑ p : β × U, q (x, p) = ∑ y, P_XY (x, y).
  rw [Fintype.sum_prod_type (f := fun p : β × U => q (x, p.1, p.2))]
  -- ∑ y, ∑ u, q (x, y, u) = ∑ y, P_XY (x, y).
  refine Finset.sum_congr rfl ?_
  intro y _
  -- ∑ u, q (x, y, u) = P_XY (x, y).
  have h_rewrite : ∀ u, q (x, y, u) = κ x u * P_XY (x, y) := fun u => hκeq x y u
  calc (∑ u, q (x, y, u))
      = ∑ u, κ x u * P_XY (x, y) := by
        refine Finset.sum_congr rfl ?_; intro u _; exact h_rewrite u
    _ = (∑ u, κ x u) * P_XY (x, y) := by rw [← Finset.sum_mul]
    _ = 1 * P_XY (x, y) := by rw [hκsum x]
    _ = P_XY (x, y) := by rw [one_mul]

/-- **`stdSimplex` membership for factorisable joints over a pmf source.**
If `P_XY ∈ stdSimplex` (a pmf), then every factorisable joint is also in
`stdSimplex ℝ (α × β × U)`. -/
lemma IsWynerZivFactorizable_mem_stdSimplex
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    {q : α × β × U → ℝ}
    (hq : IsWynerZivFactorizable U P_XY q) :
    q ∈ stdSimplex ℝ (α × β × U) := by
  refine ⟨?_, ?_⟩
  · exact IsWynerZivFactorizable_nonneg U P_XY h_pmf.1 hq
  · rw [IsWynerZivFactorizable_sum U P_XY hq]
    exact h_pmf.2

end FactorisableStructure

/-! ## §3 Convex combinations preserve factorisation -/

section FactorisableConvex

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Convex combinations of factorisable joints are factorisable.** This is
the key affine property that re-parameterisation buys us: although the
Markov cross-product constraint is non-affine on the *raw* joint pmf
coordinate, on the *factorised* manifold the predicate is affine in `κ`,
and the kernel-level convex combination

`κ := a • κ₁ + b • κ₂`

is again row-stochastic (non-negativity + row-sum `1`). The joint
combination then factors:

`a • q₁ + b • q₂ = (a • κ₁ + b • κ₂) ⊗ P_XY`. -/
lemma IsWynerZivFactorizable_convex_combination
    (P_XY : α × β → ℝ)
    {q₁ q₂ : α × β × U → ℝ}
    (h1 : IsWynerZivFactorizable U P_XY q₁)
    (h2 : IsWynerZivFactorizable U P_XY q₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsWynerZivFactorizable U P_XY (a • q₁ + b • q₂) := by
  rcases h1 with ⟨κ₁, hκ₁nn, hκ₁sum, hκ₁eq⟩
  rcases h2 with ⟨κ₂, hκ₂nn, hκ₂sum, hκ₂eq⟩
  refine ⟨fun x u => a * κ₁ x u + b * κ₂ x u, ?_, ?_, ?_⟩
  · intro x u
    exact add_nonneg (mul_nonneg ha (hκ₁nn x u)) (mul_nonneg hb (hκ₂nn x u))
  · intro x
    -- Σ_u (a • κ₁ x u + b • κ₂ x u) = a + b = 1.
    have h_split :
        (∑ u, (a * κ₁ x u + b * κ₂ x u))
          = a * (∑ u, κ₁ x u) + b * (∑ u, κ₂ x u) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h_split, hκ₁sum x, hκ₂sum x, mul_one, mul_one]; exact hab
  · intro x y u
    -- (a • q₁ + b • q₂)(x,y,u) = (a κ₁(x,u) + b κ₂(x,u)) · P_XY(x,y).
    show a * q₁ (x, y, u) + b * q₂ (x, y, u)
            = (a * κ₁ x u + b * κ₂ x u) * P_XY (x, y)
    rw [hκ₁eq x y u, hκ₂eq x y u]; ring

end FactorisableConvex

/-! ## §4 Factorisable constraint set -/

section FactorisableConstraintSet

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Factorisable Wyner–Ziv constraint set.** A `(q, f)` pair belongs iff:
1. `q` is `IsWynerZivFactorizable U P_XY` — factorises as `κ(u|x)·P_XY(x,y)`,
2. `wzExpectedDistortion d q f ≤ D` — distortion budget.

The simplex / marginal / Markov constraints (1-3 of `WynerZivConstraint`)
are *consequences* of the factorisation predicate when `P_XY` is itself a
pmf; we record this as the `factorisable_subset_constraint` lemma below. -/
def WynerZivFactorizableConstraint
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) :
    Set ((α × β × U → ℝ) × (U × β → γ)) :=
  {qf | IsWynerZivFactorizable U P_XY qf.1
        ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D}

/-- Membership unfold for `WynerZivFactorizableConstraint`. -/
lemma mem_WynerZivFactorizableConstraint_iff
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    {qf : (α × β × U → ℝ) × (U × β → γ)} :
    qf ∈ WynerZivFactorizableConstraint U P_XY d D ↔
      IsWynerZivFactorizable U P_XY qf.1
        ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D := Iff.rfl

/-- **Factorisable constraint ⊆ raw constraint.** Every factorisable
feasible point is also feasible in the original (un-re-parameterised)
constraint set, provided `P_XY` is itself a pmf in the simplex. -/
lemma factorisable_subset_constraint
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (D : ℝ) :
    WynerZivFactorizableConstraint U P_XY d D
      ⊆ WynerZivConstraint U P_XY d D := by
  rintro qf ⟨hqfact, hdist⟩
  refine ⟨?_, ?_, ?_, hdist⟩
  · exact IsWynerZivFactorizable_mem_stdSimplex U h_pmf hqfact
  · exact IsWynerZivFactorizable_marginalXY U P_XY hqfact
  · exact IsWynerZivFactorizable_markov U P_XY hqfact

end FactorisableConstraintSet

/-! ## §5 D-monotonicity of factorisable constraint -/

section FactorisableMonotone

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Factorisable constraint set is monotone in `D`.** Mirror of
`WynerZivConstraint_mono_in_D`. -/
@[entry_point]
theorem WynerZivFactorizableConstraint_mono_in_D
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D') :
    WynerZivFactorizableConstraint U P_XY d D
      ⊆ WynerZivFactorizableConstraint U P_XY d D' := by
  rintro qf ⟨h1, h2⟩
  exact ⟨h1, le_trans h2 hD⟩

end FactorisableMonotone

/-! ## §6 Convex combination preserves feasibility (D-mixed) -/

section FactorisableConvexCombination

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **The key lemma: a convex combination of two factorisable feasible
points at thresholds `D₁, D₂` is feasible at the mixed threshold
`a D₁ + b D₂`** (with shared decoder `f`).

This is the structural step that turns L-WZ3 convexity into a one-liner on
factorisable joints: feasibility *survives* convex combinations on the
factorised manifold (unlike the raw constraint set where the Markov
cross-product fails to be preserved). -/
@[entry_point]
theorem WynerZivFactorizableConstraint_convex_combination
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (f : U × β → γ) {D₁ D₂ : ℝ}
    {q₁ q₂ : α × β × U → ℝ}
    (h1 : (q₁, f) ∈ WynerZivFactorizableConstraint U P_XY d D₁)
    (h2 : (q₂, f) ∈ WynerZivFactorizableConstraint U P_XY d D₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • q₁ + b • q₂, f)
      ∈ WynerZivFactorizableConstraint U P_XY d (a * D₁ + b * D₂) := by
  rcases h1 with ⟨hq₁fact, hdist₁⟩
  rcases h2 with ⟨hq₂fact, hdist₂⟩
  refine ⟨?_, ?_⟩
  · exact IsWynerZivFactorizable_convex_combination U P_XY hq₁fact hq₂fact ha hb hab
  · -- distortion: a • q₁ + b • q₂ ⟶ a · dist(q₁) + b · dist(q₂) ≤ a·D₁ + b·D₂.
    rw [wzExpectedDistortion_convex_combination U d q₁ q₂ f]
    have h1' : a * wzExpectedDistortion U d q₁ f ≤ a * D₁ :=
      mul_le_mul_of_nonneg_left hdist₁ ha
    have h2' : b * wzExpectedDistortion U d q₂ f ≤ b * D₂ :=
      mul_le_mul_of_nonneg_left hdist₂ hb
    linarith

end FactorisableConvexCombination

/-! ## §7 Factorisable rate function and full L-WZ3 convexity -/

section FactorisableRate

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Wyner–Ziv rate function restricted to factorisable joints.**
`R_WZ_fact(D) := sInf { I(X;U) − I(Y;U) | (q, f) ∈ WynerZivFactorizableConstraint U P_XY d D }`.

This is the form Cover–Thomas §15.9 directly addresses: the minimisation
over auxiliary kernels `κ(u|x)` with side-information decoders `f(u,y)`. -/
noncomputable def wynerZivRateFactorizable
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ :=
  sInf ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d D)

/-- **Factorisable rate is antitone in `D`** (mirror of the raw
`wynerZivRatePmf_antitone`). -/
@[entry_point]
theorem wynerZivRateFactorizable_antitone
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D')
    (h_ne : ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
              '' WynerZivFactorizableConstraint U P_XY d D).Nonempty)
    (h_bdd : BddBelow
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d D')) :
    wynerZivRateFactorizable U P_XY d D' ≤ wynerZivRateFactorizable U P_XY d D := by
  unfold wynerZivRateFactorizable
  refine le_csInf h_ne ?_
  rintro v ⟨qf, hqf, rfl⟩
  refine csInf_le h_bdd ?_
  refine ⟨qf, ?_, rfl⟩
  exact WynerZivFactorizableConstraint_mono_in_D U P_XY d hD hqf

/-- **L-WZ3 full convexity, hypothesis-driven form (Cover–Thomas §15.9).**

Under the standing hypotheses:
* `h_obj_convex` — Cover–Thomas Lemma 15.9: the Wyner–Ziv objective
  `I(X;U) − I(Y;U)` is *convex* in the joint pmf `q` along convex
  combinations of factorisable joints. Discharged elsewhere
  (`wyner-ziv-objective-convexity-discharge-*`).
* `h_feasible₁, h_feasible₂` — feasibility witnesses at `D₁`, `D₂`.
* `h_bdd_mixed` — `BddBelow` of the factorisable image at the mixed
  threshold `a D₁ + b D₂` (always supplied by the simplex projection on
  the upstream raw image; carried as hypothesis here to keep this file
  self-contained — see the `_of_BddBelow_simplex` corollary).

then the rate function is convex in `D` along the factorisable manifold:
`R_WZ_fact(a D₁ + b D₂) ≤ a · R_WZ_fact(D₁) + b · R_WZ_fact(D₂)`.

The hypothesis `h_obj_convex` is the *minimal* Lemma-15.9-shaped piece
needed; the rest is the standard "feasibility ⇒ image-level inf bound"
machinery from `WynerZivDischarge.lean`.

`@audit:superseded-by(wynerZivRateFactorizable_convex_in_D_unconditional)` -/
theorem wynerZivRateFactorizable_convex
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (f : U × β → γ)
    {D₁ D₂ : ℝ}
    (h_obj_convex : ∀ q₁ q₂ : α × β × U → ℝ,
        IsWynerZivFactorizable U P_XY q₁ →
        IsWynerZivFactorizable U P_XY q₂ →
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
          wzMutualInfoXU U (a • q₁ + b • q₂)
              - wzMutualInfoYU U (a • q₁ + b • q₂)
            ≤ a * (wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
              + b * (wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂))
    {q₁ q₂ : α × β × U → ℝ}
    (h_feasible₁ : (q₁, f) ∈ WynerZivFactorizableConstraint U P_XY d D₁)
    (h_feasible₂ : (q₂, f) ∈ WynerZivFactorizableConstraint U P_XY d D₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h_bdd_mixed : BddBelow
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d (a * D₁ + b * D₂))) :
    wynerZivRateFactorizable U P_XY d (a * D₁ + b * D₂)
      ≤ a * (wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
        + b * (wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂) := by
  -- The mixed point (a • q₁ + b • q₂, f) is feasible at a·D₁ + b·D₂.
  have h_mixed_feasible :
      (a • q₁ + b • q₂, f)
        ∈ WynerZivFactorizableConstraint U P_XY d (a * D₁ + b * D₂) :=
    WynerZivFactorizableConstraint_convex_combination U P_XY d f
      h_feasible₁ h_feasible₂ ha hb hab
  -- The mixed objective is bounded above by the convex combination of objectives.
  have h_obj_bound :
      wzMutualInfoXU U (a • q₁ + b • q₂)
          - wzMutualInfoYU U (a • q₁ + b • q₂)
        ≤ a * (wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
          + b * (wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂) :=
    h_obj_convex q₁ q₂ h_feasible₁.1 h_feasible₂.1 a b ha hb hab
  -- sInf ≤ mixed objective value ≤ convex combination upper bound.
  have h_mixed_in_image :
      wzMutualInfoXU U (a • q₁ + b • q₂)
        - wzMutualInfoYU U (a • q₁ + b • q₂)
        ∈ ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                  wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
            '' WynerZivFactorizableConstraint U P_XY d (a * D₁ + b * D₂)) :=
    ⟨(a • q₁ + b • q₂, f), h_mixed_feasible, rfl⟩
  have h_sInf_le :
      wynerZivRateFactorizable U P_XY d (a * D₁ + b * D₂)
        ≤ wzMutualInfoXU U (a • q₁ + b • q₂)
          - wzMutualInfoYU U (a • q₁ + b • q₂) := by
    unfold wynerZivRateFactorizable
    exact csInf_le h_bdd_mixed h_mixed_in_image
  exact le_trans h_sInf_le h_obj_bound

end FactorisableRate

/-! ## §8 BddBelow on factorisable image (simplex projection route) -/

section FactorisableBddBelow

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **The factorisable image is `BddBelow`.** Same simplex-projection route
as in `WynerZivDischarge.lean`: the factorisable image is contained in the
raw image (modulo the side conditions in `factorisable_subset_constraint`),
which is contained in `objective '' stdSimplex`, which is compact and
hence bounded below. -/
lemma wynerZivFactorizableObjective_image_bddBelow
    [DecidableEq α] [DecidableEq β]
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (D : ℝ) :
    BddBelow
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d D) := by
  -- Image of factorisable constraint is contained in image of raw constraint.
  have h_subset :
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
          '' WynerZivFactorizableConstraint U P_XY d D)
        ⊆ ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
          '' WynerZivConstraint U P_XY d D) := by
    rintro v ⟨qf, hqf, rfl⟩
    refine ⟨qf, ?_, rfl⟩
    exact factorisable_subset_constraint U h_pmf d D hqf
  exact (wynerZivObjective_image_bddBelow U P_XY d D).mono h_subset

/-- **L-WZ3 full convexity, simplex-projection corollary.** A user-facing
form: when `P_XY ∈ stdSimplex` (genuinely a pmf), the `h_bdd_mixed` side
condition on `wynerZivRateFactorizable_convex` is discharged via
`wynerZivFactorizableObjective_image_bddBelow`. The remaining hypothesis is
the Cover–Thomas Lemma 15.9 convexity-of-objective, plus two feasibility
witnesses.

`@audit:superseded-by(wynerZivRateFactorizable_convex_in_D_unconditional)` -/
theorem wynerZivRateFactorizable_convex_of_pmf
    [DecidableEq α] [DecidableEq β]
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (f : U × β → γ)
    {D₁ D₂ : ℝ}
    (h_obj_convex : ∀ q₁ q₂ : α × β × U → ℝ,
        IsWynerZivFactorizable U P_XY q₁ →
        IsWynerZivFactorizable U P_XY q₂ →
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
          wzMutualInfoXU U (a • q₁ + b • q₂)
              - wzMutualInfoYU U (a • q₁ + b • q₂)
            ≤ a * (wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
              + b * (wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂))
    {q₁ q₂ : α × β × U → ℝ}
    (h_feasible₁ : (q₁, f) ∈ WynerZivFactorizableConstraint U P_XY d D₁)
    (h_feasible₂ : (q₂, f) ∈ WynerZivFactorizableConstraint U P_XY d D₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    wynerZivRateFactorizable U P_XY d (a * D₁ + b * D₂)
      ≤ a * (wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
        + b * (wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂) :=
  wynerZivRateFactorizable_convex U P_XY d f h_obj_convex
    h_feasible₁ h_feasible₂ ha hb hab
    (wynerZivFactorizableObjective_image_bddBelow U h_pmf d (a * D₁ + b * D₂))

end FactorisableBddBelow

/-! ## §9 Rate-level convex inequality (final wrapper) -/

section RateLevelConvexity

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **L-WZ3 full convexity in the standard rate-level form.**

`R_WZ_fact(a D₁ + b D₂) ≤ a · R_WZ_fact(D₁) + b · R_WZ_fact(D₂)`.

Hypotheses:
* `h_pmf` — `P_XY` is a pmf (discharges `BddBelow`).
* `h_obj_convex` — Cover–Thomas Lemma 15.9 (convexity of `I(X;U) − I(Y;U)`
  in `q` on factorisable joints).
* `h_ne_mixed` — image at the mixed threshold is non-empty (any feasibility
  witness at *either* `D₁` or `D₂` discharges this via the convex-combination
  lemma; we carry the side condition to keep the wrapper minimal).
* `h_inf_attained₁, h_inf_attained₂` — witnesses that `R_WZ_fact(Dᵢ)` is
  attained (or approached) by some feasible `(qᵢ, f)`. This is the standard
  "if `sInf` is bounded below + non-empty, every value `≥ sInf − ε`" route.

This wrapper is hypothesis-driven by design; the inner-loop attainment
witnesses are supplied by callers (downstream `WynerZivAchievability.lean`
already publishes the slice-form attainment lemma; the joint-form attainment
is deferred to a separate plan).

`@audit:superseded-by(wynerZivRateFactorizable_convex_in_D_unconditional)` -/
theorem wynerZivRateFactorizable_convex_in_D
    [DecidableEq α] [DecidableEq β]
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (f : U × β → γ)
    {D₁ D₂ : ℝ}
    (h_obj_convex : ∀ q₁ q₂ : α × β × U → ℝ,
        IsWynerZivFactorizable U P_XY q₁ →
        IsWynerZivFactorizable U P_XY q₂ →
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
          wzMutualInfoXU U (a • q₁ + b • q₂)
              - wzMutualInfoYU U (a • q₁ + b • q₂)
            ≤ a * (wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
              + b * (wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂))
    {q₁ q₂ : α × β × U → ℝ}
    (h_feasible₁ : (q₁, f) ∈ WynerZivFactorizableConstraint U P_XY d D₁)
    (h_feasible₂ : (q₂, f) ∈ WynerZivFactorizableConstraint U P_XY d D₂)
    (h_attain₁ : wynerZivRateFactorizable U P_XY d D₁
                  = wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
    (h_attain₂ : wynerZivRateFactorizable U P_XY d D₂
                  = wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    wynerZivRateFactorizable U P_XY d (a * D₁ + b * D₂)
      ≤ a * wynerZivRateFactorizable U P_XY d D₁
        + b * wynerZivRateFactorizable U P_XY d D₂ := by
  rw [h_attain₁, h_attain₂]
  exact wynerZivRateFactorizable_convex_of_pmf U h_pmf d f h_obj_convex
    h_feasible₁ h_feasible₂ ha hb hab

end RateLevelConvexity

end InformationTheory.Shannon
