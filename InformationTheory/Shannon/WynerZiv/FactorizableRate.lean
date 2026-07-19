import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.WynerZiv.RateMonotonicity

/-!
# Wyner–Ziv convexity under the factorization predicate

Convexity of the Wyner–Ziv rate function (Cover–Thomas, §15.9). The Markov
cross-product constraint `q(x,y,u) · Σ q(x,y',u') = q(x,y,u') · Σ q(x,y',u)` is
quadratic, so the "convex hull of two feasible points is feasible" argument fails
on the raw joint pmf. The standard route re-parameterizes the constraint by an
affine factorization predicate

```
q(x, y, u) = κ(u | x) · P_XY(x, y)
```

where `κ : α → U → ℝ` is a transition kernel (per-row non-negative, per-row sum
`1`). On the factorized manifold the Markov chain `U − X − Y` holds
automatically, the `(X,Y)`-marginal recovers `P_XY`, `stdSimplex` membership
reduces to row-stochasticity, and the joint is affine in `κ`, so convex
combinations of feasible points stay feasible.

## Main definitions

* `IsWynerZivFactorizable U P_XY q` — the factorization predicate.
* `WynerZivFactorizableConstraint` — the factorizable refinement of
  `WynerZivConstraint`.
* `wynerZivRateFactorizable` — the rate function restricted to factorizable
  joints.

## Main statements

* `IsWynerZivFactorizable_convex_combination` — convex combinations preserve the
  predicate.
* `WynerZivFactorizableConstraint_convex_combination` — feasibility survives
  convex combinations at the mixed distortion budget.
* `wynerZivRateFactorizable_convex_in_D` — under convexity of the objective on
  factorizable joints, the rate function is convex in `D`.

## Implementation notes

The convexity of the objective `I(X;U) − I(Y;U)` in the kernel `κ` (Cover–Thomas
Lemma 15.9) is carried as a hypothesis `h_obj_convex` on the convexity theorems
rather than proved here.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## §1 Factorization predicate -/

section FactorisationPredicate

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Affine factorization predicate. The joint pmf `q : α × β × U → ℝ` is
*Wyner–Ziv factorizable* over the source `P_XY : α × β → ℝ` if there exists
a transition kernel `κ : α → U → ℝ` (per-row non-negative and per-row sum
`1`) such that

```
q(x, y, u) = κ(u | x) · P_XY(x, y).
```

This is the *affine* re-parameterization underlying Cover–Thomas §15.9; the
quadratic Markov cross-product constraint is automatically satisfied (see
`IsWynerZivFactorizable_markov` below). -/
def IsWynerZivFactorizable
    (P_XY : α × β → ℝ) (q : α × β × U → ℝ) : Prop :=
  ∃ κ : α → U → ℝ,
    (∀ x u, 0 ≤ κ x u)
    ∧ (∀ x, ∑ u, κ x u = 1)
    ∧ (∀ x y u, q (x, y, u) = κ x u * P_XY (x, y))

/-- Membership unfold for `IsWynerZivFactorizable`. -/
@[entry_point]
lemma IsWynerZivFactorizable_iff
    (P_XY : α × β → ℝ) (q : α × β × U → ℝ) :
    IsWynerZivFactorizable U P_XY q ↔
      ∃ κ : α → U → ℝ,
        (∀ x u, 0 ≤ κ x u)
        ∧ (∀ x, ∑ u, κ x u = 1)
        ∧ (∀ x y u, q (x, y, u) = κ x u * P_XY (x, y)) := Iff.rfl

end FactorisationPredicate

/-! ## §2 Structural consequences on factorizable joints -/

section FactorisableStructure

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Markov chain holds automatically on factorizable joints. The
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

/-- `(X, Y)`-marginal of a factorizable joint recovers `P_XY` (when the
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

/-- Factorizable joints are non-negative pointwise (when `P_XY` is). -/
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

/-- Total mass of a factorizable joint equals total mass of `P_XY`. When
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
  rw [Fintype.sum_prod_type (f := fun p : β × U ↦ q (x, p.1, p.2))]
  -- ∑ y, ∑ u, q (x, y, u) = ∑ y, P_XY (x, y).
  refine Finset.sum_congr rfl ?_
  intro y _
  -- ∑ u, q (x, y, u) = P_XY (x, y).
  have h_rewrite : ∀ u, q (x, y, u) = κ x u * P_XY (x, y) := fun u ↦ hκeq x y u
  calc (∑ u, q (x, y, u))
      = ∑ u, κ x u * P_XY (x, y) := by
        refine Finset.sum_congr rfl ?_; intro u _; exact h_rewrite u
    _ = (∑ u, κ x u) * P_XY (x, y) := by rw [← Finset.sum_mul]
    _ = 1 * P_XY (x, y) := by rw [hκsum x]
    _ = P_XY (x, y) := by rw [one_mul]

/-- `stdSimplex` membership for factorizable joints over a pmf source.
If `P_XY ∈ stdSimplex` (a pmf), then every factorizable joint is also in
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

/-! ## §3 Convex combinations preserve factorization -/

section FactorisableConvex

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Convex combinations of factorizable joints are factorizable. This is
the key affine property that re-parameterization buys us: although the
Markov cross-product constraint is non-affine on the *raw* joint pmf
coordinate, on the *factorized* manifold the predicate is affine in `κ`,
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
  refine ⟨fun x u ↦ a * κ₁ x u + b * κ₂ x u, ?_, ?_, ?_⟩
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

/-! ## §4 Factorizable constraint set -/

section FactorisableConstraintSet

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Factorizable Wyner–Ziv constraint set. A `(q, f)` pair belongs iff:
1. `q` is `IsWynerZivFactorizable U P_XY` — factorizes as `κ(u|x)·P_XY(x,y)`,
2. `wzExpectedDistortion d q f ≤ D` — distortion budget.

The simplex / marginal / Markov constraints (1-3 of `WynerZivConstraint`)
are *consequences* of the factorization predicate when `P_XY` is itself a
pmf; we record this as the `factorisable_subset_constraint` lemma below. -/
def WynerZivFactorizableConstraint
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) :
    Set ((α × β × U → ℝ) × (U × β → γ)) :=
  {qf | IsWynerZivFactorizable U P_XY qf.1
        ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D}

/-- Membership unfold for `WynerZivFactorizableConstraint`. -/
@[entry_point]
lemma mem_WynerZivFactorizableConstraint_iff
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    {qf : (α × β × U → ℝ) × (U × β → γ)} :
    qf ∈ WynerZivFactorizableConstraint U P_XY d D ↔
      IsWynerZivFactorizable U P_XY qf.1
        ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D := Iff.rfl

/-- Factorizable constraint ⊆ raw constraint. Every factorizable
feasible point is also feasible in the original (un-re-parameterized)
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

/-! ## §5 D-monotonicity of factorizable constraint -/

section FactorisableMonotone

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Factorizable constraint set is monotone in `D`. Mirror of
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

/-- **The key lemma: a convex combination of two factorizable feasible
points at thresholds `D₁, D₂` is feasible at the mixed threshold
`a D₁ + b D₂`** (with shared decoder `f`).

This is the structural step that turns convexity into a one-liner on
factorizable joints: feasibility survives convex combinations on the
factorized manifold (unlike the raw constraint set where the Markov
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

/-! ## §7 Factorizable rate function and its convexity -/

section FactorisableRate

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Wyner–Ziv rate function restricted to factorizable joints.
`R_WZ_fact(D) := sInf { I(X;U) − I(Y;U) | (q, f) ∈ WynerZivFactorizableConstraint U P_XY d D }`.

This is the form Cover–Thomas §15.9 directly addresses: the minimization
over auxiliary kernels `κ(u|x)` with side-information decoders `f(u,y)`. -/
noncomputable def wynerZivRateFactorizable
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ :=
  sInf ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d D)

/-- Factorizable rate is antitone in `D` (mirror of the raw
`wynerZivRatePmf_antitone`). -/
@[entry_point]
theorem wynerZivRateFactorizable_antitone
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D')
    (h_ne : ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
              '' WynerZivFactorizableConstraint U P_XY d D).Nonempty)
    (h_bdd : BddBelow
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d D')) :
    wynerZivRateFactorizable U P_XY d D' ≤ wynerZivRateFactorizable U P_XY d D := by
  unfold wynerZivRateFactorizable
  refine le_csInf h_ne ?_
  rintro v ⟨qf, hqf, rfl⟩
  refine csInf_le h_bdd ?_
  refine ⟨qf, ?_, rfl⟩
  exact WynerZivFactorizableConstraint_mono_in_D U P_XY d hD hqf

/-- Convexity of the factorizable rate function along a fixed decoder `f`: under
convexity of the objective on factorizable joints (`h_obj_convex`), feasibility
witnesses at `D₁, D₂`, and `BddBelow` of the factorizable image at the mixed
threshold, the inf over the mixed budget is bounded by the convex combination of
objective values.

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
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
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
        ∈ ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
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

/-! ## §8 BddBelow on factorizable image (simplex projection route) -/

section FactorisableBddBelow

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- The factorizable image is `BddBelow`. Same simplex-projection route
as in `WynerZiv/RateMonotonicity.lean`: the factorizable image is contained in the
raw image (modulo the side conditions in `factorisable_subset_constraint`),
which is contained in `objective '' stdSimplex`, which is compact and
hence bounded below. -/
lemma wynerZivFactorizableObjective_image_bddBelow
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (D : ℝ) :
    BddBelow
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d D) := by
  -- Image of factorizable constraint is contained in image of raw constraint.
  have h_subset :
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
          '' WynerZivFactorizableConstraint U P_XY d D)
        ⊆ ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
          '' WynerZivConstraint U P_XY d D) := by
    rintro v ⟨qf, hqf, rfl⟩
    refine ⟨qf, ?_, rfl⟩
    exact factorisable_subset_constraint U h_pmf d D hqf
  exact (wynerZivObjective_image_bddBelow U P_XY d D).mono h_subset

/-- The simplex-projection corollary of `wynerZivRateFactorizable_convex`: when
`P_XY ∈ stdSimplex`, the `BddBelow` side condition is discharged via
`wynerZivFactorizableObjective_image_bddBelow`, leaving the objective-convexity
hypothesis and two feasibility witnesses.

`@audit:superseded-by(wynerZivRateFactorizable_convex_in_D_unconditional)` -/
theorem wynerZivRateFactorizable_convex_of_pmf
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

/-- Convexity of the factorizable rate function in `D`, rate-level form:
`R_WZ_fact(a D₁ + b D₂) ≤ a · R_WZ_fact(D₁) + b · R_WZ_fact(D₂)`. Takes `P_XY` a
pmf, objective convexity on factorizable joints, feasibility witnesses, and
attainment of `R_WZ_fact(Dᵢ)` at those witnesses.

`@audit:superseded-by(wynerZivRateFactorizable_convex_in_D_unconditional)` -/
theorem wynerZivRateFactorizable_convex_in_D
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

/-! ## §10 Auxiliary-alphabet infimum rate (reshape: inf over all finite `Fin k`)

The headline operational rate `wynerZivRateFactorizable U` fixes the auxiliary
alphabet type `U` up front. For the *operational converse* this forces a
Carathéodory support argument (the single-letterization auxiliary
`Uᵢ := (J, Y^{i-1})` has a cardinality that grows with the block length, so it
does not embed into a fixed `U` without the `|U| ≤ |α| + 1` reduction).

This section adds the reshaped rate `wynerZivRate` — the infimum of the
objective over feasible factorizable points at *every* finite auxiliary
alphabet `Fin k` simultaneously. A large single-letterization auxiliary then
lands directly as a feasible point of the reshaped infimum, with no cardinality
bound.

### Non-degeneracy (junk-`sInf` guard)

`wynerZivRateFactorizable U = sInf (image)` and, in `ℝ`, `sInf ∅ = 0`. A naive
`⨅ k, wynerZivRateFactorizable (Fin k) D` would inject a junk `0` at every index
`k` whose factorizable constraint is empty (e.g. `k = 0`: `Fin 0` is empty, so
no row-stochastic kernel exists), collapsing the infimum to `≤ 0`. That would
make the converse `wynerZivRate ≤ R` vacuously true — a degenerate-definition
defect.

The `⋃`-then-`sInf` form (`wzRateValueSet`) avoids this: empty-constraint
indices contribute the *empty* image, so they inject no value. The remaining
lower bound comes from the objective's non-negativity on the factorizable
manifold (data-processing inequality `I(X;U) − I(Y;U) ≥ 0` for the Markov chain
`U − X − Y`), established in `Converse.lean` and used to discharge `BddBelow`. -/

section AllAuxRate

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]

/-- The set of Wyner–Ziv objective values `I(X;U) − I(Y;U)` attainable by a
factorizable feasible point at *some* finite auxiliary alphabet `Fin k`, with
`k` ranging over all of `ℕ`. Feasibility-empty indices contribute the empty
image (no value), so this set carries no junk `sInf ∅ = 0` term. -/
def wzRateValueSet
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : Set ℝ :=
  ⋃ k : ℕ,
    (fun qf : (α × β × Fin k → ℝ) × (Fin k × β → γ) ↦
        wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1)
      '' WynerZivFactorizableConstraint (Fin k) P_XY d D

/-- Reshaped Wyner–Ziv operational rate: the infimum of the objective
`I(X;U) − I(Y;U)` over feasible factorizable points at *every* finite auxiliary
alphabet `Fin k` at once, rather than a single caller-fixed `U`.

This is the `∀`-clean form needed by the operational converse: the
single-letterization auxiliary lands directly as a feasible point (see
`wynerZivRate_le_of_feasible`), with no Carathéodory cardinality reduction.

@audit:ok (independent honesty audit 2026-07-05, non-degeneracy check PASS): the
union-of-images form `wzRateValueSet` genuinely avoids the junk `sInf ∅ = 0`
collapse — an empty-constraint index `k` (e.g. `Fin 0`) contributes the *empty*
image to the `⋃`, injecting no `0`, so `wynerZivRate ≤ R` is a substantive claim
(NOT the degenerate `⨅ k, sInf(image_k)` form that would inject `0`s). -/
noncomputable def wynerZivRate
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ :=
  sInf (wzRateValueSet P_XY d D)

/-- Membership in `wzRateValueSet`: a real `v` is a value iff it is the objective
of a feasible factorizable point at some finite auxiliary alphabet `Fin k`. -/
lemma mem_wzRateValueSet_iff
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ} {v : ℝ} :
    v ∈ wzRateValueSet P_XY d D ↔
      ∃ (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ)),
        qf ∈ WynerZivFactorizableConstraint (Fin k) P_XY d D
          ∧ wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 = v := by
  unfold wzRateValueSet
  constructor
  · intro hv
    rw [Set.mem_iUnion] at hv
    obtain ⟨k, qf, hqf, rfl⟩ := hv
    exact ⟨k, qf, hqf, rfl⟩
  · rintro ⟨k, qf, hqf, rfl⟩
    exact Set.mem_iUnion.mpr ⟨k, qf, hqf, rfl⟩

/-- A feasible factorizable point at auxiliary alphabet `Fin k` produces a value
in `wzRateValueSet` (witness for non-emptiness). -/
lemma objective_mem_wzRateValueSet
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    {k : ℕ} {qf : (α × β × Fin k → ℝ) × (Fin k × β → γ)}
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k) P_XY d D) :
    wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1
      ∈ wzRateValueSet P_XY d D :=
  mem_wzRateValueSet_iff.mpr ⟨k, qf, hqf, rfl⟩

/-- **Landing lemma (direct, `Fin k` form).** Any feasible factorizable point at
auxiliary alphabet `Fin k` bounds the reshaped rate from above. This is what
lets the single-letterization auxiliary land *directly*, with no cardinality
reduction. The `BddBelow` side condition is discharged (via the objective's
data-processing non-negativity) in `Converse.lean` by
`wzRateValueSet_bddBelow_of_pmf`.

@audit:ok (independent honesty audit 2026-07-05: sorryAx-free, verified by
`#print axioms`). `hbdd : BddBelow …` is a genuine regularity precondition (the
exact hypothesis of `csInf_le`), mirroring `wynerZivRatePmf_le_of_feasible`; it
does NOT smuggle the proof core — the body is the standard `csInf_le` shape. -/
theorem wynerZivRate_le_of_feasible
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    (hbdd : BddBelow (wzRateValueSet P_XY d D))
    {k : ℕ} {qf : (α × β × Fin k → ℝ) × (Fin k × β → γ)}
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k) P_XY d D) :
    wynerZivRate P_XY d D
      ≤ wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 := by
  unfold wynerZivRate
  exact csInf_le hbdd (objective_mem_wzRateValueSet hqf)

/-- The reshaped value set is monotone in `D`: enlarging the distortion budget
enlarges the set of attainable objective values, since every feasible
factorizable point at budget `D` remains feasible at `D' ≥ D`
(`WynerZivFactorizableConstraint_mono_in_D`, applied at each auxiliary alphabet
`Fin k`).

@audit:ok (independent honesty audit 2026-07-05: sorryAx-free, `#print axioms` =
[propext, Classical.choice, Quot.sound]; genuine subset body via
`WynerZivFactorizableConstraint_mono_in_D`, no load-bearing hyp / vacuity). -/
lemma wzRateValueSet_mono_in_D
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D D' : ℝ} (hD : D ≤ D') :
    wzRateValueSet P_XY d D ⊆ wzRateValueSet P_XY d D' := by
  intro v hv
  rw [mem_wzRateValueSet_iff] at hv ⊢
  obtain ⟨k, qf, hqf, rfl⟩ := hv
  exact ⟨k, qf, WynerZivFactorizableConstraint_mono_in_D (Fin k) P_XY d hD hqf, rfl⟩

/-- **The reshaped Wyner–Ziv rate is antitone in `D`.** A larger distortion budget
enlarges the value set (`wzRateValueSet_mono_in_D`), so its infimum is smaller.
The `BddBelow` at `D'` and non-emptiness at `D` are the standard `csInf_le_csInf`
side conditions — both discharged in `Converse.lean` (via
`wzRateValueSet_bddBelow_of_pmf` and a feasible witness).

@audit:ok (independent honesty audit 2026-07-05: sorryAx-free, `#print axioms` =
[propext, Classical.choice, Quot.sound]; genuine `csInf_le_csInf` body. `h_bdd` /
`h_ne` are its standard regularity side conditions, not load-bearing core, and the
antitone direction `D ≤ D' ⟹ rate(D') ≤ rate(D)` is the correct one). -/
theorem wynerZivRate_antitone
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D D' : ℝ} (hD : D ≤ D')
    (h_bdd : BddBelow (wzRateValueSet P_XY d D'))
    (h_ne : (wzRateValueSet P_XY d D).Nonempty) :
    wynerZivRate P_XY d D' ≤ wynerZivRate P_XY d D := by
  unfold wynerZivRate
  exact csInf_le_csInf h_bdd h_ne (wzRateValueSet_mono_in_D hD)

/-! ### §10.1 Time-sharing infrastructure -/

/-- Time-sharing helper. From `X ≤ c · s` for every `s` in a nonempty set `S`
together with `0 ≤ c`, conclude `X ≤ c · sInf S`. Isolates the `c = 0` boundary
from the `c > 0` division step. -/
lemma le_mul_csInf {S : Set ℝ} (hne : S.Nonempty)
    {c X : ℝ} (hc : 0 ≤ c) (h : ∀ s ∈ S, X ≤ c * s) :
    X ≤ c * sInf S := by
  rcases hc.eq_or_lt with hc0 | hc0
  · obtain ⟨s, hs⟩ := hne
    have hXs := h s hs
    rw [← hc0] at hXs ⊢
    simpa using hXs
  · have hle : X / c ≤ sInf S := by
      refine le_csInf hne ?_
      intro s hs
      rw [div_le_iff₀ hc0, mul_comm]
      exact h s hs
    calc X = c * (X / c) := by rw [mul_div_cancel₀ X hc0.ne']
      _ ≤ c * sInf S := mul_le_mul_of_nonneg_left hle hc

/-- Total mass of the second marginal equals the total mass of the joint. -/
lemma sum_marginalSnd {A B : Type*} [Fintype A] [Fintype B] (p : A × B → ℝ) :
    ∑ b, marginalSnd p b = ∑ z, p z := by
  unfold marginalSnd
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type p).symm

/-- **Mixture-affinity of pmf mutual information.** For two joint pmfs
`p₁ : A × B₁ → ℝ` and `p₂ : A × B₂ → ℝ`, each of total mass `1` and sharing the
*same* first marginal (`marginalFst p₁ = marginalFst p₂`, i.e. `I(X ; branch) = 0`),
form the disjoint-union mixture `mix : A × (B₁ ⊕ B₂) → ℝ` with

```
mix (x, inl b₁) = a · p₁ (x, b₁),   mix (x, inr b₂) = b · p₂ (x, b₂)
```

for weights `a + b = 1`. Then the pmf mutual information is affine:

```
mutualInfoPmf mix = a · mutualInfoPmf p₁ + b · mutualInfoPmf p₂.
```

The branch entropy `H(a, b)` cancels between the `H(U)` term and the `H(X, U)`
term; the shared-first-marginal hypothesis is what kills the `H(X)`-side
contribution. This is the reusable engine for Wyner–Ziv time-sharing (both the
value-set closure and the operational converse feasible-point step).

@audit:ok (independent honesty audit 2026-07-05, auditor-verified not self-reported:
sorryAx-free, `#print axioms` = [propext, Classical.choice, Quot.sound]). Signature
honest: `h₁sum`/`h₂sum` are pmf total-mass-1 regularity, `hmix₁`/`hmix₂` merely
*define* the disjoint-union mixture (not the conclusion), `hab` is the weight
normalization. `h_marg` (shared first marginal) is a genuine precondition ON THE
INPUTS — verified load-bearing for TRUTH (dropping it makes the identity false,
since `H(X)` is concave not affine) yet NOT bundling the conclusion (the affine
identity is a claim about the mixture's `mutualInfoPmf`, proven in-body via the
`H(a,b)` branch-entropy cancellation). Coefficients `a`,`b` verified correct
(right, not swapped); `a=0`/`a=1` degenerate boundaries stay alive and true. -/
lemma mutualInfoPmf_mixture_affine
    {A B₁ B₂ : Type*} [Fintype A] [Fintype B₁] [Fintype B₂]
    {p₁ : A × B₁ → ℝ} {p₂ : A × B₂ → ℝ}
    (h₁sum : ∑ z, p₁ z = 1) (h₂sum : ∑ z, p₂ z = 1)
    (h_marg : marginalFst p₁ = marginalFst p₂)
    {a b : ℝ} (hab : a + b = 1)
    {mix : A × (B₁ ⊕ B₂) → ℝ}
    (hmix₁ : ∀ x b₁, mix (x, Sum.inl b₁) = a * p₁ (x, b₁))
    (hmix₂ : ∀ x b₂, mix (x, Sum.inr b₂) = b * p₂ (x, b₂)) :
    mutualInfoPmf mix = a * mutualInfoPmf p₁ + b * mutualInfoPmf p₂ := by
  have hmass1 : ∑ b, marginalSnd p₁ b = 1 := by rw [sum_marginalSnd]; exact h₁sum
  have hmass2 : ∑ b, marginalSnd p₂ b = 1 := by rw [sum_marginalSnd]; exact h₂sum
  -- first marginal of the mixture equals the common first marginal
  have hmFst : marginalFst mix = marginalFst p₁ := by
    funext x
    have hx : marginalFst mix x = a * marginalFst p₁ x + b * marginalFst p₂ x := by
      show (∑ c, mix (x, c)) = a * (∑ b₁, p₁ (x, b₁)) + b * (∑ b₂, p₂ (x, b₂))
      rw [Fintype.sum_sum_type]
      simp_rw [hmix₁, hmix₂, ← Finset.mul_sum]
    have hp : marginalFst p₂ x = marginalFst p₁ x := congrFun h_marg.symm x
    rw [hx, hp, ← add_mul, hab, one_mul]
  -- first-marginal term of the mixture, re-expressed as an affine combination
  have hT1 : (∑ a', Real.negMulLog (marginalFst mix a'))
      = a * (∑ a', Real.negMulLog (marginalFst p₁ a'))
        + b * (∑ a', Real.negMulLog (marginalFst p₂ a')) := by
    rw [hmFst, ← h_marg, ← add_mul, hab, one_mul]
  -- second-marginal term splits into the two branch blocks
  have hT2 : (∑ c, Real.negMulLog (marginalSnd mix c))
      = (Real.negMulLog a + a * (∑ b₁, Real.negMulLog (marginalSnd p₁ b₁)))
        + (Real.negMulLog b + b * (∑ b₂, Real.negMulLog (marginalSnd p₂ b₂))) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · have hb1 : ∀ b₁, marginalSnd mix (Sum.inl b₁) = a * marginalSnd p₁ b₁ := by
        intro b₁
        show (∑ x, mix (x, Sum.inl b₁)) = a * (∑ x, p₁ (x, b₁))
        simp_rw [hmix₁, ← Finset.mul_sum]
      simp_rw [hb1, Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hmass1, one_mul]
    · have hb2 : ∀ b₂, marginalSnd mix (Sum.inr b₂) = b * marginalSnd p₂ b₂ := by
        intro b₂
        show (∑ x, mix (x, Sum.inr b₂)) = b * (∑ x, p₂ (x, b₂))
        simp_rw [hmix₂, ← Finset.mul_sum]
      simp_rw [hb2, Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hmass2, one_mul]
  -- joint term splits into the two branch blocks
  have hT3split : (∑ w : A × (B₁ ⊕ B₂), Real.negMulLog (mix w))
      = (∑ z : A × B₁, Real.negMulLog (mix (z.1, Sum.inl z.2)))
        + (∑ z : A × B₂, Real.negMulLog (mix (z.1, Sum.inr z.2))) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_sum_type]
    rw [Finset.sum_add_distrib,
      ← Fintype.sum_prod_type (f := fun z : A × B₁ ↦ Real.negMulLog (mix (z.1, Sum.inl z.2))),
      ← Fintype.sum_prod_type (f := fun z : A × B₂ ↦ Real.negMulLog (mix (z.1, Sum.inr z.2)))]
  have hT3 : (∑ w : A × (B₁ ⊕ B₂), Real.negMulLog (mix w))
      = (Real.negMulLog a + a * (∑ z : A × B₁, Real.negMulLog (p₁ z)))
        + (Real.negMulLog b + b * (∑ z : A × B₂, Real.negMulLog (p₂ z))) := by
    rw [hT3split]
    congr 1
    · have h1 : ∀ z : A × B₁, mix (z.1, Sum.inl z.2) = a * p₁ z := fun z ↦ hmix₁ z.1 z.2
      simp_rw [h1, Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, h₁sum, one_mul]
    · have h2 : ∀ z : A × B₂, mix (z.1, Sum.inr z.2) = b * p₂ z := fun z ↦ hmix₂ z.1 z.2
      simp_rw [h2, Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, h₂sum, one_mul]
  unfold mutualInfoPmf
  rw [hT1, hT2, hT3]
  ring

/-- `mutualInfoPmf` is invariant under reindexing the second coordinate by an
equivalence. -/
lemma mutualInfoPmf_reindex_right
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (σ : C ≃ B) (p : A × B → ℝ) :
    mutualInfoPmf (fun z : A × C ↦ p (z.1, σ z.2)) = mutualInfoPmf p := by
  have hFst : marginalFst (fun z : A × C ↦ p (z.1, σ z.2)) = marginalFst p := by
    funext a
    exact Equiv.sum_comp σ (fun b ↦ p (a, b))
  have hSnd : (∑ c, Real.negMulLog (marginalSnd (fun z : A × C ↦ p (z.1, σ z.2)) c))
      = ∑ b, Real.negMulLog (marginalSnd p b) := by
    rw [← Equiv.sum_comp σ (fun b ↦ Real.negMulLog (marginalSnd p b))]
    rfl
  have hJoint : (∑ z : A × C, Real.negMulLog (p (z.1, σ z.2)))
      = ∑ w : A × B, Real.negMulLog (p w) :=
    Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl A) σ) _ _ (fun z ↦ rfl)
  unfold mutualInfoPmf
  simp only []
  rw [hFst, hSnd, hJoint]

/-- The objective value of a feasible factorizable point at *any* finite
auxiliary alphabet `U` lands in `wzRateValueSet` — reindex `U` to
`Fin (Fintype.card U)`, under which factorizability, distortion, and the
objective are all preserved. -/
lemma wzRateValueSet_reindex_mem
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    {U : Type*} [Fintype U] [MeasurableSpace U]
    {q : α × β × U → ℝ} {f : U × β → γ}
    (hqf : (q, f) ∈ WynerZivFactorizableConstraint U P_XY d D) :
    wzMutualInfoXU U q - wzMutualInfoYU U q ∈ wzRateValueSet P_XY d D := by
  classical
  set e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U with he
  set k := Fintype.card U with hk
  set q' : α × β × Fin k → ℝ := fun p ↦ q (p.1, p.2.1, e.symm p.2.2) with hq'
  set f' : Fin k × β → γ := fun p ↦ f (e.symm p.1, p.2) with hf'
  set E : α × β × U ≃ α × β × Fin k :=
    Equiv.prodCongr (Equiv.refl α) (Equiv.prodCongr (Equiv.refl β) e) with hE
  rw [mem_wzRateValueSet_iff]
  refine ⟨k, (q', f'), ⟨?_, ?_⟩, ?_⟩
  · -- factorizability transports
    obtain ⟨κ, hκnn, hκsum, hκeq⟩ := hqf.1
    refine ⟨fun x i ↦ κ x (e.symm i), ?_, ?_, ?_⟩
    · intro x i; exact hκnn x (e.symm i)
    · intro x
      rw [Equiv.sum_comp e.symm (κ x)]
      exact hκsum x
    · intro x y i
      show q (x, y, e.symm i) = κ x (e.symm i) * P_XY (x, y)
      exact hκeq x y (e.symm i)
  · -- distortion transports (reindex the auxiliary coordinate)
    have hdisteq : wzExpectedDistortion (Fin k) d q' f'
        = wzExpectedDistortion U d q f := by
      unfold wzExpectedDistortion
      symm
      refine Fintype.sum_equiv E _ _ (fun w ↦ ?_)
      obtain ⟨x, y, u⟩ := w
      simp only [hE, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
        hq', hf', Equiv.symm_apply_apply]
    rw [hdisteq]; exact hqf.2
  · -- objective transports via reindexing invariance of `mutualInfoPmf`
    have hXeq : wzMutualInfoXU (Fin k) q' = wzMutualInfoXU U q := by
      unfold wzMutualInfoXU
      have hmarg : wzMarginalXU (Fin k) q'
          = fun z : α × Fin k ↦ wzMarginalXU U q (z.1, e.symm z.2) := by
        funext z; rfl
      rw [hmarg, mutualInfoPmf_reindex_right e.symm (wzMarginalXU U q)]
    have hYeq : wzMutualInfoYU (Fin k) q' = wzMutualInfoYU U q := by
      unfold wzMutualInfoYU
      have hmarg : wzMarginalYU (Fin k) q'
          = fun z : β × Fin k ↦ wzMarginalYU U q (z.1, e.symm z.2) := by
        funext z; rfl
      rw [hmarg, mutualInfoPmf_reindex_right e.symm (wzMarginalYU U q)]
    rw [hXeq, hYeq]

/-! ### §10.2 Time-sharing of the reshaped value set and rate -/

/-- **Time-sharing closure of the reshaped value set.** The set of attainable
Wyner–Ziv objective values is closed under convex combination across distortion
budgets: if `v₁` is attainable at budget `D₁` and `v₂` at budget `D₂`, then the
mixture `a·v₁ + b·v₂` is attainable at the mixed budget `a·D₁ + b·D₂`.

The witness is the disjoint-union auxiliary kernel `κ(x, inl u) = a·κ₁(x, u)`,
`κ(x, inr u) = b·κ₂(x, u)` at auxiliary alphabet `Fin k₁ ⊕ Fin k₂`: it is
row-stochastic, its distortion splits as `a·dist₁ + b·dist₂`, and its objective
is affine by `mutualInfoPmf_mixture_affine`.

@audit:ok (independent honesty audit 2026-07-05, auditor-verified not self-reported:
sorryAx-free, `#print axioms` = [propext, Classical.choice, Quot.sound]). All
hypotheses are genuine convex-combination preconditions: `h_pmf` (P_XY a pmf,
supplies total-mass-1 for the affine engine), `hv₁`/`hv₂` (the input value-set
memberships of a closure statement), `ha`/`hb` (weight non-negativity, feeds
kernel non-negativity + distortion bound), `hab` (weight normalization, feeds
row-stochasticity). NONE bundles the conclusion — the mixture kernel, its
feasibility (row-stochastic + distortion budget), and the affine objective are all
CONSTRUCTED/PROVEN in-body (~150 lines). The combined point lands at a genuine
`Fin (k₁+k₂)` index via `wzRateValueSet_reindex_mem` (not empty/degenerate).
Stated over the reshaped ⋃-over-`Fin k` value set. Break attempts: `a=0` reduces
to `hv₂` (alive, non-vacuous); `D₁=D₂` gives genuine midpoint time-sharing. -/
theorem wzRateValueSet_timeShare_mem
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    {d : α → γ → ℝ} {D₁ D₂ : ℝ} {v₁ v₂ : ℝ}
    (hv₁ : v₁ ∈ wzRateValueSet P_XY d D₁)
    (hv₂ : v₂ ∈ wzRateValueSet P_XY d D₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * v₁ + b * v₂ ∈ wzRateValueSet P_XY d (a * D₁ + b * D₂) := by
  classical
  rw [mem_wzRateValueSet_iff] at hv₁ hv₂
  obtain ⟨k₁, ⟨q₁, f₁⟩, ⟨hfact₁, hdist₁⟩, hobj₁⟩ := hv₁
  obtain ⟨k₂, ⟨q₂, f₂⟩, ⟨hfact₂, hdist₂⟩, hobj₂⟩ := hv₂
  obtain ⟨κ₁, hκ₁nn, hκ₁sum, hκ₁eq⟩ := hfact₁
  obtain ⟨κ₂, hκ₂nn, hκ₂sum, hκ₂eq⟩ := hfact₂
  dsimp only at hobj₁ hobj₂ hdist₁ hdist₂ hκ₁eq hκ₂eq
  -- mixture point on the disjoint-union auxiliary alphabet `Fin k₁ ⊕ Fin k₂`
  set κmix : α → (Fin k₁ ⊕ Fin k₂) → ℝ :=
    fun x ↦ Sum.elim (fun i ↦ a * κ₁ x i) (fun j ↦ b * κ₂ x j) with hκmix
  set qmix : α × β × (Fin k₁ ⊕ Fin k₂) → ℝ :=
    fun p ↦ κmix p.1 p.2.2 * P_XY (p.1, p.2.1) with hqmix
  set fmix : (Fin k₁ ⊕ Fin k₂) × β → γ :=
    fun p ↦ Sum.elim (fun i ↦ f₁ (i, p.2)) (fun j ↦ f₂ (j, p.2)) p.1 with hfmix
  -- pointwise identities: the mixture joint restricts to a scaled copy on each branch
  have hqmix_inl : ∀ x y i, qmix (x, y, Sum.inl i) = a * q₁ (x, y, i) := by
    intro x y i
    show a * κ₁ x i * P_XY (x, y) = a * q₁ (x, y, i)
    rw [hκ₁eq x y i]; ring
  have hqmix_inr : ∀ x y j, qmix (x, y, Sum.inr j) = b * q₂ (x, y, j) := by
    intro x y j
    show b * κ₂ x j * P_XY (x, y) = b * q₂ (x, y, j)
    rw [hκ₂eq x y j]; ring
  -- branch identities for the XU and YU marginals
  have hmixXU_inl : ∀ x i, wzMarginalXU (Fin k₁ ⊕ Fin k₂) qmix (x, Sum.inl i)
      = a * wzMarginalXU (Fin k₁) q₁ (x, i) := by
    intro x i
    show (∑ y, qmix (x, y, Sum.inl i)) = a * ∑ y, q₁ (x, y, i)
    simp_rw [hqmix_inl, ← Finset.mul_sum]
  have hmixXU_inr : ∀ x j, wzMarginalXU (Fin k₁ ⊕ Fin k₂) qmix (x, Sum.inr j)
      = b * wzMarginalXU (Fin k₂) q₂ (x, j) := by
    intro x j
    show (∑ y, qmix (x, y, Sum.inr j)) = b * ∑ y, q₂ (x, y, j)
    simp_rw [hqmix_inr, ← Finset.mul_sum]
  have hmixYU_inl : ∀ y i, wzMarginalYU (Fin k₁ ⊕ Fin k₂) qmix (y, Sum.inl i)
      = a * wzMarginalYU (Fin k₁) q₁ (y, i) := by
    intro y i
    show (∑ x, qmix (x, y, Sum.inl i)) = a * ∑ x, q₁ (x, y, i)
    simp_rw [hqmix_inl, ← Finset.mul_sum]
  have hmixYU_inr : ∀ y j, wzMarginalYU (Fin k₁ ⊕ Fin k₂) qmix (y, Sum.inr j)
      = b * wzMarginalYU (Fin k₂) q₂ (y, j) := by
    intro y j
    show (∑ x, qmix (x, y, Sum.inr j)) = b * ∑ x, q₂ (x, y, j)
    simp_rw [hqmix_inr, ← Finset.mul_sum]
  -- both feasible points share the source's first marginal
  have hfstXU1 : marginalFst (wzMarginalXU (Fin k₁) q₁) = fun x ↦ ∑ y, P_XY (x, y) := by
    funext x
    show (∑ i, ∑ y, q₁ (x, y, i)) = ∑ y, P_XY (x, y)
    simp_rw [hκ₁eq]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hκ₁sum, one_mul]
  have hfstXU2 : marginalFst (wzMarginalXU (Fin k₂) q₂) = fun x ↦ ∑ y, P_XY (x, y) := by
    funext x
    show (∑ i, ∑ y, q₂ (x, y, i)) = ∑ y, P_XY (x, y)
    simp_rw [hκ₂eq]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hκ₂sum, one_mul]
  have hfstYU1 : marginalFst (wzMarginalYU (Fin k₁) q₁) = fun y ↦ ∑ x, P_XY (x, y) := by
    funext y
    show (∑ u, ∑ x, q₁ (x, y, u)) = ∑ x, P_XY (x, y)
    simp_rw [hκ₁eq]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hκ₁sum, one_mul]
  have hfstYU2 : marginalFst (wzMarginalYU (Fin k₂) q₂) = fun y ↦ ∑ x, P_XY (x, y) := by
    funext y
    show (∑ u, ∑ x, q₂ (x, y, u)) = ∑ x, P_XY (x, y)
    simp_rw [hκ₂eq]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hκ₂sum, one_mul]
  have hmargXU : marginalFst (wzMarginalXU (Fin k₁) q₁)
      = marginalFst (wzMarginalXU (Fin k₂) q₂) := by rw [hfstXU1, hfstXU2]
  have hmargYU : marginalFst (wzMarginalYU (Fin k₁) q₁)
      = marginalFst (wzMarginalYU (Fin k₂) q₂) := by rw [hfstYU1, hfstYU2]
  -- total masses (both feasible points are pmfs)
  have hmassXU1 : ∑ z, wzMarginalXU (Fin k₁) q₁ z = 1 := by
    rw [Fintype.sum_prod_type (f := wzMarginalXU (Fin k₁) q₁)]
    have h : ∀ x, ∑ i, wzMarginalXU (Fin k₁) q₁ (x, i) = ∑ y, P_XY (x, y) := by
      intro x; have := congrFun hfstXU1 x; simpa [marginalFst] using this
    simp_rw [h]; rw [← Fintype.sum_prod_type (f := P_XY)]; exact h_pmf.2
  have hmassXU2 : ∑ z, wzMarginalXU (Fin k₂) q₂ z = 1 := by
    rw [Fintype.sum_prod_type (f := wzMarginalXU (Fin k₂) q₂)]
    have h : ∀ x, ∑ i, wzMarginalXU (Fin k₂) q₂ (x, i) = ∑ y, P_XY (x, y) := by
      intro x; have := congrFun hfstXU2 x; simpa [marginalFst] using this
    simp_rw [h]; rw [← Fintype.sum_prod_type (f := P_XY)]; exact h_pmf.2
  have hmassYU1 : ∑ z, wzMarginalYU (Fin k₁) q₁ z = 1 := by
    rw [Fintype.sum_prod_type (f := wzMarginalYU (Fin k₁) q₁)]
    have h : ∀ y, ∑ u, wzMarginalYU (Fin k₁) q₁ (y, u) = ∑ x, P_XY (x, y) := by
      intro y; have := congrFun hfstYU1 y; simpa [marginalFst] using this
    simp_rw [h]; rw [Finset.sum_comm, ← Fintype.sum_prod_type (f := P_XY)]; exact h_pmf.2
  have hmassYU2 : ∑ z, wzMarginalYU (Fin k₂) q₂ z = 1 := by
    rw [Fintype.sum_prod_type (f := wzMarginalYU (Fin k₂) q₂)]
    have h : ∀ y, ∑ u, wzMarginalYU (Fin k₂) q₂ (y, u) = ∑ x, P_XY (x, y) := by
      intro y; have := congrFun hfstYU2 y; simpa [marginalFst] using this
    simp_rw [h]; rw [Finset.sum_comm, ← Fintype.sum_prod_type (f := P_XY)]; exact h_pmf.2
  -- objective is affine: mixture-affinity of `mutualInfoPmf`
  have hXU : wzMutualInfoXU (Fin k₁ ⊕ Fin k₂) qmix
      = a * wzMutualInfoXU (Fin k₁) q₁ + b * wzMutualInfoXU (Fin k₂) q₂ := by
    unfold wzMutualInfoXU
    exact mutualInfoPmf_mixture_affine hmassXU1 hmassXU2 hmargXU hab hmixXU_inl hmixXU_inr
  have hYU : wzMutualInfoYU (Fin k₁ ⊕ Fin k₂) qmix
      = a * wzMutualInfoYU (Fin k₁) q₁ + b * wzMutualInfoYU (Fin k₂) q₂ := by
    unfold wzMutualInfoYU
    exact mutualInfoPmf_mixture_affine hmassYU1 hmassYU2 hmargYU hab hmixYU_inl hmixYU_inr
  have hobj : wzMutualInfoXU (Fin k₁ ⊕ Fin k₂) qmix - wzMutualInfoYU (Fin k₁ ⊕ Fin k₂) qmix
      = a * v₁ + b * v₂ := by rw [hXU, hYU, ← hobj₁, ← hobj₂]; ring
  -- feasibility of the mixture point at the mixed budget
  have hfeas : (qmix, fmix)
      ∈ WynerZivFactorizableConstraint (Fin k₁ ⊕ Fin k₂) P_XY d (a * D₁ + b * D₂) := by
    refine ⟨⟨κmix, ?_, ?_, ?_⟩, ?_⟩
    · -- non-negativity of the mixture kernel
      intro x c
      cases c with
      | inl i => exact mul_nonneg ha (hκ₁nn x i)
      | inr j => exact mul_nonneg hb (hκ₂nn x j)
    · -- row-stochasticity of the mixture kernel
      intro x
      rw [Fintype.sum_sum_type]
      simp only [hκmix, Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hκ₁sum, hκ₂sum, mul_one, mul_one]
      exact hab
    · -- factorization of the mixture joint
      intro x y c; rfl
    · -- distortion splits affinely, hence stays within the mixed budget
      have hdistsplit : wzExpectedDistortion (Fin k₁ ⊕ Fin k₂) d qmix fmix
          = a * wzExpectedDistortion (Fin k₁) d q₁ f₁
            + b * wzExpectedDistortion (Fin k₂) d q₂ f₂ := by
        let E' : (α × β × Fin k₁) ⊕ (α × β × Fin k₂) ≃ α × β × (Fin k₁ ⊕ Fin k₂) :=
          { toFun := Sum.elim (fun p ↦ (p.1, p.2.1, Sum.inl p.2.2))
              (fun p ↦ (p.1, p.2.1, Sum.inr p.2.2))
            invFun := fun p ↦ Sum.elim (fun i ↦ Sum.inl (p.1, p.2.1, i))
              (fun j ↦ Sum.inr (p.1, p.2.1, j)) p.2.2
            left_inv := by rintro (⟨x, y, i⟩ | ⟨x, y, j⟩) <;> rfl
            right_inv := by rintro ⟨x, y, (i | j)⟩ <;> rfl }
        unfold wzExpectedDistortion
        rw [← Equiv.sum_comp E' (fun p ↦ qmix p * d p.1 (fmix (p.2.2, p.2.1)))]
        rw [Fintype.sum_sum_type]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p₁ _ ↦ ?_)
          obtain ⟨x, y, i⟩ := p₁
          change qmix (x, y, Sum.inl i) * d x (f₁ (i, y))
              = a * (q₁ (x, y, i) * d x (f₁ (i, y)))
          rw [hqmix_inl]; ring
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p₂ _ ↦ ?_)
          obtain ⟨x, y, j⟩ := p₂
          change qmix (x, y, Sum.inr j) * d x (f₂ (j, y))
              = b * (q₂ (x, y, j) * d x (f₂ (j, y)))
          rw [hqmix_inr]; ring
      rw [hdistsplit]
      have h1 : a * wzExpectedDistortion (Fin k₁) d q₁ f₁ ≤ a * D₁ :=
        mul_le_mul_of_nonneg_left hdist₁ ha
      have h2 : b * wzExpectedDistortion (Fin k₂) d q₂ f₂ ≤ b * D₂ :=
        mul_le_mul_of_nonneg_left hdist₂ hb
      linarith
  have hmem := wzRateValueSet_reindex_mem (P_XY := P_XY) (d := d) hfeas
  rwa [hobj] at hmem

/-- **Convexity of the reshaped Wyner–Ziv rate in `D`.** Directly from the
time-sharing closure `wzRateValueSet_timeShare_mem`: every mixture `a·v₁ + b·v₂`
lies in the value set at the mixed budget, so its infimum is bounded above by
`a·v₁ + b·v₂` for all attainable `v₁, v₂`; taking nested infima gives the convex
bound. The `Nonempty` side conditions feed `le_csInf` (via `le_mul_csInf`) and
`BddBelow` at the mixed budget feeds `csInf_le`; both are standard regularity
preconditions, not load-bearing core.

@audit:ok (independent honesty audit 2026-07-05, auditor-verified not self-reported:
sorryAx-free, `#print axioms` = [propext, Classical.choice, Quot.sound]). Signature
honest: `h_ne₁`/`h_ne₂` are the `Nonempty` side conditions of `le_csInf` (via
`le_mul_csInf`), `h_bdd_mix` is the `BddBelow` side condition of `csInf_le` — both
standard infimum regularity (side conditions of the sInf lemmas, NOT the theorem's
asserted value, mirroring the already-audited `wynerZivRate_antitone`). `h_pmf`
feeds `wzRateValueSet_timeShare_mem`; `ha`/`hb`/`hab` are convex weights. The
convexity content is proven in-body via the time-sharing closure + nested infima,
not bundled. Convexity direction and coefficients verified correct; `a=1,b=0`
boundary reduces to reflexivity (alive), stated over the reshaped `wynerZivRate`. -/
theorem wynerZivRate_convex_in_D
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    {d : α → γ → ℝ} {D₁ D₂ : ℝ}
    (h_ne₁ : (wzRateValueSet P_XY d D₁).Nonempty)
    (h_ne₂ : (wzRateValueSet P_XY d D₂).Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h_bdd_mix : BddBelow (wzRateValueSet P_XY d (a * D₁ + b * D₂))) :
    wynerZivRate P_XY d (a * D₁ + b * D₂)
      ≤ a * wynerZivRate P_XY d D₁ + b * wynerZivRate P_XY d D₂ := by
  -- every mixture value lies in the value set at the mixed budget
  have key : ∀ v₁ ∈ wzRateValueSet P_XY d D₁, ∀ v₂ ∈ wzRateValueSet P_XY d D₂,
      wynerZivRate P_XY d (a * D₁ + b * D₂) ≤ a * v₁ + b * v₂ := by
    intro v₁ hv₁ v₂ hv₂
    exact csInf_le h_bdd_mix (wzRateValueSet_timeShare_mem h_pmf hv₁ hv₂ ha hb hab)
  -- infimum over the second budget
  have step1 : ∀ v₁ ∈ wzRateValueSet P_XY d D₁,
      wynerZivRate P_XY d (a * D₁ + b * D₂) ≤ a * v₁ + b * wynerZivRate P_XY d D₂ := by
    intro v₁ hv₁
    have hstep : wynerZivRate P_XY d (a * D₁ + b * D₂) - a * v₁
        ≤ b * wynerZivRate P_XY d D₂ := by
      refine le_mul_csInf h_ne₂ hb ?_
      intro v₂ hv₂
      have hk := key v₁ hv₁ v₂ hv₂
      linarith
    linarith
  -- infimum over the first budget
  have hstep : wynerZivRate P_XY d (a * D₁ + b * D₂) - b * wynerZivRate P_XY d D₂
      ≤ a * wynerZivRate P_XY d D₁ := by
    refine le_mul_csInf h_ne₁ ha ?_
    intro v₁ hv₁
    have := step1 v₁ hv₁
    linarith
  linarith

/-- **Weighted (n-ary) time-sharing closure of the reshaped value set.** Induction
over the finite index set `s` of the binary closure `wzRateValueSet_timeShare_mem`:
a convex combination `∑ i, p i · w i` of attainable objective values (each `w i`
attainable at its own budget `Dv i`) is attainable at the mixed budget
`∑ i, p i · Dv i`. The tail weights are renormalized so the binary lemma applies at
each induction step. -/
lemma wzRateValueSet_weightedSum_mem
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    {d : α → γ → ℝ}
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {w Dv p : ι → ℝ}
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1)
    (hmem : ∀ i ∈ s, w i ∈ wzRateValueSet P_XY d (Dv i)) :
    (∑ i ∈ s, p i * w i) ∈ wzRateValueSet P_XY d (∑ i ∈ s, p i * Dv i) := by
  classical
  refine Finset.Nonempty.cons_induction
    (motive := fun s _ => ∀ (p : ι → ℝ), (∀ i ∈ s, 0 ≤ p i) → (∑ i ∈ s, p i = 1) →
      (∀ i ∈ s, w i ∈ wzRateValueSet P_XY d (Dv i)) →
      (∑ i ∈ s, p i * w i) ∈ wzRateValueSet P_XY d (∑ i ∈ s, p i * Dv i))
    ?_ ?_ hs p hp_nn hp_sum hmem
  · -- singleton `{i}`: `p i = 1`, both sides collapse to `w i` / `Dv i`
    intro i q _ hq_sum hq_mem
    simp only [Finset.sum_singleton] at hq_sum ⊢
    rw [hq_sum, one_mul, one_mul]
    exact hq_mem i (Finset.mem_singleton_self i)
  · -- cons `insert j t`: renormalize tail weights and apply the binary lemma
    intro j t hj ht IH q hq_nn hq_sum hq_mem
    rw [Finset.sum_cons] at hq_sum
    have haj : 0 ≤ q j := hq_nn j (Finset.mem_cons_self j t)
    have hb_nn : 0 ≤ ∑ i ∈ t, q i :=
      Finset.sum_nonneg (fun i hi => hq_nn i (Finset.mem_cons_of_mem hi))
    rcases eq_or_lt_of_le hb_nn with hb0 | hbpos
    · -- `b = 0`: all tail weights vanish, so `a = 1` and everything collapses to `j`
      have hzero : ∀ i ∈ t, q i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i hi => hq_nn i (Finset.mem_cons_of_mem hi))).1 hb0.symm
      have hsum_w : ∑ i ∈ t, q i * w i = 0 :=
        Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_mul])
      have hsum_Dv : ∑ i ∈ t, q i * Dv i = 0 :=
        Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_mul])
      have hqj1 : q j = 1 := by rw [← hb0, add_zero] at hq_sum; exact hq_sum
      rw [Finset.sum_cons, Finset.sum_cons, hsum_w, hsum_Dv, add_zero, add_zero,
        hqj1, one_mul, one_mul]
      exact hq_mem j (Finset.mem_cons_self j t)
    · -- `0 < b`: renormalize `p' i := q i / b`, apply IH then the binary lemma
      have hb_ne : (∑ i ∈ t, q i) ≠ 0 := hbpos.ne'
      have hp'_nn : ∀ i ∈ t, 0 ≤ q i / (∑ k ∈ t, q k) := fun i hi =>
        div_nonneg (hq_nn i (Finset.mem_cons_of_mem hi)) hbpos.le
      have hp'_sum : ∑ i ∈ t, q i / (∑ k ∈ t, q k) = 1 := by
        rw [← Finset.sum_div, div_self hb_ne]
      have hp'_mem : ∀ i ∈ t, w i ∈ wzRateValueSet P_XY d (Dv i) := fun i hi =>
        hq_mem i (Finset.mem_cons_of_mem hi)
      have hIH := IH (fun i => q i / (∑ k ∈ t, q k)) hp'_nn hp'_sum hp'_mem
      have hbin := wzRateValueSet_timeShare_mem h_pmf
        (hq_mem j (Finset.mem_cons_self j t)) hIH haj hbpos.le hq_sum
      have heq_w : (∑ i ∈ Finset.cons j t hj, q i * w i)
          = q j * w j + (∑ i ∈ t, q i) * (∑ i ∈ t, q i / (∑ k ∈ t, q k) * w i) := by
        rw [Finset.sum_cons, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        field_simp
      have heq_Dv : (∑ i ∈ Finset.cons j t hj, q i * Dv i)
          = q j * Dv j + (∑ i ∈ t, q i) * (∑ i ∈ t, q i / (∑ k ∈ t, q k) * Dv i) := by
        rw [Finset.sum_cons, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        field_simp
      rw [heq_w, heq_Dv]
      exact hbin

/-- **Uniform `Fin n` time-sharing corollary.** The average `(1/n)·∑ᵢ w i` of `n`
attainable objective values is attainable at the averaged budget `(1/n)·∑ᵢ Dv i`.
Specialization of `wzRateValueSet_weightedSum_mem` to uniform weights `p ≡ 1/n`;
this is the form the operational converse consumes. -/
lemma wzRateValueSet_avg_mem
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    {d : α → γ → ℝ} {n : ℕ} (hn : 0 < n)
    {w Dv : Fin n → ℝ}
    (hmem : ∀ i, w i ∈ wzRateValueSet P_XY d (Dv i)) :
    ((1 / (n : ℝ)) * ∑ i, w i) ∈ wzRateValueSet P_XY d ((1 / (n : ℝ)) * ∑ i, Dv i) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsum1 : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div, div_self hn0]
  have hkey := wzRateValueSet_weightedSum_mem h_pmf (d := d)
    (s := (Finset.univ : Finset (Fin n))) (hs := Finset.univ_nonempty)
    (w := w) (Dv := Dv) (p := fun _ => 1 / (n : ℝ))
    (hp_nn := fun i _ => by positivity) (hp_sum := hsum1) (hmem := fun i _ => hmem i)
  rw [Finset.mul_sum, Finset.mul_sum]
  exact hkey

end AllAuxRate

end InformationTheory.Shannon
