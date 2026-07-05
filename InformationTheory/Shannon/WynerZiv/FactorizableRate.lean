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

/-! ## §1 Factorisation predicate -/

section FactorisationPredicate

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Affine factorisation predicate. The joint pmf `q : α × β × U → ℝ` is
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
@[entry_point]
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

/-- Markov chain holds automatically on factorisable joints. The
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

/-- `(X, Y)`-marginal of a factorisable joint recovers `P_XY` (when the
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

/-- Factorisable joints are non-negative pointwise (when `P_XY` is). -/
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

/-- Total mass of a factorisable joint equals total mass of `P_XY`. When
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

/-- `stdSimplex` membership for factorisable joints over a pmf source.
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

/-- Convex combinations of factorisable joints are factorisable. This is
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

/-! ## §4 Factorisable constraint set -/

section FactorisableConstraintSet

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Factorisable Wyner–Ziv constraint set. A `(q, f)` pair belongs iff:
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
@[entry_point]
lemma mem_WynerZivFactorizableConstraint_iff
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    {qf : (α × β × U → ℝ) × (U × β → γ)} :
    qf ∈ WynerZivFactorizableConstraint U P_XY d D ↔
      IsWynerZivFactorizable U P_XY qf.1
        ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D := Iff.rfl

/-- Factorisable constraint ⊆ raw constraint. Every factorisable
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

/-- Factorisable constraint set is monotone in `D`. Mirror of
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

This is the structural step that turns convexity into a one-liner on
factorisable joints: feasibility survives convex combinations on the
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

/-! ## §7 Factorisable rate function and its convexity -/

section FactorisableRate

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Wyner–Ziv rate function restricted to factorisable joints.
`R_WZ_fact(D) := sInf { I(X;U) − I(Y;U) | (q, f) ∈ WynerZivFactorizableConstraint U P_XY d D }`.

This is the form Cover–Thomas §15.9 directly addresses: the minimisation
over auxiliary kernels `κ(u|x)` with side-information decoders `f(u,y)`. -/
noncomputable def wynerZivRateFactorizable
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ :=
  sInf ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivFactorizableConstraint U P_XY d D)

/-- Factorisable rate is antitone in `D` (mirror of the raw
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

/-! ## §8 BddBelow on factorisable image (simplex projection route) -/

section FactorisableBddBelow

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- The factorisable image is `BddBelow`. Same simplex-projection route
as in `WynerZiv/RateMonotonicity.lean`: the factorisable image is contained in the
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
  -- Image of factorisable constraint is contained in image of raw constraint.
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
Carathéodory support argument (the single-letterisation auxiliary
`Uᵢ := (J, Y^{i-1})` has a cardinality that grows with the block length, so it
does not embed into a fixed `U` without the `|U| ≤ |α| + 1` reduction).

This section adds the reshaped rate `wynerZivRate` — the infimum of the
objective over feasible factorisable points at *every* finite auxiliary
alphabet `Fin k` simultaneously. A large single-letterisation auxiliary then
lands directly as a feasible point of the reshaped infimum, with no cardinality
bound.

### Non-degeneracy (junk-`sInf` guard)

`wynerZivRateFactorizable U = sInf (image)` and, in `ℝ`, `sInf ∅ = 0`. A naive
`⨅ k, wynerZivRateFactorizable (Fin k) D` would inject a junk `0` at every index
`k` whose factorisable constraint is empty (e.g. `k = 0`: `Fin 0` is empty, so
no row-stochastic kernel exists), collapsing the infimum to `≤ 0`. That would
make the converse `wynerZivRate ≤ R` vacuously true — a degenerate-definition
defect.

The `⋃`-then-`sInf` form (`wzRateValueSet`) avoids this: empty-constraint
indices contribute the *empty* image, so they inject no value. The remaining
lower bound comes from the objective's non-negativity on the factorisable
manifold (data-processing inequality `I(X;U) − I(Y;U) ≥ 0` for the Markov chain
`U − X − Y`), established in `Converse.lean` and used to discharge `BddBelow`. -/

section AllAuxRate

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]

/-- The set of Wyner–Ziv objective values `I(X;U) − I(Y;U)` attainable by a
factorisable feasible point at *some* finite auxiliary alphabet `Fin k`, with
`k` ranging over all of `ℕ`. Feasibility-empty indices contribute the empty
image (no value), so this set carries no junk `sInf ∅ = 0` term. -/
def wzRateValueSet
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : Set ℝ :=
  ⋃ k : ℕ,
    (fun qf : (α × β × Fin k → ℝ) × (Fin k × β → γ) ↦
        wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1)
      '' WynerZivFactorizableConstraint (Fin k) P_XY d D

/-- Reshaped Wyner–Ziv operational rate: the infimum of the objective
`I(X;U) − I(Y;U)` over feasible factorisable points at *every* finite auxiliary
alphabet `Fin k` at once, rather than a single caller-fixed `U`.

This is the `∀`-clean form needed by the operational converse: the
single-letterisation auxiliary lands directly as a feasible point (see
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
of a feasible factorisable point at some finite auxiliary alphabet `Fin k`. -/
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

/-- A feasible factorisable point at auxiliary alphabet `Fin k` produces a value
in `wzRateValueSet` (witness for non-emptiness). -/
lemma objective_mem_wzRateValueSet
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    {k : ℕ} {qf : (α × β × Fin k → ℝ) × (Fin k × β → γ)}
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k) P_XY d D) :
    wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1
      ∈ wzRateValueSet P_XY d D :=
  mem_wzRateValueSet_iff.mpr ⟨k, qf, hqf, rfl⟩

/-- **Landing lemma (direct, `Fin k` form).** Any feasible factorisable point at
auxiliary alphabet `Fin k` bounds the reshaped rate from above. This is what
lets the single-letterisation auxiliary land *directly*, with no cardinality
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
factorisable point at budget `D` remains feasible at `D' ≥ D`
(`WynerZivFactorizableConstraint_mono_in_D`, applied at each auxiliary alphabet
`Fin k`). -/
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
`wzRateValueSet_bddBelow_of_pmf` and a feasible witness). -/
theorem wynerZivRate_antitone
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D D' : ℝ} (hD : D ≤ D')
    (h_bdd : BddBelow (wzRateValueSet P_XY d D'))
    (h_ne : (wzRateValueSet P_XY d D).Nonempty) :
    wynerZivRate P_XY d D' ≤ wynerZivRate P_XY d D := by
  unfold wynerZivRate
  exact csInf_le_csInf h_bdd h_ne (wzRateValueSet_mono_in_D hD)

end AllAuxRate

end InformationTheory.Shannon
