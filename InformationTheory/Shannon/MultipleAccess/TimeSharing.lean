import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Achievability
import Mathlib.Analysis.Convex.Topology

/-!
# Multiple access channel — time-sharing achievability (full convex-hull form)

Operational time-sharing for the two-user MAC (Cover–Thomas Theorem 15.3.1, convex-hull
form).  The single-input corner-point achievability `mac_achievability` (proven, `@audit:ok`)
is the input; this file lifts it to the convex hull of the per-input pentagons via block
concatenation.

## Main definitions

* `MACAchievable W R₁ R₂` — the operational achievability predicate for the rate pair
  `(R₁, R₂)`: for every target error `ε' > 0`, eventually (in the block length `n`) there is
  a length-`n` two-user code with at least `⌈exp (n R₁)⌉` / `⌈exp (n R₂)⌉` messages per user
  and average error probability `< ε'`.  This is exactly the conclusion of
  `mac_achievability`, abstracted over `ε'`.
* `macPentagon p₁ p₂ W` — the corner-point pentagon of the independent product input
  `p₁ ⊗ p₂`: rate pairs bounded by `macInfo₁`, `macInfo₂`, `macInfoBoth`.
* `macCapacityRegion W` — the operational capacity region, the topological closure of the
  achievable set.  (The exact-rate achievable set is not closed — boundary Pareto faces
  enter only in the closure — so the region is defined as its closure.)
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β]  [DecidableEq β]  [Nonempty β]  [MeasurableSpace β]  [MeasurableSingletonClass β]

/-! ## Operational achievability predicate -/

/-- The operational achievability predicate for the MAC rate pair `(R₁, R₂)`: for every
target error `ε' > 0` there is a block length `N` such that for all `n ≥ N` there is a
length-`n` two-user code with at least `⌈exp (n R₁)⌉` / `⌈exp (n R₂)⌉` messages per user
whose average error probability is `< ε'`.  This is the `∀ ε'`-abstraction of the
conclusion of `mac_achievability`. -/
def MACAchievable (W : MACChannel α₁ α₂ β) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ n, N ≤ n →
    ∃ (M₁ M₂ : ℕ) (_ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
      (_ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
      (c : MACCode M₁ M₂ n α₁ α₂ β),
      (c.averageErrorProb W).toReal < ε'

/-- The corner-point pentagon of the independent product input `p₁ ⊗ p₂`: rate pairs with
`0 ≤ R₁`, `0 ≤ R₂`, `R₁ ≤ macInfo₁`, `R₂ ≤ macInfo₂`, `R₁ + R₂ ≤ macInfoBoth`. -/
def macPentagon (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) :
    Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ p₁ p₂ W ∧ p.2 ≤ macInfo₂ p₁ p₂ W
       ∧ p.1 + p.2 ≤ macInfoBoth p₁ p₂ W}

/-- The operational MAC capacity region: the topological closure of the achievable set.
The exact-rate achievable set is not closed (boundary Pareto faces enter only in the
closure), so the capacity region is defined as its closure. -/
def macCapacityRegion (W : MACChannel α₁ α₂ β) : Set (ℝ × ℝ) :=
  closure {p | MACAchievable W p.1 p.2}

/-! ## Monotonicity and the strict-interior wrapper -/

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Achievability is a down-set in the rate pair: a lower rate pair is easier. -/
theorem mac_achievable_mono {W : MACChannel α₁ α₂ β} {R₁ R₂ R₁' R₂' : ℝ}
    (h : MACAchievable W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) :
    MACAchievable W R₁' R₂' := by
  intro ε' hε'
  obtain ⟨N, hN⟩ := h ε' hε'
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
  have hmul₁ : (n : ℝ) * R₁' ≤ (n : ℝ) * R₁ :=
    mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg n)
  have hmul₂ : (n : ℝ) * R₂' ≤ (n : ℝ) * R₂ :=
    mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg n)
  exact ⟨M₁, M₂,
    le_trans (Nat.ceil_mono (Real.exp_le_exp.mpr hmul₁)) hM₁,
    le_trans (Nat.ceil_mono (Real.exp_le_exp.mpr hmul₂)) hM₂, c, hc⟩

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- The strict interior of a pentagon is achievable: a rate pair strictly inside the
corner-point region of a full-support product input `p₁ ⊗ p₂` is achievable.  This is the
`∀ ε'`-abstraction of `mac_achievability`. -/
theorem mac_strict_interior_achievable
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hR₁lt : R₁ < macInfo₁ p₁ p₂ W) (hR₂lt : R₂ < macInfo₂ p₁ p₂ W)
    (hRsum : R₁ + R₂ < macInfoBoth p₁ p₂ W) :
    MACAchievable W R₁ R₂ := by
  intro ε' hε'
  exact mac_achievability p₁ p₂ W hp₁ hp₂ hW hR₁ hR₂ hR₁lt hR₂lt hRsum hε'

/-! ## Gateway: time-sharing convexity via block concatenation -/

/-- **Time-sharing convexity of the achievable set (gateway).** The convex combination of
two achievable rate pairs is achievable, realised operationally by concatenating a
length-`n₁` code (rate `(a₁, a₂)`) and a length-`n₂` code (rate `(b₁, b₂)`) with
`n₁ / (n₁ + n₂) → lam`.

@residual(plan:mac-timesharing-plan)

WARNING — suspected false-as-framed at boundary points.  The exact-rate conclusion
`MACAchievable W (lam·a₁ + (1-lam)·b₁) (lam·a₂ + (1-lam)·b₂)` (both ceilings hit exactly)
is *not* achievable by block concatenation when `a₁ > b₁ ∧ a₂ < b₂` (or the symmetric
case).  With `n₁ + n₂ = n` the concatenated message count is
`M₁ = M₁¹·M₁² ≥ ⌈exp(n₁ a₁)⌉·⌈exp(n₂ b₁)⌉`, whose log-rate is
`(n₁ a₁ + n₂ b₁)/n = R₁ + (n₁ - lam·n)(a₁ - b₁)/n`.  Since `n₁ ∈ {⌊lam n⌋, ⌈lam n⌉}` the
sign of `n₁ - lam·n` is fixed, so `(n₁ - lam·n)(a₁ - b₁)` and `(n₁ - lam·n)(a₂ - b₂)` have
opposite signs when `(a₁ - b₁)` and `(a₂ - b₂)` do; one user then undershoots
`⌈exp(n R)⌉` by a constant factor `exp(Θ(1))` for infinitely many `n`, and no single `n₁`
fixes both.  Concrete refutation of the concatenation route: `lam = 1/√2`,
`(a₁,a₂) = (2,1)`, `(b₁,b₂) = (1,2)`.  These convex-hull points lie outside every single
pentagon, so `mac_achievability` alone does not cover them either.  The honest true form is
the strict-rate version `R₁ < lam·a₁ + (1-lam)·b₁ ∧ R₂ < lam·a₂ + (1-lam)·b₂ →
MACAchievable W R₁ R₂` (the strict gap absorbs the `O(1)/n` rounding), which suffices to
make `macCapacityRegion = closure {MACAchievable}` convex without needing exact-point
convexity of `{MACAchievable}`.  This is a design decision for the planner /
proof-pivot-advisor: the signature below is left in the plan's exact form pending that
review, not proven. -/
theorem mac_timesharing_concat_achievable (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {a₁ a₂ b₁ b₂ lam : ℝ} (ha : MACAchievable W a₁ a₂) (hb : MACAchievable W b₁ b₂)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    MACAchievable W (lam * a₁ + (1 - lam) * b₁) (lam * a₂ + (1 - lam) * b₂) := by
  sorry

end InformationTheory.Shannon.MAC
