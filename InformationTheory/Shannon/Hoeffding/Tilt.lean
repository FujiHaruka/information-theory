import InformationTheory.Shannon.Hoeffding.BoundaryMinimizer
import InformationTheory.Meta.EntryPoint

/-!
# Hoeffding tradeoff — interior gradient body (Lagrange tilt)

For the interior regime `0 < α < klDivPmf P₂ P₁`, the Csiszár I-projection
of `P₂` onto the constraint set `K(α)` is the one-parameter exponential tilt

      `Qstar a = c(λ) · P₁ a ^ (1 - λ) · P₂ a ^ λ`,

which is exactly `Chernoff.chernoffMediator P₁ P₂ λ`. This file reuses that
family (no new definition) and proves its defining gradient property:

      `log (Qstar a) - (1 - λ) · log (P₁ a) - λ · log (P₂ a)`  is constant in a
      (it equals `-log Z(λ)`).

This is the Lagrange first-order condition `∇[D(Q‖P₂) + μ D(Q‖P₁)] = const`:
the log-likelihood ratio of the tilt against the geometric mean of `P₁, P₂` is
flat across the alphabet. The constant-log-ratio identity is a pure-algebra fact
about `rpow`.

The interior characterization decomposes into two sub-predicates:

* `IsKLGradientHyp P₁ P₂ alpha lam Qstar` — discharged for the tilt
  `Qstar = chernoffMediator P₁ P₂ lam`: the constant-log-ratio stationarity
  above, plus full support and `Qstar ∈ stdSimplex`.

* `IsHoeffdingLagrangeHyp P₁ P₂ alpha lam` — the tilt at `lam` matches the
  constraint (`klDivPmf (tilt) P₁ ≤ alpha`) and realises the infimum
  (`hoeffdingE2 = klDivPmf (tilt) P₂`). The existence of a `lam ∈ (0,1)` solving
  `klDivPmf (tilt) P₁ = alpha` is the implicit-function step (monotonicity of
  `λ ↦ klDivPmf T_λ P₁`).

## What this file publishes

* `hoeffdingTilt` — the closed-form Lagrange minimizer (a `chernoffMediator`
  alias) with its positivity / pmf facts re-exported.

* `hoeffdingTilt_log_ratio_const` — the Lagrange gradient identity
  (constant log-ratio across the alphabet).

* `IsKLGradientHyp` — gradient sub-predicate, with constructor
  `isKLGradientHyp_tilt` discharging it for the tilt family.

* `IsHoeffdingLagrangeHyp` — Lagrange constraint-match sub-predicate.

* `isHoeffdingMinimizerFullSupport_of_lagrange` — the tilt is full support
  (purely constructive from `hoeffdingTilt_pos`).
-/

namespace InformationTheory.Shannon.HoeffdingTilt

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingSandwich
open InformationTheory.Shannon.HoeffdingBoundaryMinimizer
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Closed-form Lagrange minimizer (`chernoffMediator` alias) -/

/-- Closed-form Lagrange / KKT minimizer of `klDivPmf · P₂` on `K(α)`:
the exponential tilt `Qstar a = P₁ a ^ (1-λ) · P₂ a ^ λ / Z(λ)`.

This is definitionally `Chernoff.chernoffMediator P₁ P₂ lam`; we expose it under
the Hoeffding name so the interior characterization reads in terms of the
tradeoff problem rather than the Chernoff bound. -/
noncomputable def hoeffdingTilt (P₁ P₂ : α → ℝ) (lam : ℝ) : α → ℝ :=
  chernoffMediator P₁ P₂ lam

omit [DecidableEq α] in
lemma hoeffdingTilt_eq_chernoffMediator (P₁ P₂ : α → ℝ) (lam : ℝ) :
    hoeffdingTilt P₁ P₂ lam = chernoffMediator P₁ P₂ lam := rfl

omit [DecidableEq α] in
/-- The tilt is positive under full support. -/
lemma hoeffdingTilt_pos
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    0 < hoeffdingTilt P₁ P₂ lam a :=
  chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a

omit [DecidableEq α] in
/-- The tilt sums to `1`. -/
lemma hoeffdingTilt_sum_eq_one
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    (∑ a, hoeffdingTilt P₁ P₂ lam a) = 1 :=
  chernoffMediator_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam

omit [DecidableEq α] in
/-- The tilt lies in the simplex. -/
lemma hoeffdingTilt_mem_stdSimplex
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    hoeffdingTilt P₁ P₂ lam ∈ stdSimplex ℝ α :=
  ⟨fun a ↦ (hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam a).le,
   hoeffdingTilt_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam⟩

/-! ## Lagrange gradient identity (constant log-ratio) -/

omit [DecidableEq α] in
/-- Lagrange gradient stationarity (constant log-ratio): for the tilt
`Qstar = hoeffdingTilt P₁ P₂ lam`, the log-likelihood combination

    `log (Qstar a) - (1 - lam) · log (P₁ a) - lam · log (P₂ a)`

is constant in `a` (it equals `-log Z(λ)`). This is the Csiszár Lagrange
first-order condition `∇[D(·‖P₂) + μ D(·‖P₁)] = const`; the explicit constant
makes the stationarity dischargeable as pure `rpow` algebra. -/
lemma hoeffdingTilt_log_ratio_const
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    Real.log (hoeffdingTilt P₁ P₂ lam a)
        - (1 - lam) * Real.log (P₁ a) - lam * Real.log (P₂ a)
      = -Real.log (chernoffZSum P₁ P₂ lam) := by
  -- tilt a = (P₁ a)^(1-lam) * (P₂ a)^lam / Z, Z > 0.
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  have h_num_pos : 0 < (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam :=
    mul_pos (Real.rpow_pos_of_pos (hP₁_pos a) _) (Real.rpow_pos_of_pos (hP₂_pos a) _)
  -- log (tilt a) = (1-lam) log P₁ + lam log P₂ - log Z.
  have h_log_tilt :
      Real.log (hoeffdingTilt P₁ P₂ lam a)
        = (1 - lam) * Real.log (P₁ a) + lam * Real.log (P₂ a)
          - Real.log (chernoffZSum P₁ P₂ lam) := by
    rw [hoeffdingTilt, chernoffMediator]
    rw [Real.log_div h_num_pos.ne' hZ_pos.ne']
    rw [Real.log_mul (Real.rpow_pos_of_pos (hP₁_pos a) _).ne'
      (Real.rpow_pos_of_pos (hP₂_pos a) _).ne']
    rw [Real.log_rpow (hP₁_pos a), Real.log_rpow (hP₂_pos a)]
  rw [h_log_tilt]
  ring

omit [DecidableEq α] in
/-- Pairwise flatness: a corollary stating that the log-ratio combination
agrees at any two points `a, b`. This is the gradient condition in the form
"`∇` is constant", convenient for the KKT consumer. -/
lemma hoeffdingTilt_log_ratio_eq
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a b : α) :
    Real.log (hoeffdingTilt P₁ P₂ lam a)
        - (1 - lam) * Real.log (P₁ a) - lam * Real.log (P₂ a)
      = Real.log (hoeffdingTilt P₁ P₂ lam b)
        - (1 - lam) * Real.log (P₁ b) - lam * Real.log (P₂ b) := by
  rw [hoeffdingTilt_log_ratio_const P₁ P₂ hP₁_pos hP₂_pos lam a,
      hoeffdingTilt_log_ratio_const P₁ P₂ hP₁_pos hP₂_pos lam b]

/-! ## Gradient sub-predicate (`IsKLGradientHyp`) -/

/-- KL gradient sub-predicate: bundles the constant-log-ratio gradient
stationarity at parameter `lam` together with full support and simplex
membership of `Qstar`.

The `alpha` argument is kept for interface symmetry with the interior
predicates (the gradient condition itself does not depend on `alpha`). -/
structure IsKLGradientHyp
    (P₁ P₂ : α → ℝ) (alpha lam : ℝ) (Qstar : α → ℝ) : Prop where
  /-- `Qstar` is full support. -/
  pos : ∀ a, 0 < Qstar a
  /-- `Qstar` is a pmf. -/
  sum_one : ∑ a, Qstar a = 1
  /-- Constant log-ratio gradient stationarity: the log-likelihood combination
  is flat across the alphabet. -/
  log_ratio_const : ∀ a b : α,
    Real.log (Qstar a) - (1 - lam) * Real.log (P₁ a) - lam * Real.log (P₂ a)
      = Real.log (Qstar b) - (1 - lam) * Real.log (P₁ b) - lam * Real.log (P₂ b)

omit [DecidableEq α] in
/-- Gradient discharge for the tilt family: the closed-form tilt
`hoeffdingTilt P₁ P₂ lam` satisfies `IsKLGradientHyp` (no hypothesis on
`alpha`). -/
@[entry_point]
theorem isKLGradientHyp_tilt
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (alpha lam : ℝ) :
    IsKLGradientHyp P₁ P₂ alpha lam (hoeffdingTilt P₁ P₂ lam) where
  pos := hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam
  sum_one := hoeffdingTilt_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam
  log_ratio_const := hoeffdingTilt_log_ratio_eq P₁ P₂ hP₁_pos hP₂_pos lam

/-! ## Lagrange constraint-match sub-predicate -/

/-- Lagrange constraint-match sub-predicate: at parameter `lam`, the tilt
`hoeffdingTilt P₁ P₂ lam` lies in the constraint set `K(α)` and realises the
infimum `hoeffdingE2 P₁ P₂ alpha`.

The membership half is the constraint `klDivPmf (tilt) P₁ ≤ alpha`; the
realises half is the infimum-attainment. Existence of a `lam ∈ (0,1)` with
`klDivPmf (tilt) P₁ = alpha` is the implicit-function / monotonicity step
(`λ ↦ klDivPmf T_λ P₁` increasing from `0` at `λ=0` to `klDivPmf P₂ P₁` at
`λ=1`), kept as the single remaining analytic hypothesis.

`@audit:retract-candidate(load-bearing-predicate)` — the hypothesis-form
layer has no in-tree consumers. Producer-side constructors
(`isHoeffdingLagrangeHyp_of_minimal`,
`exists_isHoeffdingLagrangeHyp_of_minimal`,
`isHoeffdingLagrangeHyp_of_constraint_eq`,
`exists_isHoeffdingLagrangeHyp_interior`) remain constructive. -/
structure IsHoeffdingLagrangeHyp
    (P₁ P₂ : α → ℝ) (alpha lam : ℝ) : Prop where
  /-- The tilt at `lam` satisfies the Type-I constraint. -/
  mem : hoeffdingTilt P₁ P₂ lam ∈ hoeffdingConstraintSet P₁ alpha
  /-- The tilt at `lam` realises the infimum. -/
  realises : hoeffdingE2 P₁ P₂ alpha = klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂

/-! ## Full-support flag via Lagrange tilt -/

omit [DecidableEq α] in
/-- Tilt is full support: the closed-form tilt minimizer satisfies the
`IsHoeffdingMinimizerFullSupport` predicate. This is purely constructive
— `hoeffdingTilt_pos` discharges full support directly from `hP₁_pos` /
`hP₂_pos`, so no Lagrange hypothesis is needed. -/
@[entry_point]
theorem isHoeffdingMinimizerFullSupport_of_lagrange
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    IsHoeffdingMinimizerFullSupport (hoeffdingTilt P₁ P₂ lam) := by
  classical
  exact IsHoeffdingMinimizerFullSupport.of_pos
    (hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam)

end InformationTheory.Shannon.HoeffdingTilt
