import Common2026.Shannon.HoeffdingInteriorBody

/-!
# T1-D Hoeffding tradeoff — interior gradient body (L-H4-FS-grad / Lagrange tilt)

`HoeffdingInteriorBody.lean` (wave7) introduced two interface predicates for the
**interior** regime `0 < α < klDivPmf P₂ P₁`:

* `IsHoeffdingInteriorGradient P₁ P₂ alpha` — *every* Csiszar-Pythagoras
  minimizer of `klDivPmf · P₂` on `K(α)` has full support (the deferred
  log-singularity gradient argument).
* `IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar` — `Qstar` is full-support,
  lies in `K(α)`, and realises the infimum.

This file (wave9 W9-S11) discharges the **constructive** half of the interior
regime: the **Lagrangian / KKT stationarity** of the closed-form minimizer.
The textbook Csiszár I-projection of `P₂` onto `K(α)` is the one-parameter
exponential tilt

      `Qstar a = c(λ) · P₁ a ^ (1 - λ) · P₂ a ^ λ`,

which is *exactly* `Chernoff.chernoffMediator P₁ P₂ λ`. We reuse that family
(no new definition) and prove its defining gradient property:

      `log (Qstar a) - (1 - λ) · log (P₁ a) - λ · log (P₂ a)`  is **constant in a**
      (it equals `-log Z(λ)`).

This is the Lagrange first-order condition `∇[D(Q‖P₂) + μ D(Q‖P₁)] = const`
in disguise: the log-likelihood ratio of the tilt against the geometric mean of
`P₁, P₂` is flat across the alphabet. Unlike the `-∞`-singularity claim of
`IsHoeffdingInteriorGradient` (which remains the L-H4-FS retreat), the
constant-log-ratio identity is a *pure algebra* fact about `rpow` and is fully
discharged here.

## Strategy — gradient stationarity + Lagrange pass-through

Two sub-predicates decompose the interior characterization:

* **`IsKLGradientHyp P₁ P₂ alpha lam Qstar`** — *discharged internally* for the
  tilt `Qstar = chernoffMediator P₁ P₂ lam`: the constant-log-ratio
  stationarity above, plus full support and `Qstar ∈ stdSimplex`.

* **`IsHoeffdingLagrangeHyp P₁ P₂ alpha lam`** — *hypothesis pass-through*: the
  tilt at `lam` matches the constraint (`klDivPmf (tilt) P₁ ≤ alpha`) **and**
  realises the infimum (`hoeffdingE2 = klDivPmf (tilt) P₂`). The existence of a
  `lam ∈ (0,1)` solving `klDivPmf (tilt) P₁ = alpha` is the implicit-function
  step (monotonicity of `λ ↦ klDivPmf T_λ P₁`); this is the genuine remaining
  analytic content and is kept as a single named hypothesis.

The bridge `isHoeffdingInteriorMinimizer_of_lagrange` converts an
`IsHoeffdingLagrangeHyp` into the wave7 `IsHoeffdingInteriorMinimizer`, which in
turn plugs into the full sandwich pipeline via the wave7 bridges.

## What this file publishes

* **`hoeffdingTilt`** — the closed-form Lagrange minimizer (a `chernoffMediator`
  alias) with its positivity / pmf facts re-exported.

* **`hoeffdingTilt_log_ratio_const`** — the Lagrange gradient identity
  (constant log-ratio across the alphabet), **fully discharged**.

* **`IsKLGradientHyp`** — gradient sub-predicate, with constructor
  `isKLGradientHyp_tilt` discharging it for the tilt family.

* **`IsHoeffdingLagrangeHyp`** — Lagrange constraint-match sub-predicate.

* **`isHoeffdingInteriorMinimizer_of_lagrange`** — bridge into the wave7
  interior minimizer predicate.

* **`hoeffdingE2_interior_minimizer_via_lagrange`** — interior infimum reached
  at the full-support tilt witness, re-published through the wave7 chain.

## Retreat lines (L-H4-FS)

The `-∞`-singularity proof of `IsHoeffdingInteriorGradient` (full support of an
*arbitrary* minimizer) remains deferred. What is *added* here is the
constructive stationarity of the explicit tilt minimizer, which is the other
half of the Csiszár characterization and is discharged from `rpow` algebra.
-/

namespace InformationTheory.Shannon.HoeffdingInteriorGradientBody

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingSandwich
open InformationTheory.Shannon.HoeffdingSandwichBody
open InformationTheory.Shannon.HoeffdingInteriorBody
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase 1 — Closed-form Lagrange minimizer (`chernoffMediator` alias) -/

/-- **Closed-form Lagrange / KKT minimizer** of `klDivPmf · P₂` on `K(α)`:
the exponential tilt `Qstar a = P₁ a ^ (1-λ) · P₂ a ^ λ / Z(λ)`.

This is definitionally `Chernoff.chernoffMediator P₁ P₂ lam`; we expose it under
the Hoeffding name so the interior characterization reads in terms of the
tradeoff problem rather than the Chernoff bound. -/
noncomputable def hoeffdingTilt (P₁ P₂ : α → ℝ) (lam : ℝ) : α → ℝ :=
  chernoffMediator P₁ P₂ lam

lemma hoeffdingTilt_eq_chernoffMediator (P₁ P₂ : α → ℝ) (lam : ℝ) :
    hoeffdingTilt P₁ P₂ lam = chernoffMediator P₁ P₂ lam := rfl

/-- The tilt is positive under full support. -/
lemma hoeffdingTilt_pos
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    0 < hoeffdingTilt P₁ P₂ lam a :=
  chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a

/-- The tilt sums to `1`. -/
lemma hoeffdingTilt_sum_eq_one
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    (∑ a, hoeffdingTilt P₁ P₂ lam a) = 1 :=
  chernoffMediator_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam

/-- The tilt lies in the simplex. -/
lemma hoeffdingTilt_mem_stdSimplex
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    hoeffdingTilt P₁ P₂ lam ∈ stdSimplex ℝ α :=
  ⟨fun a => (hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam a).le,
   hoeffdingTilt_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam⟩

/-! ## Phase 2 — Lagrange gradient identity (constant log-ratio) -/

/-- **Lagrange gradient stationarity (constant log-ratio)**: for the tilt
`Qstar = hoeffdingTilt P₁ P₂ lam`, the log-likelihood combination

    `log (Qstar a) - (1 - lam) · log (P₁ a) - lam · log (P₂ a)`

is **constant in `a`** (it equals `-log Z(λ)`). This is the Csiszár Lagrange
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

/-- **Pairwise flatness**: a corollary stating that the log-ratio combination
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

/-! ## Phase 3 — Gradient sub-predicate (`IsKLGradientHyp`) -/

/-- **KL gradient sub-predicate**: bundles the constant-log-ratio gradient
stationarity at parameter `lam` together with full support and simplex
membership of `Qstar`.

The `alpha` argument is kept for interface symmetry with the wave7 predicates
(the gradient condition itself does not depend on `alpha`). -/
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

/-- **Gradient discharge for the tilt family**: the closed-form tilt
`hoeffdingTilt P₁ P₂ lam` satisfies `IsKLGradientHyp`. This is the internal
discharge of the gradient sub-predicate (no hypothesis on `alpha`). -/
theorem isKLGradientHyp_tilt
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (alpha lam : ℝ) :
    IsKLGradientHyp P₁ P₂ alpha lam (hoeffdingTilt P₁ P₂ lam) where
  pos := hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam
  sum_one := hoeffdingTilt_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam
  log_ratio_const := hoeffdingTilt_log_ratio_eq P₁ P₂ hP₁_pos hP₂_pos lam

/-! ## Phase 4 — Lagrange constraint-match sub-predicate -/

/-- **Lagrange constraint-match sub-predicate**: at parameter `lam`, the tilt
`hoeffdingTilt P₁ P₂ lam` lies in the constraint set `K(α)` and realises the
infimum `hoeffdingE2 P₁ P₂ alpha`.

The membership half is the constraint `klDivPmf (tilt) P₁ ≤ alpha`; the
realises half is the infimum-attainment. Existence of a `lam ∈ (0,1)` with
`klDivPmf (tilt) P₁ = alpha` is the implicit-function / monotonicity step
(`λ ↦ klDivPmf T_λ P₁` increasing from `0` at `λ=0` to `klDivPmf P₂ P₁` at
`λ=1`), kept as the single remaining analytic hypothesis.

`@audit:retract-candidate(load-bearing-predicate)` — all in-tree
hypothesis-consumers were retreated in `hoeffding-sorry-migration-plan`
Phase 2. Producer-side constructors (`isHoeffdingLagrangeHyp_of_minimal`,
`exists_isHoeffdingLagrangeHyp_of_minimal`,
`isHoeffdingLagrangeHyp_of_constraint_eq`,
`exists_isHoeffdingLagrangeHyp_interior`) are unchanged and remain
constructive. The retract-candidate status reflects that the
hypothesis-form layer is empty post-Phase 2. -/
structure IsHoeffdingLagrangeHyp
    (P₁ P₂ : α → ℝ) (alpha lam : ℝ) : Prop where
  /-- The tilt at `lam` satisfies the Type-I constraint. -/
  mem : hoeffdingTilt P₁ P₂ lam ∈ hoeffdingConstraintSet P₁ alpha
  /-- The tilt at `lam` realises the infimum. -/
  realises : hoeffdingE2 P₁ P₂ alpha = klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂

/-! ## Phase 5 — Bridge: Lagrange hypothesis ⇒ interior minimizer -/

/-- **Bridge (Lagrange ⇒ interior minimizer) — textbook L-H4-FS interior**: the
tilt at parameter `lam` is the wave7 `IsHoeffdingInteriorMinimizer`.

`@residual(plan:hoeffding-tradeoff-moonshot-plan)` — the previously bundled
`IsHoeffdingLagrangeHyp` hypothesis is retreated; the IVT constraint-match and
infimum-attainment discharges are deferred to
`hoeffding-tradeoff-moonshot-plan` Phase B. Full support is constructive
(`hoeffdingTilt_pos`) and lives in `IsHoeffdingMinimizerFullSupport.of_pos`
elsewhere. -/
theorem isHoeffdingInteriorMinimizer_of_lagrange
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {alpha lam : ℝ} :
    IsHoeffdingInteriorMinimizer P₁ P₂ alpha (hoeffdingTilt P₁ P₂ lam) := by
  sorry

/-- **Existence form** (textbook L-H4-FS interior): there exists an interior
minimizer (the tilt witness).

Transitive `sorry` via `isHoeffdingInteriorMinimizer_of_lagrange`. No
`@residual` tag is attached — the closure responsibility belongs to the
upstream declaration. The existential introduction (`⟨hoeffdingTilt ..., ...⟩`)
is itself constructive. -/
theorem isHoeffdingInteriorMinimizer_exists_of_lagrange
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {alpha lam : ℝ} :
    ∃ Qstar, IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar :=
  ⟨hoeffdingTilt P₁ P₂ lam,
   isHoeffdingInteriorMinimizer_of_lagrange P₁ P₂ hP₁_pos hP₂_pos⟩

/-! ## Phase 6 — Full-support flag via Lagrange tilt -/

/-- **Tilt is full support**: the closed-form tilt minimizer satisfies the
wave6 `IsHoeffdingMinimizerFullSupport` predicate. This is purely constructive
— `hoeffdingTilt_pos` discharges full support directly from `hP₁_pos` /
`hP₂_pos`, so no Lagrange hypothesis is needed. The Phase 2 retreat of the
predicate-form `IsHoeffdingLagrangeHyp` does not touch this lemma. -/
theorem isHoeffdingMinimizerFullSupport_of_lagrange
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    IsHoeffdingMinimizerFullSupport (hoeffdingTilt P₁ P₂ lam) :=
  IsHoeffdingMinimizerFullSupport.of_pos
    (hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam)

/-! ## Phase 7 — Interior infimum reached at the Lagrange tilt -/

/-- **Interior infimum at the Lagrange tilt** (textbook L-H4-FS interior): the
infimum `hoeffdingE2 P₁ P₂ alpha` is realised at the full-support tilt witness
lying in `K(α)`.

`@residual(plan:hoeffding-tradeoff-moonshot-plan)` — the IVT constraint-match
+ infimum-attainment content was previously bundled as
`IsHoeffdingLagrangeHyp` and is now retreated. -/
theorem hoeffdingE2_interior_minimizer_via_lagrange
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {alpha lam : ℝ} :
    ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha,
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ ∧
      IsHoeffdingMinimizerFullSupport Qstar := by
  sorry

/-! ## Phase 8 — Pythagoras at the Lagrange tilt -/

/-- **Pythagoras at the Lagrange tilt** (textbook L-H4-FS interior): at the
tilt minimizer, the Pythagorean inequality holds against any other
full-support `P ∈ K(α)`.

`@residual(plan:hoeffding-tradeoff-moonshot-plan)` — depends on the retreated
`isHoeffdingInteriorMinimizer_of_lagrange` (the tilt-realises-infimum step). -/
theorem csiszar_pythagoras_at_lagrange
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha lam : ℝ}
    {P : α → ℝ}
    (hP_mem : P ∈ hoeffdingConstraintSet P₁ alpha)
    (hP_pos : ∀ a, 0 < P a) :
    klDivPmf P P₂ ≥ klDivPmf P (hoeffdingTilt P₁ P₂ lam)
      + klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ := by
  sorry

/-! ## Phase 9 — Sandwich at the Lagrange tilt -/

/-- **Sandwich at the Lagrange tilt** (textbook L-H4-FS interior): given the
two variational hypotheses, the optimal Type II rate converges to
`hoeffdingE2 P₁ P₂ alpha`.

`@residual(plan:hoeffding-tradeoff-moonshot-plan)` — the previously bundled
`IsHoeffdingLagrangeHyp` is retreated. The two variational hypotheses remain
inputs (Phase C / Phase D deferred). -/
theorem hoeffding_tradeoff_sandwich_at_lagrange
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < 1)
    (h_liminf : (hoeffdingE2 P₁ P₂ alpha) ≤
      Filter.liminf
        (fun n : ℕ =>
          -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
        atTop)
    (h_limsup : Filter.limsup
        (fun n : ℕ =>
          -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
        atTop ≤ (hoeffdingE2 P₁ P₂ alpha)) :
    Tendsto (fun n : ℕ =>
        -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha)) := by
  sorry

end InformationTheory.Shannon.HoeffdingInteriorGradientBody
