import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Measurable selection of a log-optimal portfolio (Cover–Thomas §16.5)

Gateway lemma for the stationary-market `W_∞` AEP (Theorem 16.5.1): a Carathéodory
objective (measurable in the sample point, continuous in the portfolio) admits a
measurable selection of an argmax over the standard simplex. This is the classical
"measurable maximum theorem". Mathlib has no ready measurable-selection lemma (see
`Mathlib/Probability/Decision/BayesEstimator.lean`, which notes selection theorems
are not yet in Mathlib), so the selector is self-built from the compact-argmax
existence lemma `IsCompact.exists_isMaxOn` plus the Borel-measurability toolkit.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  §16.5.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter Topology
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {m : ℕ}

/-- Measurable selection of an argmax of a Carathéodory function over the standard simplex.
For `F` measurable in `ω` (for each fixed portfolio `b`) and continuous in `b` on the simplex,
there is a measurable `bstar : Ω → (Fin m → ℝ)` picking, for each `ω`, a point of the simplex
that maximizes `F ω` over the simplex.

@residual(plan:portfolio-stationary-woo-plan) -/
theorem exists_measurable_argmax_on_stdSimplex
    (F : Ω → (Fin m → ℝ) → ℝ)
    (hF_meas : ∀ b : Fin m → ℝ, Measurable (fun ω ↦ F ω b))
    (hF_cont : ∀ ω, ContinuousOn (F ω) (stdSimplex ℝ (Fin m))) :
    ∃ bstar : Ω → (Fin m → ℝ), Measurable bstar ∧
      (∀ ω, bstar ω ∈ stdSimplex ℝ (Fin m)) ∧
      (∀ ω, IsMaxOn (F ω) (stdSimplex ℝ (Fin m)) (bstar ω)) := by
  sorry

end InformationTheory.Shannon.Portfolio
