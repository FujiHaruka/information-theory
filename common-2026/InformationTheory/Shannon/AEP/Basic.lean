import InformationTheory.Shannon.AEP.Basic.Core
import InformationTheory.Shannon.AEP.Basic.Converse
import InformationTheory.Shannon.AEP.Basic.Achievability

/-!
# AEP — Asymptotic Equipartition Property

Formalization of the asymptotic equipartition property, Cover-Thomas Theorem
3.1.1–3.1.2. This module re-exports the AEP core, the source-coding converse, and
the achievability development from the `AEP.Basic.*` submodules.

## Main definitions

* `jointRV` — the block random variable `Ω → (Fin n → α)` built from an i.i.d.
  sequence `Xs : ℕ → Ω → α`.
* `typicalSet` — the typical set `T_ε^n`.

## Main statements

* `aep_ae` / `aep_inProbability` — the empirical entropy estimator
  `(1/n) ∑ i, (-Real.log ((μ.map (Xs 0)).real {Xs i ω}))` converges to
  `entropy μ (Xs 0)` almost surely and in probability.
* `typicalSet_card_le` / `typicalSet_prob_tendsto_one` — size bound and
  asymptotic probability of the typical set.

## Implementation notes

Mathlib has no `IsIID` predicate, so the i.i.d. hypothesis is taken in the same
two-part form as `strong_law_ae_real`:
`Pairwise (fun i j => Xs i ⟂ᵢ[μ] Xs j)` and `∀ i, IdentDistrib (Xs i) (Xs 0) μ μ`.
The `(· ⟂ᵢ[μ] ·) on Xs` anonymous-lambda form fails to parse when combined with
`on`, so the explicit `fun i j => …` form is used.
-/

