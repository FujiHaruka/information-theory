import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Conditional
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.CondMutualInfo

/-!
# Sufficient statistics and mutual information (Cover-Thomas 2.9)

If `T` is sufficient for `θ` (i.e., the chain `X → T(X) → θ` is Markov), then
`I(θ; X) = I(θ; T(X))`.

## Main definitions

* `IsSufficientStatistic` — sufficient statistic in markov-chain form:
  the chain `Xs → f∘Xs → θ` is a Markov chain, i.e., `Xs ⊥ θ ∣ f(Xs)`.
* `IsSufficientStatisticFactorized` — Neyman-Fisher factorization form:
  the conditional distribution of `Xs` given `(f(Xs), θ)` does not depend on `θ`.

## Main statements

* `mutualInfo_eq_of_sufficient` — Cover-Thomas 2.9: sufficiency implies `I(θ; X) = I(θ; T(X))`.
* `isSufficient_iff_factorized` — equivalence of the two forms of sufficiency.

## Implementation notes

`IsSufficientStatistic` is defined in markov-chain form (matching the conclusion of
`mutualInfo_le_of_markov`) rather than the Neyman-Fisher factorization form. This makes
the main theorem close directly via `mutualInfo_le_of_postprocess` (the ≥ direction) and
`mutualInfo_le_of_markov` + `mutualInfo_comm` (the ≤ direction) by `le_antisymm`.

Equivalence with the Neyman-Fisher form is proved via Mathlib's conditional independence API.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Θ : Type*} [MeasurableSpace Θ]
variable {X : Type*} [MeasurableSpace X]
variable {T' : Type*} [MeasurableSpace T']

/-- Sufficient statistic in markov-chain form: the chain `Xs → f∘Xs → θ` is a Markov chain,
i.e., the statistic `T(X) = f(X)` separates `Xs` and `θ` (conditional independence `Xs ⊥ θ ∣ T(X)`).

Equivalence with the Neyman-Fisher factorization form is proved in `isSufficient_iff_factorized`.
@audit:ok -/
def IsSufficientStatistic
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  IsMarkovChain μ Xs (fun ω => f (Xs ω)) θ

/-- Cover-Thomas 2.9: if `T` is sufficient for `θ`, then `I(θ; X) = I(θ; T(X))`.

`IsSufficientStatistic` is a structural precondition (the Markov chain property), not the
conclusion itself. The proof is `le_antisymm` with the two directions from DPI.
@audit:ok -/
@[entry_point]
theorem mutualInfo_eq_of_sufficient
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f)
    (hsuff : IsSufficientStatistic μ θ Xs f) :
    mutualInfo μ θ Xs = mutualInfo μ θ (fun ω => f (Xs ω)) := by
  have hfXs : Measurable (fun ω => f (Xs ω)) := hf.comp hXs
  -- (≥) T(X) = f∘Xs is a deterministic post-processing of Xs.
  have h_ge : mutualInfo μ θ (fun ω => f (Xs ω)) ≤ mutualInfo μ θ Xs :=
    mutualInfo_le_of_postprocess μ θ Xs hθ hXs hf
  -- (≤) DPI from the Markov chain `Xs → f∘Xs → θ`, then flip both sides via `mutualInfo_comm`.
  have h_markov : mutualInfo μ Xs θ ≤ mutualInfo μ (fun ω => f (Xs ω)) θ :=
    mutualInfo_le_of_markov μ Xs (fun ω => f (Xs ω)) θ hXs hfXs hθ hsuff
  have h_le : mutualInfo μ θ Xs ≤ mutualInfo μ θ (fun ω => f (Xs ω)) := by
    rw [mutualInfo_comm μ θ Xs hθ hXs, mutualInfo_comm μ θ (fun ω => f (Xs ω)) hθ hfXs]
    exact h_markov
  exact le_antisymm h_le h_ge

/-! ## Equivalence with the Neyman-Fisher factorization form -/

/-- Sufficient statistic in Neyman-Fisher factorization form: the conditional distribution of
`Xs` given `(f(Xs), θ)` does not depend on `θ`.

Concretely: `condDistrib Xs (T(X), θ) =ᵃᵉ (condDistrib Xs T(X)).prodMkRight Θ`.
This is the measure-theoretic encoding of `p(x ∣ θ) = g(T(x), θ) h(x)`.
@audit:ok -/
def IsSufficientStatisticFactorized
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  condDistrib Xs (fun ω => (f (Xs ω), θ ω)) μ
    =ᵐ[μ.map (fun ω => (f (Xs ω), θ ω))]
      (condDistrib Xs (fun ω => f (Xs ω)) μ).prodMkRight Θ

/-- The markov-form and the Neyman-Fisher factorization form of sufficiency are equivalent:
both express `X ⊥ θ ∣ T(X)`.

Proof via Mathlib's conditional independence API:
- (A) `IsSufficientStatistic` (γ-form joint factorization) ↔ `Xs ⟂ᵢ[f∘Xs] θ`
  via `condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib` + `compProd_eq_comp_prod`.
- (B) `Xs ⟂ᵢ[f∘Xs] θ` ↔ `θ ⟂ᵢ[f∘Xs] Xs` via `CondIndepFun.symm`.
- (C) `θ ⟂ᵢ[f∘Xs] Xs` ↔ factorization form via `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`.
@audit:ok -/
@[entry_point]
theorem isSufficient_iff_factorized
    (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f) :
    IsSufficientStatistic μ θ Xs f ↔ IsSufficientStatisticFactorized μ θ Xs f := by
  have hfXs : Measurable (fun ω => f (Xs ω)) := hf.comp hXs
  -- (A) markov γ-form ↔ condIndepFun `Xs ⟂ᵢ[f∘Xs] θ`
  have hA : IsSufficientStatistic μ θ Xs f
      ↔ Xs ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] θ := by
    unfold IsSufficientStatistic IsMarkovChain
    rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hXs hθ hfXs,
        Measure.compProd_eq_comp_prod]
  -- (B) symmetry of condIndepFun
  have hB : (Xs ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] θ)
      ↔ (θ ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] Xs) :=
    ⟨CondIndepFun.symm, CondIndepFun.symm⟩
  -- (C) `θ ⟂ᵢ[f∘Xs] Xs` ↔ factorization form
  have hC : (θ ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] Xs)
      ↔ IsSufficientStatisticFactorized μ θ Xs f := by
    unfold IsSufficientStatisticFactorized
    rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hXs hθ hfXs]
  exact hA.trans (hB.trans hC)

end InformationTheory.Shannon
