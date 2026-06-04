/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Conditional Kullback-Leibler divergence, integral form

This file fills the explicit Mathlib `TODO` of
`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`:

> Add a version of the chain rule for the integral form of the conditional KL divergence, i.e.
> `μ[fun x ↦ klDiv (κ x) (η x)]`.

The main theorem `klDiv_compProd_toReal_integral` states that, when the two joint measures
`μ ⊗ₘ κ` and `μ ⊗ₘ η` share the *same first marginal* `μ`, the `toReal` Kullback-Leibler
divergence between them equals the `μ`-average of the fibrewise divergences:

`(klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ z, (klDiv (κ z) (η z)).toReal ∂μ`.

The Mathlib chain rule `klDiv_compProd_eq_add` keeps the conditional KL term in the
composition-product form `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` precisely to avoid the measurability of
`z ↦ klDiv (κ z) (η z)`. Here we resolve that measurability and the integral identity.

## Main statements

* `rnDeriv_compProd_eq_kernel_rnDeriv`: the slice identity
  `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η) (z, y) =ᵐ Kernel.rnDeriv κ η z y`.
* `klDiv_compProd_toReal_integral`: the conditional KL integral form.

## Proof strategy

The slice identity is the linchpin. We use `Measure.compProd_withDensity`
(`μ ⊗ₘ (η.withDensity f) = (μ ⊗ₘ η).withDensity (fun p ↦ f p.1 p.2)`) together with the
kernel Radon-Nikodym facts `Kernel.withDensity_rnDeriv_eq` (`η.withDensity (κ.rnDeriv η) a = κ a`
when `κ a ≪ η a`) and `Measure.absolutelyContinuous_compProd_right_iff` (`μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔
∀ᵐ a ∂μ, κ a ≪ η a`) to rewrite `μ ⊗ₘ κ` as `(μ ⊗ₘ η).withDensity (fun p ↦ Kernel.rnDeriv κ η p.1 p.2)`,
whence `Measure.rnDeriv_withDensity` reads off the joint Radon-Nikodym derivative.

For the integral, `toReal_klDiv_eq_integral_klFun` expresses both sides through `klFun` integrated
against the dominating measure (`μ ⊗ₘ η` on the left, `η z` per fibre), and `Measure.integral_compProd`
opens the joint `klFun` integral into the outer `μ`-integral.
-/

open Real MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}

section SliceRnDeriv

variable [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
  [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]

/-- **Slice identity for the Radon-Nikodym derivative of a composition product.**
When the two joint measures share the first marginal `μ`, the joint Radon-Nikodym derivative
agrees almost everywhere with the pointwise kernel Radon-Nikodym derivative. This is the
statement the `RadonNikodym.lean` `TODO` left open. -/
theorem rnDeriv_compProd_eq_kernel_rnDeriv (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ Kernel.rnDeriv κ η p.1 p.2 := by
  -- a.e. fibrewise absolute continuity from the joint absolute continuity
  have h_fib : ∀ᵐ a ∂μ, κ a ≪ η a :=
    Measure.absolutelyContinuous_compProd_right_iff.mp h_ac
  -- `η.withDensity (Kernel.rnDeriv κ η)` agrees with `κ` `μ`-a.e.
  have h_wd : η.withDensity (Kernel.rnDeriv κ η) =ᵐ[μ] κ := by
    filter_upwards [h_fib] with a ha
    exact Kernel.withDensity_rnDeriv_eq ha
  -- rewrite the numerator measure as a `withDensity` of the denominator measure
  have h_meas : Measurable (Function.uncurry (Kernel.rnDeriv κ η)) :=
    Kernel.measurable_rnDeriv κ η
  have h_eq : μ ⊗ₘ κ
      = (μ ⊗ₘ η).withDensity (fun p ↦ Kernel.rnDeriv κ η p.1 p.2) := by
    rw [← Measure.compProd_withDensity h_meas, Measure.compProd_congr h_wd]
  -- read off the Radon-Nikodym derivative of a `withDensity`
  calc (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)
      =ᵐ[μ ⊗ₘ η] ((μ ⊗ₘ η).withDensity
          (fun p ↦ Kernel.rnDeriv κ η p.1 p.2)).rnDeriv (μ ⊗ₘ η) := by rw [h_eq]
    _ =ᵐ[μ ⊗ₘ η] fun p ↦ Kernel.rnDeriv κ η p.1 p.2 :=
        Measure.rnDeriv_withDensity (μ ⊗ₘ η) (by fun_prop)

end SliceRnDeriv

section Integral

variable [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
  [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]

/-- **Conditional Kullback-Leibler divergence, integral form** (Mathlib `ChainRule.lean` `TODO`).
When the two joint measures `μ ⊗ₘ κ` and `μ ⊗ₘ η` share the first marginal `μ`, the `toReal`
Kullback-Leibler divergence decomposes as the `μ`-average of the fibrewise divergences. -/
theorem klDiv_compProd_toReal_integral
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ)) :
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ z, (klDiv (κ z) (η z)).toReal ∂μ := by
  -- a.e. fibrewise absolute continuity
  have h_fib : ∀ᵐ a ∂μ, κ a ≪ η a :=
    Measure.absolutelyContinuous_compProd_right_iff.mp h_ac
  -- integrand of the joint `klFun` integral, rewritten through the slice identity
  set F : 𝓧 × 𝓨 → ℝ := fun p ↦ klFun (Kernel.rnDeriv κ η p.1 p.2).toReal with hF
  have h_slice := rnDeriv_compProd_eq_kernel_rnDeriv (μ := μ) (κ := κ) (η := η) h_ac
  have h_klfun_eq : (fun p ↦ klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) =ᵐ[μ ⊗ₘ η] F := by
    filter_upwards [h_slice] with p hp
    rw [hF]; rw [hp]
  -- integrability of `F` against `μ ⊗ₘ η`
  have h_int_F : Integrable F (μ ⊗ₘ η) := by
    refine (integrable_congr h_klfun_eq).mp ?_
    exact (integrable_klFun_rnDeriv_iff h_ac).mpr h_int
  -- LHS expressed through `klFun`, then opened with Fubini
  calc (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal
      = ∫ p, klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ η) :=
        toReal_klDiv_eq_integral_klFun h_ac
    _ = ∫ p, F p ∂(μ ⊗ₘ η) := integral_congr_ae h_klfun_eq
    _ = ∫ z, ∫ y, klFun (Kernel.rnDeriv κ η z y).toReal ∂(η z) ∂μ :=
        Measure.integral_compProd h_int_F
    _ = ∫ z, (klDiv (κ z) (η z)).toReal ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h_fib] with z hz
        rw [toReal_klDiv_eq_integral_klFun hz]
        refine integral_congr_ae ?_
        filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := z)] with y hy
        rw [hy]

/-- **Conditional KL divergence, integral form against a constant kernel.**
Specialization of `klDiv_compProd_toReal_integral` to `η := Kernel.const 𝓧 ν`, the form used by
the EPI G2 conditional differential-entropy bridge. -/
theorem klDiv_compProd_const_toReal_integral {ν : Measure 𝓨} [IsProbabilityMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ (Kernel.const 𝓧 ν))
    (h_int : Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ (Kernel.const 𝓧 ν))) (μ ⊗ₘ κ)) :
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (Kernel.const 𝓧 ν))).toReal = ∫ z, (klDiv (κ z) ν).toReal ∂μ := by
  rw [klDiv_compProd_toReal_integral h_ac h_int]
  simp only [Kernel.const_apply]

end Integral

end InformationTheory
