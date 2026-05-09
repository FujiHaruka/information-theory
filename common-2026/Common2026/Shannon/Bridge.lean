import Common2026.Shannon.MutualInfo
import Common2026.Fano.Measure
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Bridge: mutualInfo (KL form) ↔ Phase 3 condEntropy (Phase 4-β skeleton)

Shannon ムーンショット ([`docs/shannon-moonshot-plan.md`](../../../docs/shannon-moonshot-plan.md)) の
Phase 4-β: Phase 4-α `mutualInfo` (KL 値) と Phase 3 `condEntropy` (∫ Σ negMulLog) を、
`X : Fintype` + `IsProbabilityMeasure μ` のもとで `H(X) - H(X|Y)` で結ぶ。

## 主定理

```
(mutualInfo μ Xs Yo).toReal = entropy μ Xs - condEntropy μ Xs Yo
```

## 戦略

1. `(μ.map (Xs, Yo)) ≪ (μ.map Xs).prod (μ.map Yo)` を示す (X Fintype + 確率測度)
2. `toReal_klDiv_eq_integral_klFun` で KL を Real の積分形に翻訳
3. Fintype 上の有限和に分解し `log(P(x|y) / P(x))` の点和に整理
4. 線形性で `H(X) - H(X|Y)` の差に分離
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]

/-- Shannon entropy of a discrete random variable taking values in a finite alphabet. -/
noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ :=
  ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})

omit [DecidableEq X] [Nonempty X] in
/-- Phase 4-α `mutualInfo` is finite when `X` is a finite alphabet and `μ` a probability
measure: the joint distribution is absolutely continuous w.r.t. the product of the
marginals (always true on a discrete `X` factor). Used to legally `toReal` the KL value. -/
private theorem absolutelyContinuous_joint_prod_marginals
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (μ.map (fun ω => (Xs ω, Yo ω))) ≪ (μ.map Xs).prod (μ.map Yo) := by
  have hpair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have _ : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  have _ : IsProbabilityMeasure (μ.map Xs) :=
    Measure.isProbabilityMeasure_map hXs.aemeasurable
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  -- 1. 積測度 0 を Tonelli + Fintype 和に展開
  rw [Measure.prod_apply hA, lintegral_fintype] at hA0
  have hzero : ∀ x : X,
      (μ.map Yo) (Prod.mk x ⁻¹' A) * (μ.map Xs) {x} = 0 := by
    intro x
    have hsum := (Finset.sum_eq_zero_iff (s := (Finset.univ : Finset X))
        (f := fun x => (μ.map Yo) (Prod.mk x ⁻¹' A) * (μ.map Xs) {x})).mp hA0
    exact hsum x (Finset.mem_univ _)
  -- 2. 結合測度を Xs スライス上の有限 union として書き直し、各スライスが 0 を示す
  rw [Measure.map_apply hpair hA]
  have hslice : (fun ω => (Xs ω, Yo ω)) ⁻¹' A
      = ⋃ x : X, (Xs ⁻¹' {x}) ∩ (Yo ⁻¹' (Prod.mk x ⁻¹' A)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    refine ⟨fun h => ⟨Xs ω, rfl, h⟩, ?_⟩
    rintro ⟨x, hx, hY⟩
    rw [hx]; exact hY
  rw [hslice]
  refine measure_iUnion_null fun x => ?_
  have hAx : MeasurableSet (Prod.mk x ⁻¹' A) := measurable_prodMk_left hA
  rcases mul_eq_zero.mp (hzero x) with hY0 | hX0
  · -- (μ.map Yo)(slice) = 0 ⇒ μ(Yo ⁻¹' slice) = 0
    have : μ (Yo ⁻¹' (Prod.mk x ⁻¹' A)) = 0 := by
      rwa [← Measure.map_apply hYo hAx]
    exact measure_mono_null Set.inter_subset_right this
  · -- (μ.map Xs){x} = 0 ⇒ μ(Xs ⁻¹' {x}) = 0
    have : μ (Xs ⁻¹' {x}) = 0 := by
      rwa [← Measure.map_apply hXs (measurableSet_singleton x)]
    exact measure_mono_null Set.inter_subset_left this

/-! ### Helper lemmas for the bridge

The bridge proof goes via three independent helpers:

* `klDiv_compProd_const_eq_lintegral`: fiberwise expansion of conditional KL,
  `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ Kernel.const _ ν) = ∫⁻ x, klDiv (κ x) ν ∂μ`. The
  Mathlib chain rule (`klDiv_compProd_eq_add`) only gives the *non*-fiberwise
  form; we need the integral identity to land at `condEntropy`.

* `klDiv_discrete_toReal_eq_sum`: discrete `klDiv` on a finite alphabet
  expands as `∑ x, Q.real{x} * (log Q.real{x} - log P.real{x})`.

* `integral_condDistrib_real_singleton_eq`: marginal recovery,
  `∫ y, (condDistrib Xs Yo μ y).real {x} d(μ.map Yo) = (μ.map Xs).real {x}`.
-/

/-- Helper for `klDiv_compProd_const_eq_lintegral`: identifies the compProd
Radon-Nikodym derivative on its `b`-fiber with the kernel-side rnDeriv.

The Mathlib `Probability/Kernel/Composition/RadonNikodym.lean` file (line 26-29)
explicitly flags this as a TODO. The intended proof: for each measurable `B`
and `s`, show
```
∫⁻ a in s, ∫⁻ b in B, (μ⊗ₘκ).rnDeriv (μ⊗ₘη) (a,b) ∂(η a) ∂μ = ∫⁻ a in s, κ a B ∂μ
```
via `setLIntegral_compProd` + `setLIntegral_rnDeriv` + `compProd_apply_prod`,
then conclude by `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite` applied
fiber-wise (a.e. `a`).

**Status**: Phase 4-β core gap. Substantial plumbing (~80-120 行 estimate). -/
private lemma rnDeriv_compProd_ae_eq_kernel_rnDeriv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ]
    (κ η : Kernel α β) [IsSFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂η a,
      (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) = (κ a).rnDeriv (η a) b := by
  sorry

/-- Fiberwise KL chain rule: when both compProd's share the same `μ` on the
left, the full KL splits as the integral of fiberwise KLs.

Proof sketch (assuming the rnDeriv identification helper above):
1. Split on `∀ᵐ x ∂μ, κ x ≪ ν` (= ac of joint via `absolutelyContinuous_compProd_right_iff`)
2. AC case: `klDiv_eq_lintegral_klFun_of_ac` on both sides, Tonelli (`lintegral_compProd`)
   on LHS, then `lintegral_congr_ae` using `rnDeriv_compProd_ae_eq_kernel_rnDeriv`.
3. Non-AC case: both sides ⊤ (use `klDiv_of_not_ac` and
   `lintegral_eq_top_of_measure_eq_top_pos`-style argument). -/
private lemma klDiv_compProd_const_eq_lintegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ]
    (ν : Measure β) [IsFiniteMeasure ν] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ Kernel.const α ν)
      = ∫⁻ x, klDiv (κ x) ν ∂μ := by
  sorry

/-- Discrete `(klDiv Q P).toReal` formula on a finite alphabet under
absolute continuity.

Strategy: Use `klDiv_eq_lintegral_klFun_of_ac` + `lintegral_fintype` to express
both sides as `∑_x klFun(rnDeriv x).toReal · P.real{x}`, then identify
`(Q.rnDeriv P x) · P{x} = Q{x}` (from `setLIntegral_rnDeriv` + `lintegral_singleton`)
to rewrite each term as `Q.real{x} * (log Q.real{x} - log P.real{x})`. The
`klFun(t) = t·log t - t + 1` decomposition: the linear/constant parts integrate
to `-Q.real univ + P.real univ = -1 + 1 = 0` (both probability measures). -/
private lemma klDiv_discrete_toReal_eq_sum
    (Q P : Measure X) [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (hQP : Q ≪ P) :
    (klDiv Q P).toReal
      = ∑ x : X, Q.real {x} * (Real.log (Q.real {x}) - Real.log (P.real {x})) := by
  sorry

/-- Marginal recovery (lintegral form). -/
private lemma lintegral_condDistrib_singleton_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (x : X) :
    ∫⁻ y, (condDistrib Xs Yo μ y) {x} ∂(μ.map Yo)
      = (μ.map Xs) {x} := by
  have h_compProd : (μ.map Yo) ⊗ₘ (condDistrib Xs Yo μ)
      = μ.map (fun ω => (Yo ω, Xs ω)) := compProd_map_condDistrib hXs.aemeasurable
  have hpair : Measurable (fun ω => (Yo ω, Xs ω)) := hYo.prodMk hXs
  have hxs : MeasurableSet ({x} : Set X) := measurableSet_singleton x
  have h₁ : ((μ.map Yo) ⊗ₘ (condDistrib Xs Yo μ)) ((Set.univ : Set Y) ×ˢ ({x} : Set X))
      = ∫⁻ y in Set.univ, (condDistrib Xs Yo μ y) {x} ∂(μ.map Yo) :=
    Measure.compProd_apply_prod MeasurableSet.univ hxs
  rw [Measure.restrict_univ] at h₁
  rw [← h₁, h_compProd, Measure.map_apply hpair (MeasurableSet.univ.prod hxs),
      Measure.map_apply hXs hxs]
  congr 1
  ext ω
  simp

/-- Marginal recovery: integrating the conditional probability mass at `x` over
the `Y`-marginal returns the `X`-marginal mass at `x`. -/
private lemma integral_condDistrib_real_singleton_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (x : X) :
    ∫ y, (condDistrib Xs Yo μ y).real {x} ∂(μ.map Yo)
      = (μ.map Xs).real {x} := by
  have _ : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  -- Convert the ∫ (Bochner) into toReal of ∫⁻ via integral_toReal
  have h_ae_lt_top : ∀ᵐ y ∂(μ.map Yo), (condDistrib Xs Yo μ y) {x} < ∞ := by
    refine ae_of_all _ fun y => ?_
    exact (measure_lt_top _ _)
  have h_meas : AEMeasurable (fun y => (condDistrib Xs Yo μ y) {x}) (μ.map Yo) :=
    ((Kernel.measurable_coe _ (measurableSet_singleton x))).aemeasurable
  rw [show (fun y => ((condDistrib Xs Yo μ y).real ({x} : Set X)))
        = (fun y => ((condDistrib Xs Yo μ y) {x}).toReal) from rfl,
      integral_toReal h_meas h_ae_lt_top,
      lintegral_condDistrib_singleton_eq μ Xs Yo hXs hYo x]
  rfl

/-- Discrete-fiber expansion of the KL divergence appearing in `mutualInfo`.
For a finite alphabet `X` we may rewrite the joint integral as
`∑_{x : X} ∫_y …` and pull the discrete log decomposition through.

Plan to combine the three helpers:
1. `mutualInfo_comm` to swap to `(Yo, Xs)` form so the conditional that appears
   matches `condDistrib Xs Yo μ` (the `X|Y` direction used by `condEntropy`).
2. `compProd_map_condDistrib hXs.aemeasurable` rewrites
   `μ.map (Yo, Xs) = (μ.map Yo) ⊗ₘ condDistrib Xs Yo μ`.
3. `Measure.compProd_const` rewrites
   `(μ.map Yo).prod (μ.map Xs) = (μ.map Yo) ⊗ₘ Kernel.const Y (μ.map Xs)`.
4. `klDiv_compProd_const_eq_lintegral` (Helper 1) reduces to
   `∫⁻ y, klDiv (condDistrib Xs Yo μ y) (μ.map Xs) ∂(μ.map Yo)`.
5. Take `.toReal`, swap with `∫` via `integral_toReal` (need ae finite + integrable):
   `= ∫ y, (klDiv (condDistrib Xs Yo μ y) (μ.map Xs)).toReal d(μ.map Yo)`.
6. For each `y`, `klDiv_discrete_toReal_eq_sum` (Helper 5) expands the inner KL:
   `= ∑ x, Q_y.real{x} * (log Q_y.real{x} - log P_X.real{x})`
   `= -∑ x, negMulLog Q_y.real{x} - ∑ x, Q_y.real{x} * log P_X.real{x}`.
7. Integrate over `y`:
   - First sum integrates to `condEntropy μ Xs Yo` (definitionally).
   - Second sum: pull out `log P_X.real{x}`, get `∑ x, [∫ y, Q_y.real{x} dP_Y] * log P_X.real{x}`,
     apply `integral_condDistrib_real_singleton_eq` (Helper 3) to get
     `∑ x, P_X.real{x} * log P_X.real{x} = -∑ x, negMulLog P_X.real{x} = -entropy μ Xs`.
8. Combine: `mutualInfo.toReal = -condEntropy + entropy = entropy - condEntropy`. -/
private theorem klDiv_joint_prod_marginals_toReal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (klDiv (μ.map (fun ω => (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))).toReal
      = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo := by
  sorry

/-- The MI / condEntropy bridge: for a finite-alphabet source `X`, the Phase 4-α
KL-based mutual information equals `H(X) - H(X | Y)` where `H` is the Phase 3
measure-theoretic Shannon entropy / conditional entropy. -/
theorem mutualInfo_eq_entropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (mutualInfo μ Xs Yo).toReal
      = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo := by
  unfold mutualInfo
  exact klDiv_joint_prod_marginals_toReal μ Xs Yo hXs hYo

end InformationTheory.Shannon
