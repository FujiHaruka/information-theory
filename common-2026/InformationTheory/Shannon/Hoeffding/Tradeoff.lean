import InformationTheory.Shannon.Chernoff.Basic
import InformationTheory.Shannon.CsiszarProjection
import InformationTheory.Shannon.KLDivContinuous
import InformationTheory.Shannon.Sanov.LDPEquality
import InformationTheory.Asymptotic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Order.Compact

/-!
# Hoeffding tradeoff exponent — scaffolding and variational form

Scaffolding towards Cover-Thomas Theorem 11.7.x:

```
-(1/n) log β_n(alpha) → hoeffdingE2 P₁ P₂ alpha
```

`hoeffdingE2`, `hoeffdingE2_attained`, and `hoeffdingE2_unique` are published in
`InformationTheory/Shannon/Chernoff.lean`. This file adds the pmf-form infrastructure
and the Pythagoras-based minimizer bound.

## Main definitions

* `pmfToMeasure` — lift a pmf vector to `Measure α` via `PMF.ofFintype`.
* `steinBetaSet_pmf` — set of achievable Type II errors at Type I level `alpha` (pmf form).
* `steinTypeII_at_level_pmf` — optimal Type II error (pmf form).

## Main statements

* `hoeffdingConstraintSet_convex` — the Hoeffding constraint set is convex.
* `hoeffding_minimizer_ge` — Csiszar Pythagoras gives `klDivPmf Qstar P₂ ≤ klDivPmf P P₂`
  for any `P ∈ K` with full support, when `Qstar` is the minimizer.

## Implementation notes

* This file provides the variational scaffolding; the full sandwich `Tendsto`
  (achievability from Sanov LDP + converse from Stein typicality) is in
  `HoeffdingTradeoffExp.lean`.
* The pmf ↔ Measure bridge uses `PMF.ofFintype` + `PMF.toMeasure` (~4 lemmas).
-/

namespace InformationTheory.Shannon.HoeffdingTradeoff

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon
open scoped BigOperators Topology ENNReal

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## pmf ↔ Measure bridge (helper) -/

/-- Lift a pmf vector `P : α → ℝ` to `Measure α` via `PMF.ofFintype`. -/
noncomputable def pmfToMeasure (P : α → ℝ)
    (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) : Measure α :=
  (PMF.ofFintype (fun a => ENNReal.ofReal (P a)) (by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    rw [← hP_sum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => hP_nn a)])).toMeasure

instance pmfToMeasure_isProbabilityMeasure
    (P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) :
    IsProbabilityMeasure (pmfToMeasure P hP_nn hP_sum) := by
  unfold pmfToMeasure
  infer_instance

lemma pmfToMeasure_apply_singleton
    (P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) (a : α) :
    (pmfToMeasure P hP_nn hP_sum) {a} = ENNReal.ofReal (P a) := by
  unfold pmfToMeasure
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
  rfl

lemma pmfToMeasure_real_singleton
    (P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) (a : α) :
    (pmfToMeasure P hP_nn hP_sum).real {a} = P a := by
  unfold Measure.real
  rw [pmfToMeasure_apply_singleton P hP_nn hP_sum a]
  exact ENNReal.toReal_ofReal (hP_nn a)

/-! ## `steinTypeII_at_level_pmf` definition and basic properties -/

/-- n-IID Type II error set (pmf form).

`s : Finset (Fin n → α)` is the **acceptance region for H₀**. The Type I error is
`1 - ∑_{x ∈ s} ∏ P₁(x_i)` and the Type II error is `∑_{x ∈ s} ∏ P₂(x_i)`.
Convention matches `Stein.lean :: steinBetaSet` (Measure path) with `Finset`
instead of `Set + MeasurableSet`. -/
noncomputable def steinBetaSet_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : Set ℝ :=
  { β : ℝ | ∃ (s : Finset (Fin n → α)),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
      β = ∑ x ∈ s, ∏ i, P₂ (x i) }

/-- Optimal Type II error (pmf form). -/
noncomputable def steinTypeII_at_level_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : ℝ :=
  sInf (steinBetaSet_pmf P₁ P₂ n alpha)

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `∑_{x : Fin n → α} ∏ i, P (x i) = (∑ a, P a)^n` for pmf-like vectors. -/
lemma sum_prod_pi_eq_pow_sum (P : α → ℝ) (n : ℕ) :
    ∑ x : Fin n → α, ∏ i, P (x i) = (∑ a, P a) ^ n := by
  classical
  -- `Finset.sum_pow' : (∑ a ∈ s, f a) ^ n = ∑ p ∈ piFinset (fun _ : Fin n => s), ∏ i, f (p i)`.
  have h := Finset.sum_pow' (s := (Finset.univ : Finset α)) (f := P) n
  rw [h]
  -- piFinset (fun _ => Finset.univ) = Finset.univ : Finset (Fin n → α)
  rw [show (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset α)))
        = (Finset.univ : Finset (Fin n → α)) from Fintype.piFinset_univ]

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `1 ∈ steinBetaSet_pmf` (take `s := univ`). -/
lemma one_mem_steinBetaSet_pmf
    (P₁ P₂ : α → ℝ) (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (n : ℕ) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    (1 : ℝ) ∈ steinBetaSet_pmf P₁ P₂ n alpha := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · -- 1 - ∑_{x ∈ univ} ∏ P₁(x_i) = 1 - 1 = 0 ≤ alpha.
    have h_sum_full : ∑ x ∈ (Finset.univ : Finset (Fin n → α)), ∏ i, P₁ (x i) = 1 := by
      rw [show (Finset.univ : Finset (Fin n → α)) = Finset.univ from rfl]
      have h := sum_prod_pi_eq_pow_sum (α := α) P₁ n
      rw [h, hP₁_sum, one_pow]
    rw [h_sum_full]
    linarith
  · -- ∑_{x ∈ univ} ∏ P₂(x_i) = 1.
    have h_sum_full : ∑ x ∈ (Finset.univ : Finset (Fin n → α)), ∏ i, P₂ (x i) = 1 := by
      have h := sum_prod_pi_eq_pow_sum (α := α) P₂ n
      rw [h, hP₂_sum, one_pow]
    rw [h_sum_full]

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `steinTypeII_at_level_pmf P₁ P₂ n alpha ≥ 0`. -/
lemma steinTypeII_at_level_pmf_nonneg
    (P₁ P₂ : α → ℝ) (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    0 ≤ steinTypeII_at_level_pmf P₁ P₂ n alpha := by
  unfold steinTypeII_at_level_pmf
  refine le_csInf ?_ ?_
  · exact ⟨1, one_mem_steinBetaSet_pmf P₁ P₂ hP₁_sum hP₂_sum n alpha h_alpha_nn⟩
  · rintro β ⟨s, _, rfl⟩
    refine Finset.sum_nonneg ?_
    intro x _
    exact Finset.prod_nonneg (fun i _ => hP₂_nn (x i))

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `steinTypeII_at_level_pmf P₁ P₂ n alpha ≤ 1`. -/
lemma steinTypeII_at_level_pmf_le_one
    (P₁ P₂ : α → ℝ) (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    steinTypeII_at_level_pmf P₁ P₂ n alpha ≤ 1 := by
  unfold steinTypeII_at_level_pmf
  refine csInf_le ?_ ?_
  · exact ⟨0, fun β ⟨s, _, hβ⟩ => by
      rw [hβ]
      exact Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun i _ => hP₂_nn (x i)))⟩
  · exact one_mem_steinBetaSet_pmf P₁ P₂ hP₁_sum hP₂_sum n alpha h_alpha_nn

/-! ## Hoeffding constraint set convexity + Qstar full support -/

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The Hoeffding constraint set is **convex**: intersection of the convex simplex with
the convex sublevel set of the convex functional `Q ↦ klDivPmf Q P₁`. -/
@[entry_point]
lemma hoeffdingConstraintSet_convex
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha : ℝ) :
    Convex ℝ (hoeffdingConstraintSet P₁ alpha) := by
  -- K = {Q | Q ∈ stdSimplex ∧ klDivPmf Q P₁ ≤ alpha}.
  intro Q₁ hQ₁ Q₂ hQ₂ a b ha_nn hb_nn hab
  refine ⟨?_, ?_⟩
  · -- Q₁, Q₂ ∈ stdSimplex; midpoint is in stdSimplex by convex_stdSimplex.
    exact convex_stdSimplex ℝ α hQ₁.1 hQ₂.1 ha_nn hb_nn hab
  · -- klDivPmf · P₁ is convex on stdSimplex, both Q₁, Q₂ satisfy ≤ alpha.
    have h_conv := (klDivPmf_strictConvexOn_left P₁ hP₁_pos).convexOn
    have h_mid := h_conv.2 hQ₁.1 hQ₂.1 ha_nn hb_nn hab
    have h_kl_avg :
        klDivPmf (a • Q₁ + b • Q₂) P₁
          ≤ a • klDivPmf Q₁ P₁ + b • klDivPmf Q₂ P₁ := h_mid
    have h_kl₁ : klDivPmf Q₁ P₁ ≤ alpha := hQ₁.2
    have h_kl₂ : klDivPmf Q₂ P₁ ≤ alpha := hQ₂.2
    have h_bound : a • klDivPmf Q₁ P₁ + b • klDivPmf Q₂ P₁ ≤ alpha := by
      simp only [smul_eq_mul]
      have h1 : a * klDivPmf Q₁ P₁ ≤ a * alpha := mul_le_mul_of_nonneg_left h_kl₁ ha_nn
      have h2 : b * klDivPmf Q₂ P₁ ≤ b * alpha := mul_le_mul_of_nonneg_left h_kl₂ hb_nn
      have h_split : a * alpha + b * alpha = alpha := by
        have : (a + b) * alpha = alpha := by rw [hab]; ring
        linarith [this]
      linarith
    linarith [h_kl_avg]

-- Full-support of the minimizer: the rigorous proof requires a log-singularity gradient
-- argument (HasDerivAt computation showing the directional derivative of `klDivPmf · P₂`
-- at a 0-atom is `-∞`). Downstream lemmas take `hQs_pos` as a hypothesis.

/-! ## Pythagoras-based minimizer bound -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Hoeffding Sanov minimizer**: for any `P ∈ K` with full support,
`klDivPmf Qstar P₂ ≤ klDivPmf P P₂`, via the Csiszar Pythagoras inequality
`klDivPmf P P₂ ≥ klDivPmf P Qstar + klDivPmf Qstar P₂`. -/
@[entry_point]
lemma hoeffding_minimizer_ge
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (_hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (_h_alpha_nn : 0 ≤ alpha)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂)
    {P : α → ℝ}
    (hP_mem : P ∈ hoeffdingConstraintSet P₁ alpha)
    (hP_pos : ∀ a, 0 < P a) :
    klDivPmf Qstar P₂ ≤ klDivPmf P P₂ := by
  -- IsMinOn from hQs_min + hQs_mem.
  have hQs_isMinOn : IsMinOn (fun Q : α → ℝ => klDivPmf Q P₂)
      (hoeffdingConstraintSet P₁ alpha) Qstar := by
    intro Q hQ
    -- Goal: klDivPmf Qstar P₂ ≤ klDivPmf Q P₂.
    show klDivPmf Qstar P₂ ≤ klDivPmf Q P₂
    have hQ_K : Q ∈ hoeffdingConstraintSet P₁ alpha := hQ
    -- hoeffdingE2 ≤ klDivPmf Q P₂ since Q ∈ K.
    have h_E2_le : hoeffdingE2 P₁ P₂ alpha ≤ klDivPmf Q P₂ := by
      unfold hoeffdingE2
      have h_bdd : BddBelow ((fun Q : α → ℝ => klDivPmf Q P₂) ''
          {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}) := by
        refine ⟨0, ?_⟩
        rintro y ⟨Q', hQ', rfl⟩
        exact klDivPmf_nonneg Q' P₂ hQ'.1.1 (fun a => (hP₂_pos a).le)
      have h_in_img :
          klDivPmf Q P₂ ∈ (fun Q : α → ℝ => klDivPmf Q P₂) ''
              {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha} :=
        ⟨Q, hQ_K, rfl⟩
      exact csInf_le h_bdd h_in_img
    rw [hQs_min] at h_E2_le
    exact h_E2_le
  -- Apply csiszar_pythagoras_inequality.
  have h_pyth := csiszar_pythagoras_inequality
    (K := hoeffdingConstraintSet P₁ alpha)
    (Q := P₂)
    (hoeffdingConstraintSet_convex P₁ hP₁_pos alpha)
    (hoeffdingConstraintSet_subset_stdSimplex P₁ alpha)
    hP₂_sum
    hP₂_pos
    hQs_mem hQs_pos hQs_isMinOn
    hP_mem hP_pos
  -- klDivPmf P P₂ ≥ klDivPmf P Qstar + klDivPmf Qstar P₂.
  have h_pq_nn : 0 ≤ klDivPmf P Qstar :=
    klDivPmf_nonneg P Qstar (fun a => (hP_pos a).le) (fun a => (hQs_pos a).le)
  linarith

end InformationTheory.Shannon.HoeffdingTradeoff
