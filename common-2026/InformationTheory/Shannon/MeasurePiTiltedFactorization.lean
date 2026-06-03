import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.Basic
import InformationTheory.Meta.EntryPoint

/-!
# Finite `Measure.pi` tilt factorization (Cramér Phase C, Phase 1)

This file builds the **finite-product tilt factorization** lemma that is the
missing first piece for the `IsMeasureInfinitePiTiltedEq` discharge of
`InformationTheory/Shannon/CramerLC2PhaseC.lean`.

The key result is `pi_tilted_sum_eq_pi_tilted`:
```
(Measure.pi (fun _ : Fin n => μ₀)).tilted (fun ω => ∑ i, lam * Y (ω i))
  = Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω))
```

Mathlib has no `Measure.pi × tilted` / `Measure.pi × withDensity` compatibility
lemma (loogle `Found 0`). We build it from `Measure.pi_eq` (a measure on a finite
product equals the product measure if they agree on rectangles), reducing to a
box-wise lintegral product factorization which we prove by `Fin n` induction
mirroring `MeasureTheory.integral_fin_nat_prod_eq_prod`.

## Outline

* `lintegral_pi_prod` — unrestricted lintegral Fubini for `Measure.pi` of a
  per-coordinate product, by `Fin n` induction.
* `setLIntegral_pi_prod_factor` (1-C) — box-restricted version via the indicator
  trick.
* `integral_exp_sum_pi_eq_pow` (1-B) — normalization constant `Z^n`.
* `pi_tilted_sum_eq_pi_tilted` (1-D) — the finite tilt factorization.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## 1-C core: lintegral product factorization over `Measure.pi` -/

/-- **Unrestricted lintegral Fubini** for `Measure.pi` of a per-coordinate
product of nonnegative measurable functions. The lintegral analogue of
`MeasureTheory.integral_fin_nat_prod_eq_prod`; not present in Mathlib. -/
@[entry_point]
theorem lintegral_pi_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    {g : (i : Fin n) → E i → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, g i (x i) ∂(Measure.pi μ)
      = ∏ i, ∫⁻ ω, g i ω ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      haveI : ∀ j : Fin n, SigmaFinite (μ j.succ) := fun j => inferInstance
      have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
      rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.insertNth_zero, Fin.cons_succ,
        Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      have hpm := lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j => μ j.succ)
          (f := g 0)
          (g := fun b : (j : Fin n) → E j.succ => ∏ x, g x.succ (b x))
          (hg 0).aemeasurable
          (Finset.measurable_prod _ (fun i _ => (hg i.succ).comp
            (measurable_pi_apply i))).aemeasurable
      simp only at hpm
      conv_rhs => rw [← n_ih (fun i => hg i.succ)]
      exact hpm

/-- **1-C (box-restricted Tonelli)**: the lintegral over the box `pi univ s` of a
per-coordinate product factors as the product of the per-coordinate
box-restricted lintegrals. -/
@[entry_point]
theorem setLIntegral_pi_prod_factor {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {g : Ω₀ → ℝ≥0∞} (hg : Measurable g) (s : Fin n → Set Ω₀)
    (hs : ∀ i, MeasurableSet (s i)) :
    ∫⁻ x in Set.pi Set.univ s, ∏ i, g (x i) ∂(Measure.pi (fun _ : Fin n => μ₀))
      = ∏ i, ∫⁻ ω in s i, g ω ∂μ₀ := by
  classical
  have hbox : MeasurableSet (Set.pi (Set.univ : Set (Fin n)) s) :=
    MeasurableSet.univ_pi hs
  rw [← lintegral_indicator hbox]
  -- The box indicator of a coordinate product factors coordinate-wise.
  have hpt : ∀ x : Fin n → Ω₀,
      (Set.pi Set.univ s).indicator (fun x => ∏ i, g (x i)) x
        = ∏ i, ((s i).indicator g) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [Set.indicator_of_notMem hi]
  simp_rw [hpt]
  rw [lintegral_pi_prod (fun i => hg.indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i)]

/-! ## 1-B: normalization constant `Z^n` -/

/-- **1-B**: the partition function of the sum exponent on the finite product is
the `n`-th power of the single-coordinate partition function. -/
@[entry_point]
theorem integral_exp_sum_pi_eq_pow {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (lam : ℝ) :
    ∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : Fin n => μ₀))
      = (∫ ω, Real.exp (lam * Y ω) ∂μ₀) ^ n := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (fun ω => Real.exp (lam * Y ω)), Fintype.card_fin]

/-! ## 1-D: the finite tilt factorization (main deliverable) -/

/-- **1-D (main deliverable)**: the tilt of the finite product measure by the
sum exponent factors as the product of the per-coordinate tilts.

`(Measure.pi (fun _ => μ₀)).tilted (∑ i, lam · Y (· i)) = Measure.pi (fun _ => μ₀.tilted (lam · Y))`. -/
@[entry_point]
theorem pi_tilted_sum_eq_pi_tilted {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (lam : ℝ) :
    (Measure.pi (fun _ : Fin n => μ₀)).tilted (fun ω => ∑ i, lam * Y (ω i))
      = Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω)) := by
  -- Single-coordinate partition function.
  set Z₁ : ℝ := ∫ ω, Real.exp (lam * Y ω) ∂μ₀ with hZ₁
  -- Apply `Measure.pi_eq`: agreement on boxes determines the product measure.
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  -- LHS box mass via `tilted_apply'`.
  have hbox : MeasurableSet (Set.pi (Set.univ : Set (Fin n)) s) :=
    MeasurableSet.univ_pi hs
  rw [tilted_apply' _ _ hbox]
  -- Normalization constant: `Z_n = Z₁ ^ n`.
  have hZn : (∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : Fin n => μ₀)))
      = Z₁ ^ n := by rw [hZ₁]; exact integral_exp_sum_pi_eq_pow lam
  rw [hZn]
  -- Density factorizes coordinate-wise.
  have hdens : ∀ x : Fin n → Ω₀,
      ENNReal.ofReal (Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ n)
        = ∏ i, ENNReal.ofReal (Real.exp (lam * Y (x i)) / Z₁) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Real.exp_sum, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  simp_rw [hdens]
  rw [setLIntegral_pi_prod_factor
      (g := fun ω => ENNReal.ofReal (Real.exp (lam * Y ω) / Z₁))
      ((measurable_exp.comp (measurable_const.mul hY)).div_const _).ennreal_ofReal s hs]
  -- RHS box mass via `tilted_apply'` on each coordinate.
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [tilted_apply' _ _ (hs i)]

end InformationTheory.Shannon.Cramer.Discharge
