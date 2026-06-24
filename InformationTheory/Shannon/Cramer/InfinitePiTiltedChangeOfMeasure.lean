import InformationTheory.Shannon.MeasurePiTiltedFactorization
import InformationTheory.Shannon.Cramer.TiltedLLN
import InformationTheory.Shannon.Cramer.LC2PhaseC
import Mathlib.Probability.ProductMeasure
import InformationTheory.Meta.EntryPoint

/-!
# infinitePi-tilted change-of-measure

This file builds on the finite `Measure.pi` tilt factorization
(`MeasurePiTiltedFactorization.pi_tilted_sum_eq_pi_tilted`) to supply the
infinite-product change-of-measure machinery behind the Cramér lower bound.

## Main statements

* `pi_tilted_sum_eq_pi_tilted_fintype` — the tilt of a finite product measure by
  the sum exponent factors as the product of per-coordinate tilts, generalized
  from `Fin n` to an arbitrary `Fintype` index.
* `cramer_lower_phaseC_residual_discharge` — the end-to-end liminf lower bound
  from the optimal-tilt inputs.
* `tiltedWindow_eventually_large_of_cgfDeriv_interior` — the tilted-window mass
  is eventually `≥ 1/2` when the cgf derivative lands strictly inside the window.
-/

namespace InformationTheory.Shannon.Cramer.TiltedLLN

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Fintype generalization of the lintegral Fubini identity -/

theorem lintegral_pi_prod_fintype {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    {g : (i : ι) → E i → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, g i (x i) ∂(Measure.pi μ)
      = ∏ i, ∫⁻ ω, g i ω ∂(μ i) := by
  classical
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  -- Reindex `Measure.pi μ` along `e : Fin (card ι) ≃ ι`.
  have hmp := measurePreserving_piCongrLeft (α := fun i ↦ E i) μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hcomp : ∀ y : (i : Fin (Fintype.card ι)) → E (e i),
      (∏ i, g i ((MeasurableEquiv.piCongrLeft (fun i ↦ E i) e y) i))
        = ∏ j, g (e j) (y j) := by
    intro y
    rw [← e.prod_comp (fun i ↦ g i ((MeasurableEquiv.piCongrLeft (fun i ↦ E i) e y) i))]
    refine Finset.prod_congr rfl (fun j _ ↦ ?_)
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hcomp]
  rw [lintegral_pi_prod (μ := fun j ↦ μ (e j)) (fun j ↦ hg (e j))]
  exact e.prod_comp (fun i ↦ ∫⁻ ω, g i ω ∂(μ i))

/-! ## Fintype generalization of the box Tonelli and tilt factorization -/

theorem setLIntegral_pi_prod_factor_fintype {ι : Type*} [Fintype ι]
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {g : Ω₀ → ℝ≥0∞} (hg : Measurable g) (s : ι → Set Ω₀)
    (hs : ∀ i, MeasurableSet (s i)) :
    ∫⁻ x in Set.pi Set.univ s, ∏ i, g (x i) ∂(Measure.pi (fun _ : ι ↦ μ₀))
      = ∏ i, ∫⁻ ω in s i, g ω ∂μ₀ := by
  classical
  have hbox : MeasurableSet (Set.pi (Set.univ : Set ι) s) :=
    MeasurableSet.univ_pi hs
  rw [← lintegral_indicator hbox]
  have hpt : ∀ x : ι → Ω₀,
      (Set.pi Set.univ s).indicator (fun x ↦ ∏ i, g (x i)) x
        = ∏ i, ((s i).indicator g) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl (fun i _ ↦ ?_)
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [Set.indicator_of_notMem hi]
  simp_rw [hpt]
  rw [lintegral_pi_prod_fintype (fun i ↦ hg.indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [lintegral_indicator (hs i)]

theorem integral_exp_sum_pi_eq_pow_fintype {ι : Type*} [Fintype ι]
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀] {Y : Ω₀ → ℝ} (lam : ℝ) :
    ∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : ι ↦ μ₀))
      = (∫ ω, Real.exp (lam * Y ω) ∂μ₀) ^ (Fintype.card ι) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (fun ω ↦ Real.exp (lam * Y ω))]

/-- The tilt of a finite (`Fintype`) product measure by the sum exponent factors
as the product of per-coordinate tilts. -/
@[entry_point]
theorem pi_tilted_sum_eq_pi_tilted_fintype {ι : Type*} [Fintype ι]
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (lam : ℝ) :
    (Measure.pi (fun _ : ι ↦ μ₀)).tilted (fun ω ↦ ∑ i, lam * Y (ω i))
      = Measure.pi (fun _ : ι ↦ μ₀.tilted (fun ω ↦ lam * Y ω)) := by
  set Z₁ : ℝ := ∫ ω, Real.exp (lam * Y ω) ∂μ₀ with hZ₁
  refine (Measure.pi_eq (fun s hs ↦ ?_)).symm
  have hbox : MeasurableSet (Set.pi (Set.univ : Set ι) s) :=
    MeasurableSet.univ_pi hs
  rw [tilted_apply' _ _ hbox]
  have hZn : (∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : ι ↦ μ₀)))
      = Z₁ ^ (Fintype.card ι) := by rw [hZ₁]; exact integral_exp_sum_pi_eq_pow_fintype lam
  rw [hZn]
  have hdens : ∀ x : ι → Ω₀,
      ENNReal.ofReal (Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ (Fintype.card ι))
        = ∏ i, ENNReal.ofReal (Real.exp (lam * Y (x i)) / Z₁) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ by positivity)]
    congr 1
    rw [Real.exp_sum, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  simp_rw [hdens]
  rw [setLIntegral_pi_prod_factor_fintype
      (g := fun ω ↦ ENNReal.ofReal (Real.exp (lam * Y ω) / Z₁))
      ((measurable_exp.comp (measurable_const.mul hY)).div_const _).ennreal_ofReal s hs]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [tilted_apply' _ _ (hs i)]

/-! ## End-to-end Cramér lower bound from the residual predicate -/

/-- The Cramér lower bound, end-to-end from the cgf-derivative and cobounded
inputs: the liminf lower bound `-(lam·a − Λ(lam)) ≤ liminf (1/n) log P[S_n ≥ a·n]`
from the optimal-tilt inputs (`h_deriv : deriv (cgf …) lam = a`, non-degeneracy
`hVar`, and the cobounded-below regularity `h_coboundedBelow`). The hypotheses
`hVar` and `h_coboundedBelow` are regularity preconditions, not part of the proof
core.

See also `cramer_lower_phaseC_partial_discharge`.

@audit:ok -/
@[entry_point]
theorem cramer_lower_phaseC_residual_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_deriv : deriv (cgf (fun ω : ℕ → Ω₀ ↦ Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ ↦ μ₀))) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ ↦ Y (ω 0);
        Measure.infinitePi (fun _ : ℕ ↦ μ₀.tilted (fun ω ↦ lam * Y ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ ↦ μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ ↦ Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ ↦ μ₀)) lam)
      ≤ liminf (fun n : ℕ ↦
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ ↦ μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
  cramer_lower_phaseC_partial_discharge hY_meas h_bdd a lam hlam h_deriv hVar h_coboundedBelow


/-- Per-instance tilted window mass ≥ 1/2 (cgf-derivative interior case).

Whenever the cgf derivative at `lam` lands strictly inside the window
`a < deriv (cgf Y μ₀) lam < a + ε`, the tilted infinite-product window mass is
eventually `≥ 1/2` (indeed `→ 1`).

This covers the interior case; the boundary case `a = deriv (cgf Y μ₀) lam`
(= tilted mean) requires a central-limit-theorem refinement rather than the law
of large numbers.

See also `tiltedWindow_eventually_large_of_interior`. -/
@[entry_point]
theorem tiltedWindow_eventually_large_of_cgfDeriv_interior
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {a ε : ℝ}
    (h_lo : a < deriv (cgf Y μ₀) lam)
    (h_hi : deriv (cgf Y μ₀) lam < a + ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 ≤ (Measure.infinitePi (fun _ : ℕ ↦ μ₀.tilted (fun ω ↦ lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n} := by
  have hbridge := tiltedMean_eq_deriv_cgf (μ₀ := μ₀) hY h_bdd lam
  refine tiltedWindow_eventually_large_of_interior hY h_bdd lam ?_ ?_
  · rw [hbridge]; exact h_lo
  · rw [hbridge]; exact h_hi

end InformationTheory.Shannon.Cramer.TiltedLLN
