import InformationTheory.Shannon.MeasurePiTiltedFactorization
import InformationTheory.Shannon.Cramer.LC2DischargeExt
import InformationTheory.Draft.Shannon.CramerLC2PhaseC
import Mathlib.Probability.ProductMeasure
import InformationTheory.Meta.EntryPoint

/-!
# infinitePi-tilted change-of-measure (Cramér Phase C, Phases 2–4)

This file builds on the finite `Measure.pi` tilt factorization
(`MeasurePiTiltedFactorization.pi_tilted_sum_eq_pi_tilted`) to discharge — or
maximally shrink — the `IsMeasureInfinitePiTiltedEq` predicate of
`InformationTheory/Shannon/CramerLC2PhaseC.lean`.

## Outline

* **Fintype generalization of Phase 1**: the `Fin n` factorization lemmas
  generalized to an arbitrary `Fintype` index via `MeasurableEquiv.piCongrLeft`
  reindexing, so they apply at the `↥(Finset.range n)` subtype produced by
  `infinitePi_cylinder`.
* **Phase 2 (cylinder lift)**: the width-`n` event
  `{ω | a·n ≤ ∑_{i<n} Y(ω i)}` is a cylinder over `Finset.range n`; its
  `infinitePi` mass equals the `Measure.pi` mass of the corresponding finite
  event, on both the un-tilted and the tilted ambient.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Fintype generalization of the Phase 1 lintegral Fubini -/

/-- **Fintype lintegral Fubini** for `Measure.pi` of a per-coordinate product,
generalizing `lintegral_pi_prod` from `Fin n` to an arbitrary `Fintype` index by
reindexing through `Fintype.equivFin`. -/
theorem lintegral_pi_prod_fintype {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    {g : (i : ι) → E i → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, g i (x i) ∂(Measure.pi μ)
      = ∏ i, ∫⁻ ω, g i ω ∂(μ i) := by
  classical
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  -- Reindex `Measure.pi μ` along `e : Fin (card ι) ≃ ι`.
  have hmp := measurePreserving_piCongrLeft (α := fun i => E i) μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hcomp : ∀ y : (i : Fin (Fintype.card ι)) → E (e i),
      (∏ i, g i ((MeasurableEquiv.piCongrLeft (fun i => E i) e y) i))
        = ∏ j, g (e j) (y j) := by
    intro y
    rw [← e.prod_comp (fun i => g i ((MeasurableEquiv.piCongrLeft (fun i => E i) e y) i))]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hcomp]
  rw [lintegral_pi_prod (μ := fun j => μ (e j)) (fun j => hg (e j))]
  exact e.prod_comp (fun i => ∫⁻ ω, g i ω ∂(μ i))

/-! ## Fintype generalization of the Phase 1 box Tonelli and tilt factorization -/

/-- **Fintype box Tonelli**: the lintegral over the box `pi univ s` of a
per-coordinate product factors coordinate-wise, for an arbitrary `Fintype`
index. Generalizes `setLIntegral_pi_prod_factor`. -/
theorem setLIntegral_pi_prod_factor_fintype {ι : Type*} [Fintype ι]
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {g : Ω₀ → ℝ≥0∞} (hg : Measurable g) (s : ι → Set Ω₀)
    (hs : ∀ i, MeasurableSet (s i)) :
    ∫⁻ x in Set.pi Set.univ s, ∏ i, g (x i) ∂(Measure.pi (fun _ : ι => μ₀))
      = ∏ i, ∫⁻ ω in s i, g ω ∂μ₀ := by
  classical
  have hbox : MeasurableSet (Set.pi (Set.univ : Set ι) s) :=
    MeasurableSet.univ_pi hs
  rw [← lintegral_indicator hbox]
  have hpt : ∀ x : ι → Ω₀,
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
  rw [lintegral_pi_prod_fintype (fun i => hg.indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i)]

/-- **Fintype normalization constant**: the partition function of the sum
exponent on a finite (`Fintype`) product is the `card`-th power of the
single-coordinate partition function. Generalizes `integral_exp_sum_pi_eq_pow`. -/
theorem integral_exp_sum_pi_eq_pow_fintype {ι : Type*} [Fintype ι]
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀] {Y : Ω₀ → ℝ} (lam : ℝ) :
    ∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : ι => μ₀))
      = (∫ ω, Real.exp (lam * Y ω) ∂μ₀) ^ (Fintype.card ι) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (fun ω => Real.exp (lam * Y ω))]

/-- **Fintype tilt factorization**: the tilt of a finite (`Fintype`) product
measure by the sum exponent factors as the product of per-coordinate tilts.
Generalizes `pi_tilted_sum_eq_pi_tilted`. -/
@[entry_point]
theorem pi_tilted_sum_eq_pi_tilted_fintype {ι : Type*} [Fintype ι]
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (lam : ℝ) :
    (Measure.pi (fun _ : ι => μ₀)).tilted (fun ω => ∑ i, lam * Y (ω i))
      = Measure.pi (fun _ : ι => μ₀.tilted (fun ω => lam * Y ω)) := by
  set Z₁ : ℝ := ∫ ω, Real.exp (lam * Y ω) ∂μ₀ with hZ₁
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  have hbox : MeasurableSet (Set.pi (Set.univ : Set ι) s) :=
    MeasurableSet.univ_pi hs
  rw [tilted_apply' _ _ hbox]
  have hZn : (∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : ι => μ₀)))
      = Z₁ ^ (Fintype.card ι) := by rw [hZ₁]; exact integral_exp_sum_pi_eq_pow_fintype lam
  rw [hZn]
  have hdens : ∀ x : ι → Ω₀,
      ENNReal.ofReal (Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ (Fintype.card ι))
        = ∏ i, ENNReal.ofReal (Real.exp (lam * Y (x i)) / Z₁) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Real.exp_sum, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  simp_rw [hdens]
  rw [setLIntegral_pi_prod_factor_fintype
      (g := fun ω => ENNReal.ofReal (Real.exp (lam * Y ω) / Z₁))
      ((measurable_exp.comp (measurable_const.mul hY)).div_const _).ennreal_ofReal s hs]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [tilted_apply' _ _ (hs i)]

/-! ## Phase 2/3/4 — hoisted to `CramerBoundaryUpstream.lean`

The following declarations were moved **verbatim** to
`InformationTheory/Shannon/CramerBoundaryUpstream.lean` on 2026-06-11 to break
the `CramerCltBoundaryClosure → InfinitePiTiltedChangeOfMeasure → CramerLC2PhaseC`
import cycle (`cramer-root-wiring-plan` Phase A a1):
`infinitePi_partialSum_event_eq_pi`, `change_of_measure_lower_bound_pi`,
`IsTiltedWindowEventuallyLarge`, `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`,
`tiltedWindow_eventually_tendsto_one`, `tiltedWindow_eventually_large_of_interior`,
`tiltedMean_eq_deriv_cgf`. They remain available here transitively via
`CramerLC2PhaseC → CramerBoundaryUpstream`. -/


/-! ## Phase 4 — end-to-end Cramér lower bound from the residual predicate -/

/-- **Cramér lower bound, residual discharge**. The `h_pred`
(`IsMeasureInfinitePiTiltedEq`) hypothesis of `cramer_lower_phaseC_partial_discharge`
is replaced by the strictly smaller residual window predicate
`IsTiltedWindowEventuallyLarge`. The full change-of-measure machinery (Phases
1–3 of `infinitepi-tilted-rn-discharge`) is discharged here; the only remaining
input is the eventual `≥ 1/2` largeness of the tilted-side window mass, which is
a one-sided LLN/boundary statement (`∫ Y ∂μ₀.tilted ∈ [a, a+ε)`).

NOTE: `cramer_lower_phaseC_partial_discharge` does not accept the
`h_pred : IsMeasureInfinitePiTiltedEq` hypothesis; the producer call into
`isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` was removed in the 2026-05-25
sweep. **The `_h_res` parameter is load-bearing in name only** (signature
retained for caller-API stability); the body is a single pass-through to the
upstream wrapper.

WIRED 2026-06-11 (`cramer-root-wiring-plan` Phase A): the upstream
`cramer_lower_phaseC_partial_discharge` is now discharged by the sorryAx-free
CLT-boundary headline, so this wrapper is sorryAx-free too (verified
`#print axioms` = `[propext, Classical.choice, Quot.sound]`). The root's
non-degeneracy precondition `hVar` is threaded through here as a regularity
precondition. `_h_res` remains load-bearing in name only (see above).

`@audit:closed-by-successor(cramer-chernoff-clt-closure-moonshot-plan)` -/
@[entry_point]
theorem cramer_lower_phaseC_residual_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_deriv : deriv (cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ => μ₀))) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (_h_res : IsTiltedWindowEventuallyLarge μ₀ Y lam) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
  cramer_lower_phaseC_partial_discharge hY_meas h_bdd a lam hlam h_deriv hVar h_coboundedBelow


/-- **Per-instance tilted window mass ≥ 1/2** (cgf-derivative interior case).

cgf-calculus restatement of `tiltedWindow_eventually_large_of_interior`: the
interior condition `a < tilted mean < a + ε` is rewritten via the
cgf-derivative bridge `tiltedMean_eq_deriv_cgf` as `a < deriv (cgf Y μ₀) lam`,
`deriv (cgf Y μ₀) lam < a + ε`. Whenever the cgf derivative at `lam` lands
strictly inside the window, the tilted infinite-product window mass is
eventually `≥ 1/2` (indeed `→ 1`).

The only residual gap left after this lemma is the **CLT boundary** case
`a = deriv (cgf Y μ₀) lam` (= tilted mean): squeezing the window mass to `1/2`
there requires a central-limit-theorem refinement, not the law of large numbers.
The interior `a < deriv (cgf Y μ₀) lam < a + ε` is fully discharged here, with
the window mass tending to `1`. -/
@[entry_point]
theorem tiltedWindow_eventually_large_of_cgfDeriv_interior
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {a ε : ℝ}
    (h_lo : a < deriv (cgf Y μ₀) lam)
    (h_hi : deriv (cgf Y μ₀) lam < a + ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n} := by
  have hbridge := tiltedMean_eq_deriv_cgf (μ₀ := μ₀) hY h_bdd lam
  refine tiltedWindow_eventually_large_of_interior hY h_bdd lam ?_ ?_
  · rw [hbridge]; exact h_lo
  · rw [hbridge]; exact h_hi

end InformationTheory.Shannon.Cramer.Discharge
