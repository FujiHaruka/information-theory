import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CentralLimitTheorem
import Common2026.Shannon.CramerLC2DischargeExt

/-!
# Cramér / Chernoff CLT-boundary closure — foundations (Phase 1-2) + CLT (Phase 3-4)

Foundational pieces and the CLT-based boundary discharge for the boundary case
`a = tilted mean` of `IsTiltedWindowEventuallyLarge` (left open by the interior
LLN-squeeze `tiltedWindow_eventually_large_of_cgfDeriv_interior`).

* `gaussianReal_Ici_eq_half` — **Gaussian median**: a centered Gaussian with
  non-degenerate variance puts mass `1/2` on the closed half-line `{x | 0 ≤ x}`.
  Mathlib-absent; proved via `gaussianReal_map_neg` symmetry + `noAtoms`.
* `tendsto_measure_Ici_of_tendsto_gaussian` — **portmanteau half-line bridge**:
  if a sequence of probability measures on `ℝ` converges weakly to a
  non-degenerate centered Gaussian, then the half-line masses converge to `1/2`.
  Assembled from `tendsto_measure_of_null_frontier_of_tendsto'` + `frontier_Ici`
  + `noAtoms_gaussianReal` + `gaussianReal_Ici_eq_half`.

## Phase 3-4 (CLT-based boundary discharge)

* `tiltedAmbient_clt` — apply Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`
  to the tilted ambient `infinitePi (μ₀.tilted (lam·Y))`, using the existing
  plumbing (`iIndepFun_tilted_ambient`, `identDistrib_tilted_ambient`,
  `memLp_of_bounded`) and the `HasLaw.id` witness, then reshape the resulting
  `TendstoInDistribution.tendsto` into a `ProbabilityMeasure` weak-convergence.
* `tiltedHalfLine_tendsto_half` — the half-line mass `P{m·n ≤ ∑ Y}` tends to
  `1/2` (CLT + scaling preimage + Gaussian median).
* `tiltedWindow_eventually_large_of_boundary` — at the boundary `a = m`, the
  window mass `P{m·n ≤ ∑ Y < (m+ε)·n}` is eventually `≥ 1/4` (half-line at `m`
  tends to `1/2`, half-line at `m+ε` tends to `0` by the existing LLN).
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal NNReal

/-- **Gaussian median**: a centered Gaussian with non-degenerate variance puts
mass `1/2` on the closed half-line `{x | 0 ≤ x}`.  Mathlib-absent; proved via
`gaussianReal_map_neg` symmetry + `noAtoms_gaussianReal`. -/
theorem gaussianReal_Ici_eq_half {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v {x : ℝ | (0 : ℝ) ≤ x} = 1 / 2 := by
  set μ : Measure ℝ := gaussianReal 0 v with hμ
  set A : Set ℝ := {x : ℝ | (0 : ℝ) ≤ x} with hA
  set B : Set ℝ := {x : ℝ | x ≤ (0 : ℝ)} with hB
  have hAmeas : MeasurableSet A := measurableSet_Ici
  have hBmeas : MeasurableSet B := measurableSet_Iic
  -- Symmetry: the half-line masses agree, via `x ↦ -x`.
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' A = B := by
    ext x; simp only [hA, hB, Set.mem_preimage, Set.mem_setOf_eq, neg_nonneg]
  have hsym : μ A = μ B := by
    have hmap : μ.map (fun x : ℝ ↦ -x) = μ := by
      rw [hμ, gaussianReal_map_neg]; simp
    calc
      μ A = μ.map (fun x : ℝ ↦ -x) A := by rw [hmap]
      _ = μ ((fun x : ℝ ↦ -x) ⁻¹' A) := by
            rw [Measure.map_apply measurable_neg hAmeas]
      _ = μ B := by rw [hpre]
  -- Union covers everything, intersection is the null point `{0}`.
  have hunion : A ∪ B = Set.univ := by
    ext x
    simp only [hA, hB, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total 0 x
  have hinter : A ∩ B = {(0 : ℝ)} := by
    ext x
    simp only [hA, hB, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx0, hx1⟩; exact le_antisymm hx1 hx0
    · rintro rfl; exact ⟨le_refl _, le_refl _⟩
  haveI : NoAtoms μ := noAtoms_gaussianReal hv
  have hinter0 : μ (A ∩ B) = 0 := by rw [hinter]; exact measure_singleton _
  have huniv : μ (A ∪ B) = 1 := by rw [hunion, measure_univ]
  -- `μ(A∪B) + μ(A∩B) = μ A + μ B`, i.e. `2 * μ A = 1`.
  have htwo : 2 * μ A = 1 := by
    have hkey := measure_union_add_inter (μ := μ) A hBmeas
    rw [huniv, hinter0, add_zero, ← hsym] at hkey
    rw [two_mul]
    exact hkey.symm
  -- Solve `2 * μ A = 1` for `μ A = 1 / 2` in `ℝ≥0∞`.
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  exact htwo

/-- **Portmanteau half-line bridge** (Gaussian limit): if `μs n` converges weakly
to a non-degenerate centered Gaussian, the closed half-line masses converge to
`1/2` (the Gaussian median). -/
theorem tendsto_measure_Ici_of_tendsto_gaussian {v : ℝ≥0} (hv : v ≠ 0)
    {μs : ℕ → ProbabilityMeasure ℝ}
    (h_lim : Tendsto μs atTop
      (𝓝 (⟨gaussianReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ))) :
    Tendsto (fun n ↦ (μs n : Measure ℝ) {x : ℝ | (0 : ℝ) ≤ x}) atTop (𝓝 (1 / 2)) := by
  set μ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 v, inferInstance⟩ with hμ
  set E : Set ℝ := {x : ℝ | (0 : ℝ) ≤ x} with hE
  have hEIci : E = Set.Ici (0 : ℝ) := rfl
  -- The frontier of the closed half-line is the null point `{0}`.
  haveI : NoAtoms (gaussianReal (0 : ℝ) v) := noAtoms_gaussianReal hv
  have E_nullbdry : (μ : Measure ℝ) (frontier E) = 0 := by
    rw [hμ, ProbabilityMeasure.coe_mk, hEIci, frontier_Ici]
    exact measure_singleton _
  -- Portmanteau half-line convergence.
  have hport :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h_lim E_nullbdry
  -- Rewrite the limit value to the Gaussian median `1/2`.
  have hlimval : (μ : Measure ℝ) E = 1 / 2 := by
    rw [hμ, ProbabilityMeasure.coe_mk, hE]
    exact gaussianReal_Ici_eq_half hv
  rwa [hlimval] at hport

/-! ## Phase 3 — CLT on the tilted ambient -/

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **CLT on the tilted ambient** (Phase 3).  Applying Mathlib's
`tendstoInDistribution_inv_sqrt_mul_sum_sub` to the coordinate-eval family
`X i ω := Y (ω i)` under `P := infinitePi (μ₀.tilted (lam·Y))`, the centered &
rescaled partial sums `S_n := (√n)⁻¹ · (∑ Y(ω k) − n·𝔼[Y(ω 0)])` converge weakly
to the centered Gaussian with the tilted variance.  Output is reshaped to the
`ProbabilityMeasure` weak-convergence form consumed by
`tendsto_measure_Ici_of_tendsto_gaussian`. -/
theorem tiltedAmbient_clt
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    [IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))] :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → Ω₀) => (√n)⁻¹ *
        (∑ k ∈ Finset.range n, Y (ω k)
          - n * ∫ ω, Y (ω 0)
              ∂(Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))))
      atTop (id : ℝ → ℝ)
      (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
      (gaussianReal 0
        Var[fun ω : ℕ → Ω₀ => Y (ω 0);
          Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))].toNNReal) := by
  obtain ⟨M, hM⟩ := h_bdd
  have hX_memLp : MemLp (fun ω : ℕ → Ω₀ => Y (ω 0)) 2
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := by
    refine memLp_of_bounded (a := -M) (b := M) ?_
      (hY_meas.comp (measurable_pi_apply 0)).aestronglyMeasurable 2
    exact Filter.Eventually.of_forall (fun ω => abs_le.mp (hM (ω 0)))
  -- Mathlib's CLT, instantiated at `X i ω := Y (ω i)` over the tilted ambient,
  -- with the Gaussian limit law witnessed by `HasLaw.id`.
  exact tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))
    (P := Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
    (Y := (id : ℝ → ℝ))
    (P' := gaussianReal 0
      Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))].toNNReal)
    HasLaw.id hX_memLp
    (iIndepFun_tilted_ambient hY_meas ⟨M, hM⟩ lam)
    (fun i => identDistrib_tilted_ambient hY_meas ⟨M, hM⟩ lam i)

/-! ## Phase 4 — half-line mass tends to `1/2`, window mass eventually `≥ 1/4` -/

/-- **Half-line mass tends to `1/2`** (Phase 4).  At the tilted mean `m := 𝔼[Y]`,
the probability `P{m·n ≤ ∑ Y(ω k)}` tends to `1/2` — the Gaussian-median value,
via CLT + the scaling preimage identity `{m·n ≤ ∑ Y} = S_n ⁻¹' (Ici 0)`. -/
theorem tiltedHalfLine_tendsto_half
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    Tendsto
      (fun n : ℕ =>
        (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ |
            (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
              ≤ ∑ i ∈ Finset.range n, Y (ω i)})
      atTop (𝓝 (1 / 2)) := by
  haveI hP : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    isProbabilityMeasure_infinitePi_tilted_of_bounded hY_meas h_bdd lam
  set P : Measure (ℕ → Ω₀) :=
    Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) with hPdef
  set v : ℝ := Var[fun ω : ℕ → Ω₀ => Y (ω 0); P] with hvdef
  -- tilted mean, in the two equal forms used by the CLT vs the goal.
  set m : ℝ := ∫ ω, Y (ω 0) ∂P with hmdef
  have hm_eq : m = ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) :=
    integral_eval_under_infinitePi_tilted hY_meas h_bdd lam
  -- the CLT statistic.
  set S : ℕ → (ℕ → Ω₀) → ℝ :=
    fun n ω => (√n)⁻¹ * (∑ k ∈ Finset.range n, Y (ω k) - n * m) with hSdef
  -- non-degeneracy of the limiting variance.
  have hv_ne : v.toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hVar
  -- `S n` is a.e.-measurable, packaging the source `ProbabilityMeasure`.
  have hS_aem : ∀ n : ℕ, AEMeasurable (S n) P := by
    intro n
    refine AEMeasurable.const_mul ?_ _
    refine AEMeasurable.sub ?_ aemeasurable_const
    exact (Finset.measurable_sum _
      (fun i _ => hY_meas.comp (measurable_pi_apply i))).aemeasurable
  -- Repackage the CLT limit as a Gaussian `ProbabilityMeasure`.
  set μs : ℕ → ProbabilityMeasure ℝ :=
    fun n => ⟨P.map (S n), Measure.isProbabilityMeasure_map (hS_aem n)⟩ with hμsdef
  -- CLT `.tendsto` field, with the limit `P'.map id` reshaped to `P'`.
  have hclt := (tiltedAmbient_clt (μ₀ := μ₀) hY_meas h_bdd lam).tendsto
  have h_lim : Tendsto μs atTop
      (𝓝 (⟨gaussianReal 0 v.toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
    have hlim_eq :
        (⟨gaussianReal 0 v.toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ)
          = ⟨(gaussianReal 0 v.toNNReal).map (id : ℝ → ℝ),
              Measure.isProbabilityMeasure_map aemeasurable_id⟩ := by
      apply Subtype.ext; exact Measure.map_id.symm
    rw [hlim_eq]
    exact hclt
  -- Half-line masses converge to `1/2` (Gaussian median, portmanteau).
  have h_half := tendsto_measure_Ici_of_tendsto_gaussian hv_ne h_lim
  -- Scaling preimage: `(P.map (S n)) {0 ≤ ·} = P {m·n ≤ ∑ Y}` for `n ≥ 1`.
  have h_pre : ∀ n : ℕ, 1 ≤ n →
      (μs n : Measure ℝ) {x : ℝ | (0 : ℝ) ≤ x}
        = P {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
    intro n hn
    rw [hμsdef]
    simp only [ProbabilityMeasure.coe_mk]
    have hms : MeasurableSet {x : ℝ | (0 : ℝ) ≤ x} := measurableSet_Ici
    rw [Measure.map_apply_of_aemeasurable (hS_aem n) hms]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hSdef]
    -- `0 ≤ (√n)⁻¹ * (∑ Y − n·m) ⟺ m·n ≤ ∑ Y`, using `√n > 0` for `n ≥ 1`.
    have hsqrt_pos : (0 : ℝ) < (√n)⁻¹ := by
      rw [inv_pos]; exact Real.sqrt_pos.mpr (by exact_mod_cast hn)
    rw [← sub_nonneg (b := m * n)]
    constructor
    · intro h
      have := (mul_nonneg_iff_of_pos_left hsqrt_pos).mp h
      linarith
    · intro h
      have hge : (0 : ℝ) ≤ ∑ k ∈ Finset.range n, Y (ω k) - n * m := by linarith
      exact mul_nonneg hsqrt_pos.le hge
  -- Rewrite `h_half` (eventually, for `n ≥ 1`) to the half-line probability of `P`.
  have h_half' : Tendsto
      (fun n : ℕ => P {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})
      atTop (𝓝 (1 / 2)) := by
    refine h_half.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn using h_pre n hn
  -- Move to `.real` via `toReal`.
  have h_toReal := (ENNReal.tendsto_toReal (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞)).comp h_half'
  rw [show ((1 / 2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num] at h_toReal
  refine h_toReal.congr ?_
  intro n
  simp only [Function.comp_apply, measureReal_def, hm_eq]

/-- **Boundary window largeness** (Phase 4 main).  At the boundary `a = m`
(tilted mean), with non-degenerate tilted variance, the window mass
`P{m·n ≤ ∑ Y < (m+ε)·n}` is eventually at least `1/4`.  Combines
`tiltedHalfLine_tendsto_half` (→ `1/2`) with the existing LLN
`tilted_lln_in_probability_real` (the `(m+ε)`-half-line mass → `0`). -/
theorem tiltedWindow_eventually_large_of_boundary
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 4 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ |
            (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i)
                < ((∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) + ε) * n} := by
  haveI hP : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    isProbabilityMeasure_infinitePi_tilted_of_bounded hY_meas h_bdd lam
  set P : Measure (ℕ → Ω₀) :=
    Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) with hPdef
  set m : ℝ := ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) with hmdef
  -- Half-line at the boundary mean `m` → 1/2.
  have h1 : Tendsto
      (fun n : ℕ => P.real {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})
      atTop (𝓝 (1 / 2)) :=
    tiltedHalfLine_tendsto_half (μ₀ := μ₀) hY_meas h_bdd lam hVar
  -- Half-line at `m + ε` → 0, by the in-probability LLN (right tail beyond the mean).
  have hlln := tilted_lln_in_probability_real (μ₀ := μ₀) hY_meas h_bdd lam (ε := ε) hε
  have h2 : Tendsto
      (fun n : ℕ => P.real {ω : ℕ → Ω₀ | (m + ε) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})
      atTop (𝓝 0) := by
    -- squeeze between `0` and the LLN bad-set mass, eventually for `n ≥ 1`
    refine squeeze_zero' (Filter.Eventually.of_forall (fun n => measureReal_nonneg))
      (g := fun n => P.real {ω : ℕ → Ω₀ | ε ≤ |(∑ i ∈ Finset.range n, Y (ω i)) / n - m|}) ?_ hlln
    filter_upwards [eventually_ge_atTop 1] with n hn
    -- monotonicity, for `n ≥ 1`: `(m+ε)·n ≤ ∑Y ⟹ ε ≤ |∑Y/n − m|`
    refine measureReal_mono (fun ω hω => ?_)
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv : m + ε ≤ (∑ i ∈ Finset.range n, Y (ω i)) / n := by
      rw [le_div_iff₀ hnR]; linarith [hω]
    calc ε ≤ (∑ i ∈ Finset.range n, Y (ω i)) / n - m := by linarith
      _ ≤ |(∑ i ∈ Finset.range n, Y (ω i)) / n - m| := le_abs_self _
  -- The window mass is the difference of the two half-line masses.
  have hsub : ∀ n : ℕ,
      {ω : ℕ → Ω₀ | (m + ε) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}
        ⊆ {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hεn : (0 : ℝ) ≤ ε * n := by positivity
    nlinarith [hω]
  have hms2 : ∀ n : ℕ,
      MeasurableSet {ω : ℕ → Ω₀ | (m + ε) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
    intro n
    exact measurableSet_le measurable_const
      (Finset.measurable_sum _ (fun i _ => hY_meas.comp (measurable_pi_apply i)))
  have hwin_eq : ∀ n : ℕ,
      P.real {ω : ℕ → Ω₀ |
          m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
          ∧ ∑ i ∈ Finset.range n, Y (ω i) < (m + ε) * n}
        = P.real {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}
          - P.real {ω : ℕ → Ω₀ | (m + ε) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
    intro n
    rw [← measureReal_diff (hsub n) (hms2 n)]
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_diff, not_le]
  -- The window mass tends to `1/2 − 0 = 1/2`, hence eventually `≥ 1/4`.
  have hwin_tendsto : Tendsto
      (fun n : ℕ => P.real {ω : ℕ → Ω₀ |
          m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
          ∧ ∑ i ∈ Finset.range n, Y (ω i) < (m + ε) * n})
      atTop (𝓝 (1 / 2)) := by
    have := (h1.sub h2)
    simp only [sub_zero] at this
    exact this.congr (fun n => (hwin_eq n).symm)
  exact hwin_tendsto.eventually_const_le (show (1 : ℝ) / 4 < 1 / 2 by norm_num)

end InformationTheory.Shannon.Cramer.Discharge
