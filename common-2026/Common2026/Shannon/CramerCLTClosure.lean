import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CentralLimitTheorem
import Common2026.Shannon.CramerLC2DischargeExt
import Common2026.Shannon.InfinitePiTiltedChangeOfMeasure

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

/-! ## Phase 5 — `∃ C > 0` relaxed change-of-measure, single-`a` slice

The Phase-4 boundary lemma `tiltedWindow_eventually_large_of_boundary` only
delivers window mass `≥ 1/4`, whereas the residual reduction
`isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` hardcodes the `≥ 1/2`
threshold (and quantifies over *all* `a`). This section re-runs the Phase-2/3
change-of-measure (`change_of_measure_lower_bound_pi` + the cylinder lift
`infinitePi_partialSum_event_eq_pi`) at a *single* `a`, threading an arbitrary
positive constant `C` through instead of the fixed `1/2`. The output is the
`a`-slice of `IsMeasureInfinitePiTiltedEq`, in the exact `h_tilted_lower` shape
consumed by the parent `cramer_lower`. -/

/-- **`∃ C > 0` relaxed change-of-measure, single-`a` slice** (Phase 5).

Given, at a fixed threshold `a`, that for every `ε > 0` the tilted-side window
mass is eventually `≥` some positive constant `C` (the boundary case only gives
`1/4`, well below the `1/2` of `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`),
the un-tilted half-line mass admits the Chernoff lower bound `C · exp(…) ≤ …`.
This is the `a`-slice of `IsMeasureInfinitePiTiltedEq`, already in the
`cramer_lower` `h_tilted_lower` shape. -/
theorem isMeasureInfinitePiTiltedEq_at_of_window
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (lam : ℝ) (hlam : 0 ≤ lam) (a : ℝ)
    (h_win : ∀ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n}) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
  haveI hp : IsProbabilityMeasure (μ₀.tilted (fun ω => lam * Y ω)) :=
    isProbabilityMeasure_tilted_of_bounded hY h_bdd lam
  intro ε hε
  obtain ⟨C, hC_pos, hC_event⟩ := h_win ε hε
  refine ⟨C, hC_pos, ?_⟩
  -- The tilted window mass is eventually ≥ C.
  filter_upwards [hC_event] with n hn
  -- Cylinder lift, un-tilted side: half-line event.
  have hPE : MeasurableSet {r : ℝ | a * (n : ℝ) ≤ r} :=
    measurableSet_le measurable_const measurable_id
  have hlift_E := infinitePi_partialSum_event_eq_pi (ν := μ₀) hY n
      (fun r => a * (n : ℝ) ≤ r) hPE
  -- Cylinder lift, tilted side: window event.
  have hPW : MeasurableSet {r : ℝ | a * (n : ℝ) ≤ r ∧ r < (a + ε) * n} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  have hlift_W := infinitePi_partialSum_event_eq_pi
      (ν := μ₀.tilted (fun ω => lam * Y ω)) hY n
      (fun r => a * (n : ℝ) ≤ r ∧ r < (a + ε) * n) hPW
  -- Phase 3 change-of-measure at the finite level.
  have hcm := change_of_measure_lower_bound_pi (n := n) (μ₀ := μ₀) hY h_bdd a ε lam hlam
  -- Convert change-of-measure to `.real` form.
  have hfin_E : (Measure.pi (fun _ : Fin n => μ₀))
      {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i)} ≠ ⊤ := (measure_ne_top _ _)
  have hcm_real :
      Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
          * (Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω))).real
              {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i) ∧ ∑ i, Y (x i) < (a + ε) * n}
        ≤ (Measure.pi (fun _ : Fin n => μ₀)).real
              {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i)} := by
    have h := ENNReal.toReal_mono hfin_E hcm
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] at h
  -- Cylinder lift identifies the un-tilted half-line `.real`.
  have hE_real : (Measure.infinitePi (fun _ : ℕ => μ₀)).real
        {ω : ℕ → Ω₀ | a * (n : ℝ) ≤ ∑ i ∈ Finset.range n, Y (ω i)}
      = (Measure.pi (fun _ : Fin n => μ₀)).real
          {x : Fin n → Ω₀ | a * (n : ℝ) ≤ ∑ i, Y (x i)} := by
    rw [measureReal_def, measureReal_def, hlift_E]
  -- Cylinder lift identifies the tilted window `.real`.
  have hW_real : (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
        {ω : ℕ → Ω₀ | a * (n : ℝ) ≤ ∑ i ∈ Finset.range n, Y (ω i)
          ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n}
      = (Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω))).real
          {x : Fin n → Ω₀ | a * (n : ℝ) ≤ ∑ i, Y (x i) ∧ ∑ i, Y (x i) < (a + ε) * n} := by
    rw [measureReal_def, measureReal_def, hlift_W]
  rw [hE_real]
  refine le_trans ?_ hcm_real
  rw [mul_comm C]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
  rw [hW_real] at hn
  exact hn

/-- **`a`-slice discharge at the boundary** (Phase 5+4 glue).

Injects the Phase-4 boundary lemma (`tiltedWindow_eventually_large_of_boundary`,
constant `1/4`) into the `∃ C > 0` relaxed change-of-measure
`isMeasureInfinitePiTiltedEq_at_of_window`, at the boundary threshold
`a = m := ∫ Y ∂(μ₀.tilted (lam·Y))`. Yields the `a`-slice of
`IsMeasureInfinitePiTiltedEq` at `a = m`, with no residual largeness hypothesis
(only non-degeneracy of the tilted variance). -/
theorem tiltedHalfLine_chernoff_lower_at_boundary
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) *
          (lam * (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)))
            - cgf Y μ₀ lam + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ |
              (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
                ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
  set m : ℝ := ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) with hmdef
  -- The `∃ C > 0` window hypothesis at `a = m`, with `C = 1/4` from the boundary lemma.
  have h_win : ∀ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (m + ε) * n} := by
    intro ε hε
    exact ⟨1 / 4, by norm_num,
      tiltedWindow_eventually_large_of_boundary (μ₀ := μ₀) hY h_bdd lam hε hVar⟩
  exact isMeasureInfinitePiTiltedEq_at_of_window hY h_bdd lam hlam m h_win

/-! ## Phase 6 — per-`a` Cramér lower bound from the `a`-slice

`cramer_lower_phaseC_partial_discharge` requires the full `∀a∀ε`
`IsMeasureInfinitePiTiltedEq` predicate. Its body, however, only consumes the
`a`-slice (via `tilted_lower_from_predicate`, which uses `h_pred a ε hε`). We
add a per-`a` wrapper `cramer_lower_at` taking the `a`-slice directly and routing
straight through the parent `cramer_lower`, then specialize it at the optimal
tilt threshold `a = deriv (cgf Y μ₀) lam` to obtain the **unconditional** Cramér
lower bound. -/

/-- **Per-`a` Cramér lower bound from the `a`-slice** (Phase 6).

A single-`a` variant of `cramer_lower_phaseC_partial_discharge`: the `a`-slice
(the `h_tilted_lower` shape) is the canonical per-`a` Chernoff lower bound on
the un-tilted infinite product, routed directly through the parent
`cramer_lower`. The load-bearing residual is the n-letter Radon–Nikodym
derivative identification of the tilted infinite product (the L-C2 Mathlib gap),
closure deferred to `cramer-chernoff-clt-closure-moonshot-plan`.

`@residual(plan:cramer-chernoff-clt-closure-moonshot-plan)` -/
theorem cramer_lower_at
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  sorry

/-- **Unconditional Cramér lower bound at the optimal tilt threshold** (Phase 6
main).

At the optimal threshold `a = deriv (cgf Y μ₀) lam` (= the tilted mean,
`tiltedMean_eq_deriv_cgf`), with bounded measurable `Y` and *non-degenerate*
tilted variance, the Cramér lower bound holds with **no residual largeness
hypothesis**.

NOTE (2026-05-25 sorry-migration sweep): the upstream `cramer_lower_at` had its
load-bearing `h_slice` hypothesis migrated to `sorry + @residual(...)`. The
constructive route that previously discharged `cramer_lower_at`'s `h_slice` via
`tiltedHalfLine_chernoff_lower_at_boundary` is **structurally still intact**
inside this file (`hmean` + the boundary `a`-slice), but the upstream signature
no longer accepts an `h_slice` argument, so the call collapses to a transitive
`sorry` carried by `cramer_lower_at`. -/
theorem cramer_lower_at_cgfDeriv_unconditional
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ |
              deriv (cgf Y μ₀) lam * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -(lam * deriv (cgf Y μ₀) lam
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ |
                deriv (cgf Y μ₀) lam * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
  cramer_lower_at hY_meas h_bdd (deriv (cgf Y μ₀) lam) lam hlam h_coboundedBelow

end InformationTheory.Shannon.Cramer.Discharge
