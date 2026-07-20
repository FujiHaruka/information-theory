import InformationTheory.Shannon.Portfolio.StationaryWinftyAEP
import InformationTheory.Probability.TwoSidedExtension.Backward

/-!
# Concrete two-sided market instantiation of the growing-memory `W_∞` AEP (Cover–Thomas §16.5)

The abstract Theorem 16.5.1 headline
`growingMemory_logWealth_tendsto_condOptGrowthInfty` is stated for an arbitrary increasing
filtration `ℱ` and measure-preserving map `T`, conditional on two measurability-only shift/past
*coherence* hypotheses (`hcoh`, `hcoh_inf`) linking the filtration to the shift orbit. This file
discharges both coherences for the concrete two-sided market — sequence space
`Ω = ∀ _ : ℤ, Fin m → ℝ`, shift `T = shiftZ`, coordinate-0 price relative `X = coord0`, and the
finite-past filtration `ℱ = pastFiltration` — and produces the concrete headline
`growingMemory_logWealth_tendsto_condOptGrowthInfty_concrete` with the two coherences removed
(every remaining hypothesis is a market-regularity/ergodicity precondition).

The discharge is bounded plumbing: each coherence component is a finite-window function pulled back
through a shift, so it factors as `g ∘ shiftZ^[k+1]` with `g` measurable w.r.t. the negative-past
σ-algebra, using the generic comap-through-shift factorization.
-/

namespace InformationTheory.Shannon.Portfolio

open InformationTheory.Shannon.TwoSided MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

variable {m : ℕ}

/-! ## Local shift-iterate helpers

Replicated from the (privately scoped) engine in `SMB/AlgoetCover/TwoSidedRatio.lean` to keep the
import surface light (`shiftZ_iterate_apply` is public in `Core`, so it is used directly). -/

private lemma shiftZSymm_shiftZ' (x : ∀ _ : ℤ, Fin m → ℝ) :
    shiftZSymm (shiftZ x) = x := by
  funext i
  change (shiftZ x) (i - 1) = x i
  change x ((i - 1) + 1) = x i
  congr 1; ring

private lemma shiftZSymm_iterate_shiftZ_iterate' (n : ℕ) (x : ∀ _ : ℤ, Fin m → ℝ) :
    (shiftZSymm^[n]) (shiftZ^[n] x) = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [shiftZSymm_shiftZ']
    exact ih

private lemma shiftZSymm_iterate_apply' (n : ℕ) (y : ∀ _ : ℤ, Fin m → ℝ) (i : ℤ) :
    (shiftZSymm^[n]) y i = y (i - n) := by
  induction n generalizing i with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (shiftZSymm^[k] y) (i - 1) = y (i - (k + 1 : ℕ))
    rw [ih]
    congr 1
    push_cast; ring

/-! ## Coordinate measurability in the past σ-algebras -/

private lemma measurable_coord_pastSigma {p : ℕ} {ℓ : ℤ} (h_lo : -(p : ℤ) ≤ ℓ) (h_hi : ℓ ≤ -1) :
    @Measurable _ _ (pastSigma (α := Fin m → ℝ) p) _
      (fun y : (∀ _ : ℤ, Fin m → ℝ) ↦ y ℓ) :=
  measurable_cylinderEvent_apply (Δ := {i : ℤ | -(p : ℤ) ≤ i ∧ i ≤ -1}) ⟨h_lo, h_hi⟩

private lemma measurable_coord_negPast {ℓ : ℤ} (h_hi : ℓ ≤ -1) :
    @Measurable _ _ (negPastSigma (α := Fin m → ℝ)) _
      (fun y : (∀ _ : ℤ, Fin m → ℝ) ↦ y ℓ) :=
  measurable_cylinderEvent_apply (Δ := {i : ℤ | i ≤ -1}) h_hi

/-! ## Generic comap-through-shift factorization -/

private lemma measurable_comap_of_eq_comp {β : Type*} [MeasurableSpace β]
    (base : MeasurableSpace (∀ _ : ℤ, Fin m → ℝ)) (n : ℕ)
    {f G : (∀ _ : ℤ, Fin m → ℝ) → β}
    (hG : @Measurable _ _ base _ G)
    (hf : f = G ∘ (shiftZ^[n])) :
    @Measurable _ _ (base.comap (shiftZ^[n])) _ f := by
  intro s hs
  exact ⟨G ⁻¹' s, hG hs, by rw [hf]; rfl⟩

/- A finite-window function `h` (measurable w.r.t. the cylinder σ-algebra on `Δ`), read along the
shift at time `i` and pulled back through `shiftZ^[n]`, is measurable w.r.t. `base.comap shiftZ^[n]`
provided every window coordinate `j ∈ Δ`, shifted to `j + i - n`, is `base`-measurable. -/
private lemma stronglyMeasurable_comp_shift_comap
    (base : MeasurableSpace (∀ _ : ℤ, Fin m → ℝ)) (Δ : Set ℤ) (i n : ℕ)
    (h : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ)
    (hh : @Measurable _ _ (cylinderEvents (X := fun _ : ℤ ↦ Fin m → ℝ) Δ) _ h)
    (hbase : ∀ j ∈ Δ, @Measurable _ _ base _
      (fun y : (∀ _ : ℤ, Fin m → ℝ) ↦ y (j + (i : ℤ) - (n : ℤ)))) :
    @StronglyMeasurable _ _ _ (base.comap (shiftZ^[n])) (fun ω ↦ h (shiftZ^[i] ω)) := by
  refine Measurable.stronglyMeasurable ?_
  refine measurable_comap_of_eq_comp base n
    (G := fun y ↦ h (shiftZ^[i] (shiftZSymm^[n] y))) ?_ ?_
  · -- `h ∘ (shiftZ^[i] ∘ shiftZSymm^[n])` is `base`-measurable.
    refine hh.comp ?_
    refine (measurable_cylinderEvents_iff (mα := base)).2 ?_
    intro j hj
    have hcoord :
        (fun y : ∀ _ : ℤ, Fin m → ℝ ↦ (shiftZ^[i] (shiftZSymm^[n] y)) j)
          = (fun y ↦ y (j + (i : ℤ) - (n : ℤ))) := by
      funext y
      rw [shiftZ_iterate_apply, shiftZSymm_iterate_apply']
    rw [hcoord]
    exact hbase j hj
  · funext ω
    change h (shiftZ^[i] ω) = h (shiftZ^[i] (shiftZSymm^[n] (shiftZ^[n] ω)))
    rw [shiftZSymm_iterate_shiftZ_iterate']

-- Coordinate-0 price relative read along the shift: `coord0 (shiftZ^[i] ω) = ω i`, so the pullback
-- through `shiftZ^[n]` is `base.comap shiftZ^[n]`-measurable once coordinate `i - n` is
-- `base`-measurable.
private lemma stronglyMeasurable_coord0_comp_shift_comap
    (base : MeasurableSpace (∀ _ : ℤ, Fin m → ℝ)) (i n : ℕ)
    (hbase : @Measurable _ _ base _
      (fun y : (∀ _ : ℤ, Fin m → ℝ) ↦ y ((i : ℤ) - (n : ℤ)))) :
    @StronglyMeasurable _ _ _ (base.comap (shiftZ^[n]))
      (fun ω ↦ coord0 (shiftZ^[i] ω)) := by
  refine Measurable.stronglyMeasurable ?_
  refine measurable_comap_of_eq_comp base n
    (G := fun y ↦ y ((i : ℤ) - (n : ℤ))) hbase ?_
  funext ω
  change coord0 (shiftZ^[i] ω) = (shiftZ^[n] ω) ((i : ℤ) - (n : ℤ))
  rw [show coord0 (shiftZ^[i] ω) = (shiftZ^[i] ω) 0 from rfl, shiftZ_iterate_apply,
    shiftZ_iterate_apply]
  congr 1
  ring

/-! ## The two coherence discharges -/

private lemma coherence_lower
    (bstar : ℕ → (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ)
    (hbstar_meas : ∀ k, StronglyMeasurable[(pastFiltration (α := Fin m → ℝ)) k] (bstar k)) :
    ∀ (K : ℕ), ∀ k, ∀ i, K ≤ i → i ≤ k →
      StronglyMeasurable[((pastFiltration (α := Fin m → ℝ)) (k + 1)).comap (shiftZ^[k + 1])]
        (fun ω ↦ coord0 (shiftZ^[i] ω)) ∧
      StronglyMeasurable[((pastFiltration (α := Fin m → ℝ)) (k + 1)).comap (shiftZ^[k + 1])]
        (fun ω ↦ bstar i (shiftZ^[i] ω)) ∧
      StronglyMeasurable[((pastFiltration (α := Fin m → ℝ)) (k + 1)).comap (shiftZ^[k + 1])]
        (fun ω ↦ bstar K (shiftZ^[i] ω)) := by
  intro K k i hKi hik
  refine ⟨?_, ?_, ?_⟩
  · -- coord0 component
    exact stronglyMeasurable_coord0_comp_shift_comap (pastSigma (k + 1)) i (k + 1)
      (measurable_coord_pastSigma (by omega) (by omega))
  · -- bstar i component
    refine stronglyMeasurable_comp_shift_comap (pastSigma (k + 1))
      {j : ℤ | -(i : ℤ) ≤ j ∧ j ≤ -1} i (k + 1) (bstar i) (hbstar_meas i).measurable ?_
    intro j hj
    exact measurable_coord_pastSigma (by simp only [Set.mem_setOf_eq] at hj; omega)
      (by simp only [Set.mem_setOf_eq] at hj; omega)
  · -- bstar K component (uses `K ≤ i`)
    refine stronglyMeasurable_comp_shift_comap (pastSigma (k + 1))
      {j : ℤ | -(K : ℤ) ≤ j ∧ j ≤ -1} i (k + 1) (bstar K) (hbstar_meas K).measurable ?_
    intro j hj
    exact measurable_coord_pastSigma (by simp only [Set.mem_setOf_eq] at hj; omega)
      (by simp only [Set.mem_setOf_eq] at hj; omega)

private lemma coherence_upper
    (bstar : ℕ → (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ)
    (bstarInf : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ)
    (hbstar_meas : ∀ k, StronglyMeasurable[(pastFiltration (α := Fin m → ℝ)) k] (bstar k))
    (hInf_meas : StronglyMeasurable[⨆ j, (pastFiltration (α := Fin m → ℝ)) j] bstarInf) :
    ∀ k, ∀ i, i ≤ k →
      StronglyMeasurable[(⨆ j, (pastFiltration (α := Fin m → ℝ)) j).comap (shiftZ^[k + 1])]
        (fun ω ↦ coord0 (shiftZ^[i] ω)) ∧
      StronglyMeasurable[(⨆ j, (pastFiltration (α := Fin m → ℝ)) j).comap (shiftZ^[k + 1])]
        (fun ω ↦ bstar i (shiftZ^[i] ω)) ∧
      StronglyMeasurable[(⨆ j, (pastFiltration (α := Fin m → ℝ)) j).comap (shiftZ^[k + 1])]
        (fun ω ↦ bstarInf (shiftZ^[i] ω)) := by
  intro k i hik
  have h_iSup : (⨆ j, (pastFiltration (α := Fin m → ℝ)) j) = negPastSigma (α := Fin m → ℝ) := by
    simp only [pastFiltration_apply]; exact iSup_pastSigma_eq_negPastSigma
  rw [h_iSup]
  refine ⟨?_, ?_, ?_⟩
  · -- coord0 component
    exact stronglyMeasurable_coord0_comp_shift_comap negPastSigma i (k + 1)
      (measurable_coord_negPast (by omega))
  · -- bstar i component
    refine stronglyMeasurable_comp_shift_comap negPastSigma
      {j : ℤ | -(i : ℤ) ≤ j ∧ j ≤ -1} i (k + 1) (bstar i) (hbstar_meas i).measurable ?_
    intro j hj
    exact measurable_coord_negPast (by simp only [Set.mem_setOf_eq] at hj; omega)
  · -- bstarInf component (infinite past, `negPastSigma`-measurable)
    have hInf : @Measurable _ _ (negPastSigma (α := Fin m → ℝ)) _ bstarInf := by
      have h := hInf_meas.measurable
      rwa [h_iSup] at h
    refine stronglyMeasurable_comp_shift_comap negPastSigma
      {j : ℤ | j ≤ -1} i (k + 1) bstarInf hInf ?_
    intro j hj
    exact measurable_coord_negPast (by simp only [Set.mem_setOf_eq] at hj; omega)

/-! ## Concrete headline -/

/-- Growing-memory `W_∞` AEP (Cover–Thomas Theorem 16.5.1) for the concrete two-sided market: the
growing-memory log-wealth average converges almost surely to the infinite-past optimal growth rate
`W_∞ = condOptGrowthInfty`. The sequence space is `Ω = ∀ _ : ℤ, Fin m → ℝ`, the dynamics is the
two-sided shift `shiftZ`, the per-epoch price relative is the coordinate-0 projection `coord0`, and
the filtration is the finite-past `pastFiltration`. The two shift/past coherences of the abstract
statement are discharged internally; all remaining hypotheses are market-regularity/ergodicity
preconditions (measure preservation, ergodicity, simplex membership, positivity, integrability,
conditional dominance).
@audit:ok -/
theorem growingMemory_logWealth_tendsto_condOptGrowthInfty_concrete
    (μ : Measure (∀ _ : ℤ, Fin m → ℝ)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (shiftZ (α := Fin m → ℝ)) μ μ)
    (hT_erg : Ergodic (shiftZ (α := Fin m → ℝ)) μ) [Nonempty (Fin m)]
    (hpos : ∀ (ω : ∀ _ : ℤ, Fin m → ℝ), ∀ b ∈ stdSimplex ℝ (Fin m),
      0 < ∑ j, b j * coord0 ω j)
    (hint : ∀ c : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ, Measurable c →
      (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) → Integrable (causalLogReturn coord0 c) μ)
    (bstar : ℕ → (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ)
    (hbstar_meas : ∀ k, StronglyMeasurable[(pastFiltration (α := Fin m → ℝ)) k] (bstar k))
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hbstar_dom : ∀ (k : ℕ) (c : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ),
        StronglyMeasurable[(pastFiltration (α := Fin m → ℝ)) k] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn coord0 c | (pastFiltration (α := Fin m → ℝ)) k]
          ≤ᵐ[μ] μ[causalLogReturn coord0 (bstar k) | (pastFiltration (α := Fin m → ℝ)) k])
    (hint_coord : ∀ i coord,
      Integrable (fun ω : ∀ _ : ℤ, Fin m → ℝ ↦
        coord0 ω coord / (∑ j, bstar i ω j * coord0 ω j)) μ)
    (hUB : ∃ C : ℝ, ∀ c : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ,
      (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn coord0 c) μ → ∫ ω, causalLogReturn coord0 c ω ∂μ ≤ C)
    (bstarInf : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ)
    (hInf_meas : StronglyMeasurable[⨆ j, (pastFiltration (α := Fin m → ℝ)) j] bstarInf)
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m))
    (hint_coord_inf : ∀ i, Integrable (fun ω : ∀ _ : ℤ, Fin m → ℝ ↦
      coord0 ω i / (∑ j, bstarInf ω j * coord0 ω j)) μ)
    (hInf_dom : ∀ (c : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ),
        StronglyMeasurable[⨆ j, (pastFiltration (α := Fin m → ℝ)) j] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn coord0 c | ⨆ j, (pastFiltration (α := Fin m → ℝ)) j]
          ≤ᵐ[μ] μ[causalLogReturn coord0 bstarInf | ⨆ j, (pastFiltration (α := Fin m → ℝ)) j]) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ growingMemoryLogAvg coord0 bstar (shiftZ (α := Fin m → ℝ)) n ω) atTop
        (𝓝 (condOptGrowthInfty μ coord0 bstar)) :=
  growingMemory_logWealth_tendsto_condOptGrowthInfty μ hT hT_erg
    (pastFiltration (α := Fin m → ℝ)) coord0 measurable_coord0 hpos hint bstar hbstar_meas
    hbstar_simplex hbstar_dom hint_coord hUB (coherence_lower bstar hbstar_meas)
    bstarInf hInf_meas hInf_simplex hint_coord_inf hInf_dom
    (coherence_upper bstar bstarInf hbstar_meas hInf_meas)

end InformationTheory.Shannon.Portfolio
