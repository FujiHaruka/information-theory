import InformationTheory.Shannon.MeasurePiTiltedFactorization
import InformationTheory.Shannon.Cramer.LC2DischargeExt
import Mathlib.Probability.ProductMeasure
import InformationTheory.Meta.EntryPoint

/-!
# Cramér boundary-closure upstream module (cycle-break hoist target)

This file hoists the `IsMeasureInfinitePiTiltedEq` predicate (formerly in
`InformationTheory/Draft/Shannon/CramerLC2PhaseC.lean`) together with the seven
Phase-2/3/4 change-of-measure / tilted-LLN-window theorems (formerly in
`InformationTheory/Draft/Shannon/InfinitePiTiltedChangeOfMeasure.lean`) into a
single **upstream** module that does NOT import `CramerLC2PhaseC.lean`.

## Why this module exists (import-cycle break)

The CLT-boundary headline
`InformationTheory.Shannon.CramerCltBoundary.cramer_lower_boundary_unconditional`
(in `CramerCltBoundaryClosure.lean`) is forward-independent of the two root
sorries `cramer_lower_phaseC_partial_discharge` (root A) and `cramer_lower`
(root B), so it can be used to discharge them. But discharging root A in place
needs `CramerLC2PhaseC.lean` to import the headline file, while the headline file
previously imported `InfinitePiTiltedChangeOfMeasure.lean`, which imports
`CramerLC2PhaseC.lean` — an import cycle.

Hoisting the eight declarations the headline forward-depends on (the
`IsMeasureInfinitePiTiltedEq` def plus the seven window/change-of-measure
theorems) into this upstream module breaks the cycle: the new linear DAG is

```
Cramer → CramerBoundaryUpstream → CramerCltBoundaryClosure
       → CramerLC2PhaseC → InfinitePiTiltedChangeOfMeasure
```

All hoisted declarations are sorry-free and were moved verbatim. No new proof is
introduced here (pure wiring). Closure plan: `cramer-root-wiring-plan`.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Phase C-1 — n-letter RN-deriv identification predicate (hoisted) -/

/-- **Cramér n-letter change-of-measure predicate** (Mathlib gap abstraction).

Captures the missing Mathlib compatibility lemma
`Measure.infinitePi (fun _ => μ₀.tilted (lam * Y ·)) ↔ (Measure.infinitePi μ₀).tilted (∑ lam * Y ∘ eval i)`
on cylinders of width `n`, in the form usable as input to Cramér's lower-bound
change-of-measure step.

The intended interpretation: for every `n` and every measurable event
`E ⊆ {ω | a·n ≤ ∑ i ∈ Finset.range n, Y (ω i)}`, the un-tilted product measure
of `E` admits the Chernoff-style lower bound
`exp(-n · (lam · a − Λ(lam))) · μ_tilt(E) − o(1) ≤ μ.real E`,
where `μ_tilt := Measure.infinitePi (fun _ => μ₀.tilted (lam * Y ·))` and
`Λ := cgf Y μ₀`.

In the textbook setting this follows from `(dμ_tilt / dμ)|_{cylinder n}
= exp(lam · ∑ Y(ω_i) − n·Λ(lam))`, but the n-letter RN-deriv identification is
not yet in Mathlib.

HOISTED 2026-06-11 from `CramerLC2PhaseC.lean:102` (`cramer-root-wiring-plan`
Phase A a1, cycle-break). Verbatim move, no proof change. -/
def IsMeasureInfinitePiTiltedEq (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a ε : ℝ, 0 < ε →
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}

/-! ## Phase 2 — cylinder lift (hoisted) -/

/-- **Cylinder lift**: an event over the first `n` coordinates of the infinite
product, expressed via a predicate on the partial sum, has `infinitePi` mass
equal to the corresponding `Measure.pi (Fin n)` mass. Works for any constant
factor `ν` (apply with `ν = μ₀` and `ν = μ₀.tilted ...`). -/
theorem infinitePi_partialSum_event_eq_pi {ν : Measure Ω₀} [IsProbabilityMeasure ν]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (n : ℕ) (P : ℝ → Prop)
    (hP : MeasurableSet {r : ℝ | P r}) :
    (Measure.infinitePi (fun _ : ℕ => ν))
        {ω : ℕ → Ω₀ | P (∑ i ∈ Finset.range n, Y (ω i))}
      = (Measure.pi (fun _ : Fin n => ν))
          {x : Fin n → Ω₀ | P (∑ i, Y (x i))} := by
  classical
  -- The cylinder set on the subtype `↥(Finset.range n)`.
  set S : Set (∀ i : ↥(Finset.range n), Ω₀) :=
    {f | P (∑ j, Y (f j))} with hS
  -- Measurability of `S`.
  have hSmeas : MeasurableSet S := by
    have hfun : Measurable (fun f : ∀ i : ↥(Finset.range n), Ω₀ => ∑ j, Y (f j)) :=
      Finset.measurable_sum _ (fun j _ => hY.comp (measurable_pi_apply j))
    exact hfun hP
  -- The infinite event is the preimage of `S` under the `range n` restriction.
  have hpre : {ω : ℕ → Ω₀ | P (∑ i ∈ Finset.range n, Y (ω i))}
      = (Finset.range n).restrict ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS]
    rw [← Finset.sum_coe_sort (Finset.range n) (fun i => Y (ω i))]
    rfl
  rw [hpre, ← Measure.map_apply (Finset.measurable_restrict _) hSmeas,
    Measure.infinitePi_map_restrict]
  -- Reindex the subtype product `↥(range n)` to `Fin n` via `piCongrLeft`.
  set e : Fin n ≃ ↥(Finset.range n) :=
    (Finset.equivFinOfCardEq (Finset.card_range n)).symm with he
  have hmp := measurePreserving_piCongrLeft (α := fun _ : ↥(Finset.range n) => Ω₀)
      (fun _ : ↥(Finset.range n) => ν) e
  rw [← hmp.measure_preimage_emb (MeasurableEquiv.measurableEmbedding _) S]
  -- The preimage event agrees with the `Fin n` event after reindexing.
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, hS,
    MeasurableEquiv.coe_piCongrLeft]
  rw [← e.sum_comp (fun j : ↥(Finset.range n) => Y ((Equiv.piCongrLeft
    (fun _ : ↥(Finset.range n) => Ω₀) e) x j))]
  refine iff_of_eq (congrArg P (Finset.sum_congr rfl (fun j _ => ?_)))
  rw [Equiv.piCongrLeft_apply_apply]

/-! ## Phase 3 — finite change-of-measure lower bound (hoisted) -/

/-- **Finite change-of-measure lower bound** (Phase 3, `Measure.pi` level).

For `lam ≥ 0`, on the window `W_n := {x | a·n ≤ ∑ Y(x i) < (a+ε)·n}` the
un-tilted product mass of the half-line event `E_n := {x | a·n ≤ ∑ Y(x i)}` is
bounded below by `exp(-n·(lam·a − Λ + lam·ε))` times the tilted product mass of
`W_n`, where `Λ = cgf Y μ₀ lam`. The density `d(pi μ₀)/d(pi μ_tilt)` is
`exp(−lam·∑Y + n·Λ)`, bounded below on `W_n` by `exp(−lam(a+ε)n + nΛ)`.

@audit:ok (2026-06-11 independent honesty audit: sorryAx-free machine-confirmed;
signature verbatim-identical to the pre-hoist version, genuine density-bound proof,
honesty-neutral relocation.) -/
theorem change_of_measure_lower_bound_pi {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a ε lam : ℝ) (hlam : 0 ≤ lam) :
    ENNReal.ofReal (Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε)))
        * (Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω)))
            {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i) ∧ ∑ i, Y (x i) < (a + ε) * n}
      ≤ (Measure.pi (fun _ : Fin n => μ₀))
            {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i)} := by
  classical
  -- Notation: single-coordinate partition function `Z₁ = ∫ exp(lam·Y) dμ₀`.
  set Z₁ : ℝ := ∫ ω, Real.exp (lam * Y ω) ∂μ₀ with hZ₁
  have hint : Integrable (fun ω => Real.exp (lam * Y ω)) μ₀ :=
    Cramer.integrable_exp_mul_of_bounded hY h_bdd lam
  have hZ₁_pos : 0 < Z₁ := mgf_pos hint
  have hcgf : cgf Y μ₀ lam = Real.log Z₁ := rfl
  -- The two events; `W_n ⊆ E_n`.
  set W : Set (Fin n → Ω₀) :=
    {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i) ∧ ∑ i, Y (x i) < (a + ε) * n} with hW
  set E : Set (Fin n → Ω₀) := {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i)} with hE
  have hWmeas : MeasurableSet W := by
    have hsum : Measurable (fun x : Fin n → Ω₀ => ∑ i, Y (x i)) :=
      Finset.measurable_sum _ (fun i _ => hY.comp (measurable_pi_apply i))
    exact (measurableSet_le measurable_const hsum).inter
      (measurableSet_lt hsum measurable_const)
  have hWsubE : W ⊆ E := fun x hx => hx.1
  -- Step 1: rewrite the tilted product as the tilt of the un-tilted product.
  rw [← pi_tilted_sum_eq_pi_tilted (n := n) (μ₀ := μ₀) hY lam,
    tilted_apply' _ _ hWmeas]
  -- Normalization constant `Z_n = Z₁ ^ n`.
  have hZn : (∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : Fin n => μ₀)))
      = Z₁ ^ n := by rw [hZ₁]; exact integral_exp_sum_pi_eq_pow lam
  rw [hZn]
  -- Step 2: pointwise upper bound of the density on `W` by the constant
  -- `exp(n·(lam(a+ε) − Λ))`.
  set c : ℝ := Real.exp ((n : ℝ) * (lam * (a + ε) - Real.log Z₁)) with hc
  have hdens_le : ∀ x ∈ W,
      ENNReal.ofReal (Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ n) ≤ ENNReal.ofReal c := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    rw [hc]
    -- `exp(∑λY)/Z₁^n = exp(λ·∑Y − n·log Z₁) ≤ exp(λ(a+ε)n − n log Z₁)`.
    have hsum_lt : ∑ i, lam * Y (x i) ≤ lam * ((a + ε) * n) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (le_of_lt hx.2) hlam
    have hden_eq : Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ n
        = Real.exp (∑ i, lam * Y (x i) - (n : ℝ) * Real.log Z₁) := by
      rw [Real.exp_sub, ← Real.log_pow, Real.exp_log (by positivity)]
    rw [hden_eq]
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) * (lam * (a + ε) - Real.log Z₁)
        = lam * ((a + ε) * n) - (n : ℝ) * Real.log Z₁ := by ring
    rw [this]
    linarith [hsum_lt]
  -- Step 3: bound the set-lintegral by the constant times the measure of `W`.
  have hstep2 :
      ∫⁻ x in W, ENNReal.ofReal (Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ n)
          ∂(Measure.pi (fun _ : Fin n => μ₀))
        ≤ ENNReal.ofReal c * (Measure.pi (fun _ : Fin n => μ₀)) W := by
    calc ∫⁻ x in W, ENNReal.ofReal (Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ n)
            ∂(Measure.pi (fun _ : Fin n => μ₀))
        ≤ ∫⁻ _ in W, ENNReal.ofReal c ∂(Measure.pi (fun _ : Fin n => μ₀)) :=
          setLIntegral_mono' hWmeas hdens_le
      _ = ENNReal.ofReal c * (Measure.pi (fun _ : Fin n => μ₀)) W := by
          rw [setLIntegral_const]
  -- Step 4: combine. The LHS coefficient times `(pi μ_tilt) W` rewritten via
  -- `tilted_apply'` is exactly the set-lintegral; we bound it and use `W ⊆ E`.
  refine le_trans ?_ (measure_mono (μ := Measure.pi (fun _ : Fin n => μ₀)) hWsubE)
  -- Goal: ofReal(exp(-n(λa-Λ+λε))) * ∫⁻_W density ≤ (pi μ₀) W.
  calc ENNReal.ofReal (Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε)))
          * ∫⁻ x in W, ENNReal.ofReal (Real.exp (∑ i, lam * Y (x i)) / Z₁ ^ n)
              ∂(Measure.pi (fun _ : Fin n => μ₀))
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε)))
          * (ENNReal.ofReal c * (Measure.pi (fun _ : Fin n => μ₀)) W) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε)) * c)
          * (Measure.pi (fun _ : Fin n => μ₀)) W := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ = (Measure.pi (fun _ : Fin n => μ₀)) W := by
        have hprod : Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε)) * c = 1 := by
          rw [hc, hcgf, ← Real.exp_add]
          rw [show -(n : ℝ) * (lam * a - Real.log Z₁ + lam * ε)
              + (n : ℝ) * (lam * (a + ε) - Real.log Z₁) = 0 by ring]
          exact Real.exp_zero
        rw [hprod, ENNReal.ofReal_one, one_mul]

/-! ## Phase 4 — residual predicate + reduction to `IsMeasureInfinitePiTiltedEq` (hoisted) -/

/-- **Residual predicate** (Phase 4, W-3 reduction): the tilted infinite-product
window mass is eventually at least `1/2`. This is the *only* piece left after the
change-of-measure machinery (Phases 1–3) is discharged; it holds precisely when
the tilted mean `∫ Y ∂μ₀.tilted` lies in the window `[a, a+ε)`, which is the
Cramér optimality condition `∫ Y ∂μ₀.tilted = a`. It follows from the existing
tilted-side LLN `tilted_lln_in_probability_real` under that condition. -/
def IsTiltedWindowEventuallyLarge (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n}

/-- **W-3 residual reduction**: the residual window predicate implies the full
n-letter RN-deriv predicate `IsMeasureInfinitePiTiltedEq`. The change-of-measure
lower bound (Phase 3) plus the cylinder lift (Phase 2) reduce the predicate to
the eventual largeness of the tilted window mass, discharged here with `C = 1/2`.

@audit:ok (2026-06-11 independent honesty audit: sorryAx-free `[propext,
Classical.choice, Quot.sound]` machine-confirmed; signature matches the pre-hoist
version verbatim (honesty-neutral relocation). `h_res` is genuinely consumed
(`filter_upwards [h_res a ε hε]`) to supply the window-mass input, not a vacuous
bundle.) -/
@[entry_point]
theorem isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) (hlam : 0 ≤ lam)
    (h_res : IsTiltedWindowEventuallyLarge μ₀ Y lam) :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam := by
  haveI hp : IsProbabilityMeasure (μ₀.tilted (fun ω => lam * Y ω)) :=
    isProbabilityMeasure_tilted_of_bounded hY h_bdd lam
  intro a ε hε
  refine ⟨1 / 2, by norm_num, ?_⟩
  -- The tilted window mass is eventually ≥ 1/2.
  filter_upwards [h_res a ε hε] with n hn
  -- Cylinder lift, un-tilted side: half-line event.
  have hPE : MeasurableSet {r : ℝ | a * (n : ℝ) ≤ r} := measurableSet_le measurable_const measurable_id
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
  have hfin_t : (Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω)))
      {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i) ∧ ∑ i, Y (x i) < (a + ε) * n} ≠ ⊤ :=
    (measure_ne_top _ _)
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
  -- Assemble: 1/2 · exp(...) ≤ exp(...) · (tilted window).real ≤ (un-tilted half-line).real.
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
  rw [mul_comm ((1 : ℝ) / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
  rw [hW_real] at hn
  exact hn

/-! ## Per-instance window largeness from interior of the tilted mean (hoisted) -/

/-- **Per-instance tilted window mass → 1** (interior case).

The `∀a∀ε` predicate `IsTiltedWindowEventuallyLarge` is *false* in general (for
`a` far from the tilted mean the window has vanishing mass). The meaningful
statement is the per-instance one: when the tilted mean
`m := ∫ Y ∂(μ₀.tilted (lam·Y))` lies strictly inside the window `(a, a+ε)`, the
tilted infinite-product mass of `{ω | a·n ≤ ∑_{i<n} Y(ω i) < (a+ε)·n}` tends to
`1`.

Proof: with `δ := min (m − a) (a + ε − m) > 0`, the in-probability LLN
(`tilted_lln_in_probability_real`) sends the bad-set mass `{|S̄_n − m| ≥ δ}` to
`0`, so the complement `{|S̄_n − m| < δ}` mass → 1; that complement is contained
in the window for `n ≥ 1`, and the window mass is ≤ 1, so it is squeezed to 1. -/
theorem tiltedWindow_eventually_tendsto_one
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {a ε : ℝ}
    (h_lo : a < ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)))
    (h_hi : ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) < a + ε) :
    Tendsto (fun n : ℕ =>
        (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n}) atTop (𝓝 1) := by
  haveI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    isProbabilityMeasure_infinitePi_tilted_of_bounded hY h_bdd lam
  set μ : Measure (ℕ → Ω₀) :=
    Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) with hμ
  set m : ℝ := ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) with hm
  -- The half-window radius `δ`.
  set δ : ℝ := min (m - a) (a + ε - m) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  -- The bad set and the window event, per `n`.
  set bad : ℕ → Set (ℕ → Ω₀) := fun n =>
    {ω | δ ≤ |(∑ i ∈ Finset.range n, Y (ω i)) / n - m|} with hbad
  set window : ℕ → Set (ℕ → Ω₀) := fun n =>
    {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
      ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n} with hwindow
  -- Measurability of the bad set.
  have hbad_meas : ∀ n, MeasurableSet (bad n) := fun n =>
    measurableSet_le measurable_const
      ((((Finset.measurable_sum _ (fun i _ => hY.comp (measurable_pi_apply i))).div_const
        (n : ℝ)).sub measurable_const).norm)
  -- LLN: bad-set mass → 0.
  have h_bad : Tendsto (fun n : ℕ => μ.real (bad n)) atTop (𝓝 0) :=
    tilted_lln_in_probability_real hY h_bdd lam hδ
  -- Complement mass → 1.
  have h_compl : Tendsto (fun n : ℕ => μ.real (bad n)ᶜ) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - μ.real (bad n)) atTop (𝓝 (1 - 0)) :=
      h_bad.const_sub 1
    rw [sub_zero] at h1
    refine h1.congr (fun n => ?_)
    rw [probReal_compl_eq_one_sub (hbad_meas n)]
  -- Inclusion: complement of bad ⊆ window, for `n ≥ 1`.
  have h_sub : ∀ n : ℕ, 1 ≤ n → (bad n)ᶜ ⊆ window n := by
    intro n hn ω hω
    simp only [hbad, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_lt] at hω
    -- `m - δ < S̄_n < m + δ`, hence `a < S̄_n < a + ε`.
    have hδle1 : δ ≤ m - a := min_le_left _ _
    have hδle2 : δ ≤ a + ε - m := min_le_right _ _
    set S : ℝ := ∑ i ∈ Finset.range n, Y (ω i) with hS
    have hlo : a ≤ S / n := by linarith [hω.1]
    have hhi : S / n < a + ε := by linarith [hω.2]
    simp only [hwindow, Set.mem_setOf_eq]
    refine ⟨(le_div_iff₀ hnpos).mp hlo, (div_lt_iff₀ hnpos).mp hhi⟩
  -- Squeeze the window mass between the complement mass (→1, eventually ≤) and 1.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_compl tendsto_const_nhds ?_ ?_
  · -- eventually `μ.real (bad n)ᶜ ≤ μ.real (window n)`
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact measureReal_mono (h_sub n hn) (measure_ne_top _ _)
  · -- always `μ.real (window n) ≤ 1`
    exact Eventually.of_forall (fun n => measureReal_le_one)

/-- **Per-instance tilted window mass ≥ 1/2** (interior case, `≥ 1/2` corollary).

Immediate from `tiltedWindow_eventually_tendsto_one` and `1/2 < 1`: the window
mass is eventually ≥ 1/2. This is the per-instance replacement for the
(generally false) `∀a∀ε` `IsTiltedWindowEventuallyLarge` predicate. -/
theorem tiltedWindow_eventually_large_of_interior
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {a ε : ℝ}
    (h_lo : a < ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)))
    (h_hi : ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) < a + ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n} :=
  (tiltedWindow_eventually_tendsto_one hY h_bdd lam h_lo h_hi).eventually_const_le
    (by norm_num)

/-! ## cgf-calculus form of the interior window condition (hoisted) -/

/-- **Tilted mean = cgf derivative** (cgf-derivative bridge).

For a bounded measurable `Y` under a probability measure `μ₀`, the tilted mean
`∫ Y ∂(μ₀.tilted (lam·Y))` equals the first derivative of the cgf at `lam`:
`∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) = deriv (cgf Y μ₀) lam`.

This is Mathlib's `ProbabilityTheory.integral_tilted_mul_self`, whose interior
side condition `lam ∈ interior (integrableExpSet Y μ₀)` is discharged for free
here: boundedness of `Y` makes `exp (t·Y)` integrable for *every* `t`
(`Cramer.integrable_exp_mul_of_bounded`), so `integrableExpSet Y μ₀ = Set.univ`
and its interior is again `Set.univ`.

@audit:ok (2026-06-11 independent honesty audit: sorryAx-free machine-confirmed;
signature verbatim-identical to the pre-hoist version, honesty-neutral relocation.) -/
theorem tiltedMean_eq_deriv_cgf
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) = deriv (cgf Y μ₀) lam := by
  have h_univ : integrableExpSet Y μ₀ = Set.univ := by
    refine Set.eq_univ_of_forall (fun t => ?_)
    exact Cramer.integrable_exp_mul_of_bounded hY h_bdd t
  have hmem : lam ∈ interior (integrableExpSet Y μ₀) := by
    rw [h_univ, interior_univ]
    exact Set.mem_univ lam
  exact integral_tilted_mul_self hmem

end InformationTheory.Shannon.Cramer.Discharge
