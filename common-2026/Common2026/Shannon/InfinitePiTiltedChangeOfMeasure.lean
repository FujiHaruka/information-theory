import Common2026.Shannon.MeasurePiTiltedFactorization
import Common2026.Shannon.CramerLC2DischargeExt
import Common2026.Shannon.CramerLC2PhaseC
import Mathlib.Probability.ProductMeasure

/-!
# infinitePi-tilted change-of-measure (Cramér Phase C, Phases 2–4)

This file builds on the finite `Measure.pi` tilt factorization
(`MeasurePiTiltedFactorization.pi_tilted_sum_eq_pi_tilted`) to discharge — or
maximally shrink — the `IsMeasureInfinitePiTiltedEq` predicate of
`Common2026/Shannon/CramerLC2PhaseC.lean`.

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

/-! ## Phase 2 — cylinder lift -/

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

/-! ## Phase 3 — finite change-of-measure lower bound -/

/-- **Finite change-of-measure lower bound** (Phase 3, `Measure.pi` level).

For `lam ≥ 0`, on the window `W_n := {x | a·n ≤ ∑ Y(x i) < (a+ε)·n}` the
un-tilted product mass of the half-line event `E_n := {x | a·n ≤ ∑ Y(x i)}` is
bounded below by `exp(-n·(lam·a − Λ + lam·ε))` times the tilted product mass of
`W_n`, where `Λ = cgf Y μ₀ lam`. The density `d(pi μ₀)/d(pi μ_tilt)` is
`exp(−lam·∑Y + n·Λ)`, bounded below on `W_n` by `exp(−lam(a+ε)n + nΛ)`. -/
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

/-! ## Phase 4 — residual predicate + reduction to `IsMeasureInfinitePiTiltedEq` -/

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
the eventual largeness of the tilted window mass, discharged here with `C = 1/2`. -/
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

/-! ## Phase 4 — end-to-end Cramér lower bound from the residual predicate -/

/-- **Cramér lower bound, residual discharge**. The `h_pred`
(`IsMeasureInfinitePiTiltedEq`) hypothesis of `cramer_lower_phaseC_partial_discharge`
is replaced by the strictly smaller residual window predicate
`IsTiltedWindowEventuallyLarge`. The full change-of-measure machinery (Phases
1–3 of `infinitepi-tilted-rn-discharge`) is discharged here; the only remaining
input is the eventual `≥ 1/2` largeness of the tilted-side window mass, which is
a one-sided LLN/boundary statement (`∫ Y ∂μ₀.tilted ∈ [a, a+ε)`). -/
theorem cramer_lower_phaseC_residual_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_res : IsTiltedWindowEventuallyLarge μ₀ Y lam) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
  cramer_lower_phaseC_partial_discharge hY_meas h_bdd a lam hlam h_coboundedBelow
    (isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge hY_meas h_bdd lam hlam h_res)

/-! ## Per-instance window largeness from interior of the tilted mean -/

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

end InformationTheory.Shannon.Cramer.Discharge
