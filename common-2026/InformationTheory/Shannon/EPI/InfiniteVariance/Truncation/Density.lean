import InformationTheory.Shannon.EPI.Case1.SmoothingLimit
import InformationTheory.Shannon.EPI.Stam.SupplyTwoTime
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Construction

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The sum density is the convolution of the marginal densities:
`(P.map (X + Y)).rnDeriv =ᵐ ofReal (convDensityAdd pX pY)`, where
`pX := (P.map X).rnDeriv volume |>.toReal` and `pY := (P.map Y).rnDeriv volume |>.toReal`. This is
the conditioning-free version of `rnDeriv_map_condTrunc_sum_ae`.
@audit:ok -/
theorem rnDeriv_map_sum_ae (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P) :
    (P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume
      =ᵐ[volume] fun x ↦ ENNReal.ofReal
        (convDensityAdd (fun y ↦ (P.map X).rnDeriv volume y |>.toReal)
          (fun y ↦ (P.map Y).rnDeriv volume y |>.toReal) x) := by
  -- a.c. of the sum law.
  have hXYac : (P.map (fun ω ↦ X ω + Y ω)) ≪ volume := by
    have hconv : P.map (fun ω ↦ X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω ↦ X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  -- density witnesses.
  set pX : ℝ → ℝ := fun y ↦ (P.map X).rnDeriv volume y |>.toReal with hpX
  set pY : ℝ → ℝ := fun y ↦ (P.map Y).rnDeriv volume y |>.toReal with hpY
  set pXY : ℝ → ℝ := fun y ↦ (P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume y |>.toReal with hpXY
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpXY_meas : Measurable pXY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x ↦ ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x ↦ ENNReal.toReal_nonneg
  have hpXY_nn : ∀ x, 0 ≤ pXY x := fun x ↦ ENNReal.toReal_nonneg
  -- withDensity laws (a.c. probability ⇒ recovered by `withDensity_rnDeriv_eq`).
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  haveI : IsProbabilityMeasure (P.map (fun ω ↦ X ω + Y ω)) :=
    Measure.isProbabilityMeasure_map (hX.add hY).aemeasurable
  have mk_law : ∀ (W : Ω → ℝ) (pW : ℝ → ℝ), Measurable W → (P.map W) ≪ volume
      → pW = (fun y ↦ (P.map W).rnDeriv volume y |>.toReal)
      → P.map W = volume.withDensity (fun x ↦ ENNReal.ofReal (pW x)) := by
    intro W pW hWmeas hWac hpW_eq
    haveI : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hWmeas.aemeasurable
    have hcongr : (fun x ↦ ENNReal.ofReal (pW x))
        =ᵐ[volume] (P.map W).rnDeriv volume := by
      filter_upwards [(P.map W).rnDeriv_lt_top volume] with x hx
      rw [hpW_eq]; exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hWac]
  have hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)) :=
    mk_law X pX hX hX_ac hpX
  have hpY_law : P.map Y = volume.withDensity (fun x ↦ ENNReal.ofReal (pY x)) :=
    mk_law Y pY hY hY_ac hpY
  have hpXY_law : P.map (fun ω ↦ X ω + Y ω)
      = volume.withDensity (fun x ↦ ENNReal.ofReal (pXY x)) :=
    mk_law (fun ω ↦ X ω + Y ω) pXY (hX.add hY) hXYac hpXY
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  -- lmasses.
  have hlmass : ∀ (W : Ω → ℝ) (pW : ℝ → ℝ),
      P.map W = volume.withDensity (fun x ↦ ENNReal.ofReal (pW x))
      → (∫⁻ x, ENNReal.ofReal (pW x) ∂volume) = (P.map W) Set.univ := by
    intro W pW hlaw
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hpX_lmass : (∫⁻ x, ENNReal.ofReal (pX x) ∂volume) = 1 := by
    rw [hlmass X pX hpX_law]; exact measure_univ
  have hpY_lmass : (∫⁻ x, ENNReal.ofReal (pY x) ∂volume) = 1 := by
    rw [hlmass Y pY hpY_law]; exact measure_univ
  have hpXY_lmass : (∫⁻ x, ENNReal.ofReal (pXY x) ∂volume) ≠ ⊤ := by
    rw [hlmass (fun ω ↦ X ω + Y ω) pXY hpXY_law]; exact measure_ne_top _ _
  have hkey : pXY =ᵐ[volume] convDensityAdd pX pY :=
    EPIStamSupplyTwoTime.indepSum_density_ae (P := P) X Y hX hY hXY
      pX pY pXY hpX_nn hpX_meas hpY_nn hpY_meas hpX_law hpY_law hpXY_law
      hpXY_nn hpXY_meas hpX_int hpY_int hpXY_lmass hpX_lmass hpY_lmass
  have hrn_ofReal : (P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume
      =ᵐ[volume] fun x ↦ ENNReal.ofReal (pXY x) := by
    filter_upwards [(P.map (fun ω ↦ X ω + Y ω)).rnDeriv_lt_top volume] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  filter_upwards [hrn_ofReal, hkey] with x hx hkx
  rw [hx, hkx]

/-- Positivity of the marginal mass: `P (truncSet X Y n) ≠ 0` implies
`(P.map Z) {r | |r| ≤ n} ≠ 0` for `Z = X` or `Z = Y`, since independence factors
`P (truncSet) = P (X⁻¹ Sn) · P (Y⁻¹ Sn)` and one factor equals `(P.map Z) Sn`.
@audit:ok -/
theorem map_measure_truncBall_ne_zero (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y) {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    (P.map Z) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0 := by
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn :=
    measurableSet_le measurable_norm measurable_const
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  rw [Measure.map_apply hZmeas hSn_meas]
  have hfac : P (truncSet X Y n) = P (X ⁻¹' Sn) * P (Y ⁻¹' Sn) := by
    show P (X ⁻¹' Sn ∩ Y ⁻¹' Sn) = _
    exact hXY.measure_inter_preimage_eq_mul Sn Sn hSn_meas hSn_meas
  rcases hZ with rfl | rfl
  · intro h0; apply hpos; rw [hfac, h0, zero_mul]
  · intro h0; apply hpos; rw [hfac, h0, mul_zero]

/-- Single-component dominating bound for the conditioned marginal density: for a fixed
positive-mass `n₀` and any `n ≥ n₀`, the conditioned density
`p_n := (condTrunc.map Z).rnDeriv volume |>.toReal` is bounded by `C_Z · pZ`, where
`pZ := (P.map Z).rnDeriv volume |>.toReal` and `C_Z := ((P.map Z) {|r| ≤ n₀})⁻¹.toReal`. Reducing
to single-component conditioning gives `p_n =ᵐ (m_n)⁻¹ · 1_Sn · pZ`, and `m_n⁻¹ ≤ m_{n₀}⁻¹ = C_Z`
by monotonicity.
@audit:ok -/
theorem condTrunc_marginal_density_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y) {n₀ n : ℕ} (hn : n₀ ≤ n)
    (hpos₀ : P (truncSet X Y n₀) ≠ 0) :
    ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal
        ≤ (((P.map Z) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal
          * ((P.map Z).rnDeriv volume x).toReal := by
  classical
  set Sn₀ : Set ℝ := {r : ℝ | |r| ≤ (n₀ : ℝ)} with hSn₀_def
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn₀_meas : MeasurableSet Sn₀ := measurableSet_le measurable_norm measurable_const
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  haveI : IsProbabilityMeasure (P.map Z) :=
    Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  -- positive mass at level `n₀` and `n` (the latter by monotone `Sn₀ ⊆ Sn`).
  have hpos_n : P (truncSet X Y n) ≠ 0 := by
    intro h0; exact hpos₀ (measure_mono_null (truncSet_mono hn) h0)
  have hm₀_ne : (P.map Z) Sn₀ ≠ 0 := map_measure_truncBall_ne_zero P hX hY hXY hZ hpos₀
  have hm_ne : (P.map Z) Sn ≠ 0 := map_measure_truncBall_ne_zero P hX hY hXY hZ hpos_n
  set m₀ : ℝ≥0∞ := (P.map Z) Sn₀ with hm₀_def
  set m : ℝ≥0∞ := (P.map Z) Sn with hm_def
  have hm₀_top : m₀ ≠ ∞ := measure_ne_top _ _
  -- `m₀ ≤ m` (Sn₀ ⊆ Sn), hence `m⁻¹ ≤ m₀⁻¹`, hence `(m⁻¹).toReal ≤ (m₀⁻¹).toReal`.
  have hSn₀_sub : Sn₀ ⊆ Sn := by
    intro r hr
    have hnn : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_trans hr hnn
  have hm_le : m₀ ≤ m := measure_mono hSn₀_sub
  have hinv_le : m⁻¹ ≤ m₀⁻¹ := ENNReal.inv_le_inv.mpr hm_le
  have hC_bound : (m⁻¹).toReal ≤ (m₀⁻¹).toReal :=
    ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr hm₀_ne) hinv_le
  -- cond density formula: `(condTrunc.map Z).rnDeriv =ᵐ (cond (P.map Z) Sn).rnDeriv`.
  rw [map_condTrunc_eq_cond_map P hX hY hXY hZ hpos_n]
  have h_rn : (ProbabilityTheory.cond (P.map Z) Sn).rnDeriv volume
      =ᵐ[volume] fun x ↦ m⁻¹ * Sn.indicator ((P.map Z).rnDeriv volume) x :=
    rnDeriv_cond_eq (P.map Z) hSn_meas hm_ne
  filter_upwards [h_rn] with x hx
  rw [hx]
  set pZx : ℝ := ((P.map Z).rnDeriv volume x).toReal with hpZx_def
  have hpZx_nn : 0 ≤ pZx := ENNReal.toReal_nonneg
  by_cases hxs : x ∈ Sn
  · rw [Set.indicator_of_mem hxs (f := (P.map Z).rnDeriv volume), ENNReal.toReal_mul]
    -- `(m⁻¹).toReal * pZx ≤ (m₀⁻¹).toReal * pZx`.
    exact mul_le_mul_of_nonneg_right hC_bound hpZx_nn
  · rw [Set.indicator_of_notMem hxs (f := (P.map Z).rnDeriv volume), mul_zero,
      ENNReal.toReal_zero]
    exact mul_nonneg ENNReal.toReal_nonneg hpZx_nn

/-- Dominating bound `p_n ∗ q_n ≤ C · (pX ∗ pY)` (a.e. `z`, with `C = C_X · C_Y`): for a fixed
positive-mass `n₀` and all `n ≥ n₀`, each conditioned marginal density is bounded by a constant
multiple of the corresponding `P`-marginal (`condTrunc_marginal_density_le`), and monotonicity of
the convolution lifts this to the sum density. Per-`z` integrability of the convolution slice is
supplied by `integrable_prod_iff'` plus `Integrable.prod_right_ae`, and the `Y`-bound is
transported through the measure-preserving map `x ↦ z - x`.
@audit:ok -/
theorem convDensity_condTrunc_le_const_mul (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (_hX_ac : (P.map X) ≪ volume) (_hY_ac : (P.map Y) ≪ volume) {n₀ : ℕ}
    (hpos₀ : P (truncSet X Y n₀) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ᵐ z ∂volume,
      convDensityAdd (fun y ↦ ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal)
        (fun y ↦ ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal) z
        ≤ C * convDensityAdd (fun y ↦ (P.map X).rnDeriv volume y |>.toReal)
            (fun y ↦ (P.map Y).rnDeriv volume y |>.toReal) z := by
  classical
  -- marginal densities of `P` (probability measures, a.c. ⇒ integrable toReal rnDeriv).
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set pX : ℝ → ℝ := fun y ↦ ((P.map X).rnDeriv volume y).toReal with hpX_def
  set pY : ℝ → ℝ := fun y ↦ ((P.map Y).rnDeriv volume y).toReal with hpY_def
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x ↦ ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x ↦ ENNReal.toReal_nonneg
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  -- constants.
  set C_X : ℝ := (((P.map X) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal with hCX_def
  set C_Y : ℝ := (((P.map Y) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal with hCY_def
  have hCX_nn : 0 ≤ C_X := ENNReal.toReal_nonneg
  have hCY_nn : 0 ≤ C_Y := ENNReal.toReal_nonneg
  refine ⟨C_X * C_Y, mul_nonneg hCX_nn hCY_nn, ?_⟩
  -- Step 2 prerequisite: for a.e. `z`, the convolution slice `x ↦ pX x · pY (z - x)`
  -- is integrable. Established via 2D integrability + `Integrable.prod_right_ae`.
  -- Layout: `f (z, x) = pX x · pY (z - x)` (first coord `z`, second coord `x`). This is the
  -- `convKernel_envelope_integrable` shape (`FisherInfoDeBruijnAssembly.lean:791`) with
  -- `K = pY` and the kernel-density being `pX`.
  have hslice_int : ∀ᵐ z ∂volume, Integrable (fun x ↦ pX x * pY (z - x)) volume := by
    -- the 2D integrand `f (z, x) = pX x · pY (z - x)`.
    set f : ℝ × ℝ → ℝ := fun p ↦ pX p.2 * pY (p.1 - p.2) with hf_def
    have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ pX p.2) (volume.prod volume) :=
        (hpX_meas.comp measurable_snd).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ pY (p.1 - p.2)) (volume.prod volume) := by
        have hsub : Measurable (fun p : ℝ × ℝ ↦ p.1 - p.2) := measurable_fst.sub measurable_snd
        exact (hpY_meas.comp hsub).aestronglyMeasurable
      exact h1.mul h2
    have hf_int : Integrable f (volume.prod volume) := by
      rw [integrable_prod_iff' hf_meas]
      refine ⟨?_, ?_⟩
      · -- for each `x`, `z ↦ pX x · pY (z − x)` is integrable (`pX x` constant).
        refine Filter.Eventually.of_forall (fun x ↦ ?_)
        exact (hpY_int.comp_sub_right x).const_mul (pX x)
      · -- `x ↦ ∫ z ‖pX x · pY(z−x)‖ dz = ‖pX x‖ · (∫‖pY‖)` is integrable.
        have heq : (fun x ↦ ∫ z, ‖f (z, x)‖ ∂volume)
            = (fun x ↦ ‖pX x‖ * ∫ z, ‖pY z‖ ∂volume) := by
          funext x
          simp only [hf_def, norm_mul]
          rw [integral_const_mul]
          congr 1
          rw [← integral_sub_right_eq_self (fun z ↦ ‖pY z‖) x]
        rw [heq]
        exact (hpX_int.norm.mul_const _)
    -- slice over the second coord `x` for fixed first `z`.
    exact hf_int.prod_right_ae
  -- the eventual filter: `n ≥ n₀` (positive mass automatic by monotonicity).
  rw [Filter.eventually_atTop]
  refine ⟨n₀, fun n hn ↦ ?_⟩
  -- per-component density bounds (a.e. `x`).
  have hbX : ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map X).rnDeriv volume x).toReal ≤ C_X * pX x :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inl rfl) hn hpos₀
  have hbY : ∀ᵐ y ∂volume,
      (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal ≤ C_Y * pY y :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inr rfl) hn hpos₀
  -- abbreviations for the conditioned marginal densities.
  set pnX : ℝ → ℝ := fun y ↦ (((condTrunc P X Y n).map X).rnDeriv volume y).toReal with hpnX_def
  set pnY : ℝ → ℝ := fun y ↦ (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal with hpnY_def
  have hpnX_nn : ∀ x, 0 ≤ pnX x := fun x ↦ ENNReal.toReal_nonneg
  have hpnY_nn : ∀ x, 0 ≤ pnY x := fun x ↦ ENNReal.toReal_nonneg
  -- combine slice integrability + transported `Y` bound over a.e. `z`.
  filter_upwards [hslice_int] with z hz_int
  -- transport the `Y` bound through the measure-preserving map `x ↦ z - x`.
  have hbY_z : ∀ᵐ x ∂volume, pnY (z - x) ≤ C_Y * pY (z - x) :=
    (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hbY
  -- the integrand bound `pnX x · pnY (z−x) ≤ (C_X·C_Y)·(pX x · pY (z−x))` a.e. `x`.
  have hfg : (fun x ↦ pnX x * pnY (z - x))
      ≤ᵐ[volume] fun x ↦ (C_X * C_Y) * (pX x * pY (z - x)) := by
    filter_upwards [hbX, hbY_z] with x hxX hxY
    have h1 : pnX x * pnY (z - x) ≤ (C_X * pX x) * (C_Y * pY (z - x)) :=
      mul_le_mul hxX hxY (hpnY_nn (z - x)) (le_trans (hpnX_nn x) hxX)
    calc pnX x * pnY (z - x)
        ≤ (C_X * pX x) * (C_Y * pY (z - x)) := h1
      _ = (C_X * C_Y) * (pX x * pY (z - x)) := by ring
  -- nonnegativity of the LHS integrand.
  have hf_nn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun x ↦ pnX x * pnY (z - x) :=
    Filter.Eventually.of_forall (fun x ↦ mul_nonneg (hpnX_nn x) (hpnY_nn (z - x)))
  -- integrability of the RHS integrand.
  have hgi : Integrable (fun x ↦ (C_X * C_Y) * (pX x * pY (z - x))) volume :=
    hz_int.const_mul (C_X * C_Y)
  -- integral monotonicity, then pull out the constant.
  have hmono : (∫ x, pnX x * pnY (z - x) ∂volume)
      ≤ ∫ x, (C_X * C_Y) * (pX x * pY (z - x)) ∂volume :=
    integral_mono_of_nonneg hf_nn hgi hfg
  rw [integral_const_mul] at hmono
  -- rewrite both sides as `convDensityAdd`.
  show convDensityAdd pnX pnY z ≤ (C_X * C_Y) * convDensityAdd pX pY z
  simpa only [convDensityAdd] using hmono

/-- Fixed-`n` version of the dominating bound: for a single positive-mass `n`,
`convDensityAdd pnX pnY ≤ C · convDensityAdd pX pY` (a.e. `z`). Same argument as
`convDensity_condTrunc_le_const_mul` specialized at `n₀ := n`, supplied directly without the
`atTop` eventually wrapper so that callers requiring the bound at a fixed `n` avoid threshold
dependence.
@audit:ok -/
theorem convDensityAdd_condTrunc_le_const_mul_at (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (_hX_ac : (P.map X) ≪ volume) (_hY_ac : (P.map Y) ≪ volume) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z ∂volume,
      convDensityAdd (fun y ↦ ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal)
        (fun y ↦ ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal) z
        ≤ C * convDensityAdd (fun y ↦ (P.map X).rnDeriv volume y |>.toReal)
            (fun y ↦ (P.map Y).rnDeriv volume y |>.toReal) z := by
  classical
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set pX : ℝ → ℝ := fun y ↦ ((P.map X).rnDeriv volume y).toReal with hpX_def
  set pY : ℝ → ℝ := fun y ↦ ((P.map Y).rnDeriv volume y).toReal with hpY_def
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x ↦ ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x ↦ ENNReal.toReal_nonneg
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  set C_X : ℝ := (((P.map X) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal with hCX_def
  set C_Y : ℝ := (((P.map Y) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal with hCY_def
  have hCX_nn : 0 ≤ C_X := ENNReal.toReal_nonneg
  have hCY_nn : 0 ≤ C_Y := ENNReal.toReal_nonneg
  refine ⟨C_X * C_Y, mul_nonneg hCX_nn hCY_nn, ?_⟩
  -- slice integrability `∀ᵐ z, Integrable (x ↦ pX x · pY (z − x))`.
  have hslice_int : ∀ᵐ z ∂volume, Integrable (fun x ↦ pX x * pY (z - x)) volume := by
    set f : ℝ × ℝ → ℝ := fun p ↦ pX p.2 * pY (p.1 - p.2) with hf_def
    have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ pX p.2) (volume.prod volume) :=
        (hpX_meas.comp measurable_snd).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ pY (p.1 - p.2)) (volume.prod volume) := by
        have hsub : Measurable (fun p : ℝ × ℝ ↦ p.1 - p.2) := measurable_fst.sub measurable_snd
        exact (hpY_meas.comp hsub).aestronglyMeasurable
      exact h1.mul h2
    have hf_int : Integrable f (volume.prod volume) := by
      rw [integrable_prod_iff' hf_meas]
      refine ⟨?_, ?_⟩
      · refine Filter.Eventually.of_forall (fun x ↦ ?_)
        exact (hpY_int.comp_sub_right x).const_mul (pX x)
      · have heq : (fun x ↦ ∫ z, ‖f (z, x)‖ ∂volume)
            = (fun x ↦ ‖pX x‖ * ∫ z, ‖pY z‖ ∂volume) := by
          funext x
          simp only [hf_def, norm_mul]
          rw [integral_const_mul]
          congr 1
          rw [← integral_sub_right_eq_self (fun z ↦ ‖pY z‖) x]
        rw [heq]
        exact (hpX_int.norm.mul_const _)
    exact hf_int.prod_right_ae
  -- per-component density bounds (a.e. `x`), at the fixed level `n` (`n₀ = n`, `hn = le_refl`).
  have hbX : ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map X).rnDeriv volume x).toReal ≤ C_X * pX x :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inl rfl) (le_refl n) hpos
  have hbY : ∀ᵐ y ∂volume,
      (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal ≤ C_Y * pY y :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inr rfl) (le_refl n) hpos
  set pnX : ℝ → ℝ := fun y ↦ (((condTrunc P X Y n).map X).rnDeriv volume y).toReal with hpnX_def
  set pnY : ℝ → ℝ := fun y ↦ (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal with hpnY_def
  have hpnX_nn : ∀ x, 0 ≤ pnX x := fun x ↦ ENNReal.toReal_nonneg
  have hpnY_nn : ∀ x, 0 ≤ pnY x := fun x ↦ ENNReal.toReal_nonneg
  filter_upwards [hslice_int] with z hz_int
  have hbY_z : ∀ᵐ x ∂volume, pnY (z - x) ≤ C_Y * pY (z - x) :=
    (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hbY
  have hfg : (fun x ↦ pnX x * pnY (z - x))
      ≤ᵐ[volume] fun x ↦ (C_X * C_Y) * (pX x * pY (z - x)) := by
    filter_upwards [hbX, hbY_z] with x hxX hxY
    have h1 : pnX x * pnY (z - x) ≤ (C_X * pX x) * (C_Y * pY (z - x)) :=
      mul_le_mul hxX hxY (hpnY_nn (z - x)) (le_trans (hpnX_nn x) hxX)
    calc pnX x * pnY (z - x)
        ≤ (C_X * pX x) * (C_Y * pY (z - x)) := h1
      _ = (C_X * C_Y) * (pX x * pY (z - x)) := by ring
  have hf_nn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun x ↦ pnX x * pnY (z - x) :=
    Filter.Eventually.of_forall (fun x ↦ mul_nonneg (hpnX_nn x) (hpnY_nn (z - x)))
  have hgi : Integrable (fun x ↦ (C_X * C_Y) * (pX x * pY (z - x))) volume :=
    hz_int.const_mul (C_X * C_Y)
  have hmono : (∫ x, pnX x * pnY (z - x) ∂volume)
      ≤ ∫ x, (C_X * C_Y) * (pX x * pY (z - x)) ∂volume :=
    integral_mono_of_nonneg hf_nn hgi hfg
  rw [integral_const_mul] at hmono
  show convDensityAdd pnX pnY z ≤ (C_X * C_Y) * convDensityAdd pX pY z
  simpa only [convDensityAdd] using hmono

private theorem condTrunc_marginal_density_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y) (_hZ_ac : (P.map Z) ≪ volume) :
    ∀ᵐ x ∂volume, Tendsto
      (fun n ↦ (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal) atTop
      (𝓝 (((P.map Z).rnDeriv volume x).toReal)) := by
  -- `Sn n = {|r| ≤ n}`, monotone exhausting `ℝ`.
  set Sn : ℕ → Set ℝ := fun n ↦ {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : ∀ n, MeasurableSet (Sn n) := fun n ↦
    measurableSet_le measurable_norm measurable_const
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  set pZ : ℝ → ℝ := fun y ↦ ((P.map Z).rnDeriv volume y).toReal with hpZ_def
  -- a fixed positive-mass index (internal to this helper).
  obtain ⟨n₀, hpos₀⟩ := (eventually_measure_truncSet_pos P hX hY).exists
  -- `m n := (P.map Z) (Sn n)`, exhausts → `m n → 1`.
  have hSn_mono : Monotone Sn := by
    intro a b hab r hr
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    exact le_trans hr hab'
  have hSn_union : ⋃ n, Sn n = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro r
    obtain ⟨k, hk⟩ := exists_nat_ge (|r|)
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  have hm_tendsto : Tendsto (fun n ↦ (P.map Z) (Sn n)) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := P.map Z) hSn_mono
    rw [hSn_union, measure_univ] at h
    exact h
  have hmreal_tendsto : Tendsto (fun n ↦ ((P.map Z) (Sn n)).toReal) atTop (𝓝 (1 : ℝ)) := by
    have := (ENNReal.tendsto_toReal (ENNReal.one_ne_top)).comp hm_tendsto
    simpa using this
  have hc_tendsto : Tendsto (fun n ↦ (((P.map Z) (Sn n))⁻¹).toReal) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n ↦ ((P.map Z) (Sn n)).toReal⁻¹) atTop (𝓝 1) := by
      have := (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hmreal_tendsto
      simpa using this
    refine h1.congr (fun n ↦ ?_)
    rw [ENNReal.toReal_inv]
  -- per-`n` a.e. equality (only for positive-mass indices `n ≥ n₀`):
  -- `pnZ_n =ᵐ (m n)⁻¹.toReal · 1_{Sn n} · pZ`.
  set fseq : ℕ → ℝ → ℝ :=
    fun n x ↦ (((P.map Z) (Sn n))⁻¹).toReal * (Sn n).indicator pZ x with hfseq_def
  have hper_n : ∀ n, ∀ᵐ x ∂volume, n₀ ≤ n →
      (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal = fseq n x := by
    intro n
    by_cases hge : n₀ ≤ n
    · have hpos : P (truncSet X Y n) ≠ 0 := by
        intro h0; exact hpos₀ (measure_mono_null (truncSet_mono hge) h0)
      have hm_ne : (P.map Z) (Sn n) ≠ 0 :=
        map_measure_truncBall_ne_zero P hX hY hXY hZ hpos
      rw [map_condTrunc_eq_cond_map P hX hY hXY hZ hpos]
      have h_rn := rnDeriv_cond_eq (P.map Z) (hSn_meas n) hm_ne
      filter_upwards [h_rn] with x hx _
      simp only [hfseq_def]
      rw [hx]
      by_cases hxs : x ∈ Sn n
      · rw [Set.indicator_of_mem hxs (f := (P.map Z).rnDeriv volume),
          Set.indicator_of_mem hxs (f := pZ), ENNReal.toReal_mul]
      · rw [Set.indicator_of_notMem hxs (f := (P.map Z).rnDeriv volume),
          Set.indicator_of_notMem hxs (f := pZ), mul_zero, ENNReal.toReal_zero, mul_zero]
    · exact Filter.Eventually.of_forall (fun x hxle ↦ absurd hxle hge)
  -- a single a.e. set where the tail equalities all hold.
  rw [← ae_all_iff] at hper_n
  filter_upwards [hper_n] with x hx
  -- `fseq n x → pZ x` (constant `c_n → 1`, indicator `→ 1`).
  have hf_lim : Tendsto (fun n ↦ fseq n x) atTop (𝓝 (pZ x)) := by
    have hev_eq : (fun n ↦ fseq n x)
        =ᶠ[atTop] fun n ↦ (((P.map Z) (Sn n))⁻¹).toReal * pZ x := by
      obtain ⟨k, hk⟩ := exists_nat_ge (|x|)
      filter_upwards [Filter.eventually_ge_atTop k] with n hn
      have hxn : x ∈ Sn n := le_trans hk (by exact_mod_cast hn)
      simp only [hfseq_def, Set.indicator_of_mem hxn (f := pZ)]
    refine Tendsto.congr' hev_eq.symm ?_
    have := hc_tendsto.mul_const (pZ x)
    simpa using this
  -- transport the tail equality `pnZ_n x = fseq n x` (for `n ≥ n₀`) into the limit.
  refine (hf_lim.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
  exact (hx n hn).symm

/-- Pointwise convergence of the sum density under conditioning truncation:
`p_n ∗ q_n → pX ∗ pY` (a.e. `z`). Each conditioned marginal converges a.e.
(`p_n → pX`, `q_n → qY`), and the filter-form dominated convergence theorem with the dominating
function `C² · pX(x) · pY(z - x)` gives `p_n ∗ q_n (z) → pX ∗ pY (z)` for a.e. `z`.
@audit:ok -/
theorem convDensity_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) :
    ∀ᵐ z ∂volume, Tendsto
      (fun n ↦ convDensityAdd (fun y ↦ ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal)
        (fun y ↦ ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal) z) atTop
      (𝓝 (convDensityAdd (fun y ↦ (P.map X).rnDeriv volume y |>.toReal)
          (fun y ↦ (P.map Y).rnDeriv volume y |>.toReal) z)) := by
  classical
  -- marginal densities of `P`.
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set pX : ℝ → ℝ := fun y ↦ ((P.map X).rnDeriv volume y).toReal with hpX_def
  set pY : ℝ → ℝ := fun y ↦ ((P.map Y).rnDeriv volume y).toReal with hpY_def
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x ↦ ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x ↦ ENNReal.toReal_nonneg
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  -- a fixed positive-mass index `n₀`.
  obtain ⟨n₀, hpos₀⟩ := (eventually_measure_truncSet_pos P hX hY).exists
  -- per-component pointwise convergence (a.e. `x`).
  have hX_lim := condTrunc_marginal_density_tendsto P hX hY hXY (Or.inl rfl) hX_ac
  have hY_lim := condTrunc_marginal_density_tendsto P hX hY hXY (Or.inr rfl) hY_ac
  -- per-component eventual uniform bound (`n ≥ n₀`, a.e. `x`).
  set C_X : ℝ := (((P.map X) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal with hCX_def
  set C_Y : ℝ := (((P.map Y) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal with hCY_def
  have hCX_nn : 0 ≤ C_X := ENNReal.toReal_nonneg
  have hCY_nn : 0 ≤ C_Y := ENNReal.toReal_nonneg
  have hX_bdd : ∀ᶠ n in atTop, ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map X).rnDeriv volume x).toReal ≤ C_X * pX x := by
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    exact condTrunc_marginal_density_le P hX hY hXY (Or.inl rfl) hn hpos₀
  have hY_bdd : ∀ᶠ n in atTop, ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map Y).rnDeriv volume x).toReal ≤ C_Y * pY x := by
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    exact condTrunc_marginal_density_le P hX hY hXY (Or.inr rfl) hn hpos₀
  -- slice integrability of `x ↦ pX x · pY (z − x)` (a.e. `z`), as in sub-helper A.
  have hslice_int : ∀ᵐ z ∂volume, Integrable (fun x ↦ pX x * pY (z - x)) volume := by
    set f : ℝ × ℝ → ℝ := fun p ↦ pX p.2 * pY (p.1 - p.2) with hf_def
    have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ pX p.2) (volume.prod volume) :=
        (hpX_meas.comp measurable_snd).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ pY (p.1 - p.2)) (volume.prod volume) := by
        have hsub : Measurable (fun p : ℝ × ℝ ↦ p.1 - p.2) := measurable_fst.sub measurable_snd
        exact (hpY_meas.comp hsub).aestronglyMeasurable
      exact h1.mul h2
    have hf_int : Integrable f (volume.prod volume) := by
      rw [integrable_prod_iff' hf_meas]
      refine ⟨?_, ?_⟩
      · refine Filter.Eventually.of_forall (fun x ↦ ?_)
        exact (hpY_int.comp_sub_right x).const_mul (pX x)
      · have heq : (fun x ↦ ∫ z, ‖f (z, x)‖ ∂volume)
            = (fun x ↦ ‖pX x‖ * ∫ z, ‖pY z‖ ∂volume) := by
          funext x
          simp only [hf_def, norm_mul]
          rw [integral_const_mul]
          congr 1
          rw [← integral_sub_right_eq_self (fun z ↦ ‖pY z‖) x]
        rw [heq]
        exact (hpX_int.norm.mul_const _)
    exact hf_int.prod_right_ae
  -- abbreviations for the conditioned marginal densities.
  set pnX : ℕ → ℝ → ℝ :=
    fun n y ↦ (((condTrunc P X Y n).map X).rnDeriv volume y).toReal with hpnX_def
  set pnY : ℕ → ℝ → ℝ :=
    fun n y ↦ (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal with hpnY_def
  have hpnX_nn : ∀ n x, 0 ≤ pnX n x := fun n x ↦ ENNReal.toReal_nonneg
  have hpnY_nn : ∀ n x, 0 ≤ pnY n x := fun n x ↦ ENNReal.toReal_nonneg
  -- assemble per `z` with the filter-version dominated convergence theorem.
  filter_upwards [hslice_int] with z hz_int
  -- the convolution as `∫ pnX n x · pnY n (z − x) dx → ∫ pX x · pY (z − x) dx`.
  show Tendsto (fun n ↦ convDensityAdd (pnX n) (pnY n) z) atTop
    (𝓝 (convDensityAdd pX pY z))
  simp only [convDensityAdd]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ (C_X * C_Y) * (pX x * pY (z - x))) ?_ ?_ ?_ ?_
  · -- `∀ᶠ n, AEStronglyMeasurable (fun x => pnX n x · pnY n (z − x))`.
    refine Filter.Eventually.of_forall (fun n ↦ ?_)
    refine (?_ : AEStronglyMeasurable (fun x ↦ pnX n x * pnY n (z - x)) volume)
    have h1 : Measurable (fun x ↦ pnX n x) := by
      simpa [hpnX_def] using (Measure.measurable_rnDeriv
        ((condTrunc P X Y n).map X) volume).ennreal_toReal
    have h2 : Measurable (fun x ↦ pnY n (z - x)) := by
      have hb : Measurable (fun y ↦ pnY n y) := by
        simpa [hpnY_def] using (Measure.measurable_rnDeriv
          ((condTrunc P X Y n).map Y) volume).ennreal_toReal
      exact hb.comp (measurable_const.sub measurable_id)
    exact (h1.mul h2).aestronglyMeasurable
  · -- `∀ᶠ n, ∀ᵐ x, ‖pnX n x · pnY n (z − x)‖ ≤ (C_X·C_Y)·(pX x · pY (z − x))`.
    filter_upwards [hX_bdd, hY_bdd] with n hxX hxY
    -- transport the `Y` bound through `x ↦ z − x`.
    have hxY_z : ∀ᵐ x ∂volume, pnY n (z - x) ≤ C_Y * pY (z - x) :=
      (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hxY
    filter_upwards [hxX, hxY_z] with x hbx hby
    have hprod_nn : 0 ≤ pnX n x * pnY n (z - x) :=
      mul_nonneg (hpnX_nn n x) (hpnY_nn n (z - x))
    rw [Real.norm_of_nonneg hprod_nn]
    have h1 : pnX n x * pnY n (z - x) ≤ (C_X * pX x) * (C_Y * pY (z - x)) :=
      mul_le_mul hbx hby (hpnY_nn n (z - x)) (le_trans (hpnX_nn n x) hbx)
    calc pnX n x * pnY n (z - x)
        ≤ (C_X * pX x) * (C_Y * pY (z - x)) := h1
      _ = (C_X * C_Y) * (pX x * pY (z - x)) := by ring
  · -- bound integrable.
    exact hz_int.const_mul (C_X * C_Y)
  · -- `∀ᵐ x, pnX n x · pnY n (z − x) → pX x · pY (z − x)`.
    -- transport the `X` convergence (z-independent) + transported `Y` convergence.
    have hzY_lim' : ∀ᵐ x ∂volume, Tendsto (fun n ↦ pnY n (z - x)) atTop (𝓝 (pY (z - x))) :=
      (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hY_lim
    filter_upwards [hX_lim, hzY_lim'] with x hxlim hylim
    exact hxlim.mul hylim

/-- The cross-entropy sequence `RHS_n := -∫ log (density of ν) ∂μ_n`, where
`μ_n := (condTrunc P X Y n).map (X + Y)` and `ν := P.map (X + Y)`. It links the Gibbs upper bound
and the dominated-convergence limit in the upper semicontinuity argument.
@audit:ok -/
noncomputable def crossEntropySeq (P : Measure Ω) (X Y : Ω → ℝ) (n : ℕ) : ℝ :=
  - ∫ x, Real.log ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal
      ∂((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω))

/-- Per-`n` integrability of the cross-entropy integrand: `log (density of ν)` is integrable
against `μ_n`, where `ν := P.map (X + Y)` and `μ_n := (condTrunc P X Y n).map (X + Y)`. Pulling the
integral back to `volume` and using the dominating bound `p_n ∗ q_n ≤ C (pX ∗ pY)` together with
`hent_sum` bounds the integrand by `C · |negMulLog ((ν.rnDeriv).toReal)|`, which is integrable.
This supplies the `h_cross_int` premise of the Gibbs bound.
@audit:ok -/
theorem crossEntropy_integrable_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x ↦ Real.log ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal)
      ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω)) := by
  classical
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  have hsum_meas : Measurable (fun ω ↦ X ω + Y ω) := hX.add hY
  set ν := P.map (fun ω ↦ X ω + Y ω) with hν_def
  set μn := (condTrunc P X Y n).map (fun ω ↦ X ω + Y ω) with hμn_def
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  haveI : IsProbabilityMeasure μn := Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  -- a.c. of the conditioned sum law (used for the pull-back).
  have hν_ac : ν ≪ volume := by
    have hconv : P.map (fun ω ↦ X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω ↦ X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hν_def, hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  have hμn_ac : μn ≪ volume := map_condTrunc_absolutelyContinuous P hX hsum_meas hν_ac
  -- pull back the integrability to `volume` via the rnDeriv smul characterisation.
  set g : ℝ → ℝ := fun x ↦ Real.log ((ν.rnDeriv volume x).toReal) with hg_def
  rw [← integrable_rnDeriv_smul_iff (μ := μn) (ν := volume) hμn_ac (f := g)]
  -- abbreviations: marginal/sum densities.
  set pnX : ℝ → ℝ := fun y ↦ ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal with hpnX_def
  set pnY : ℝ → ℝ := fun y ↦ ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal with hpnY_def
  set pX : ℝ → ℝ := fun y ↦ (P.map X).rnDeriv volume y |>.toReal with hpX_def
  set pY : ℝ → ℝ := fun y ↦ (P.map Y).rnDeriv volume y |>.toReal with hpY_def
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x ↦ ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x ↦ ENNReal.toReal_nonneg
  have hpnX_nn : ∀ x, 0 ≤ pnX x := fun x ↦ ENNReal.toReal_nonneg
  have hpnY_nn : ∀ x, 0 ≤ pnY x := fun x ↦ ENNReal.toReal_nonneg
  -- `(μn.rnDeriv vol).toReal =ᵐ convDensityAdd pnX pnY`.
  have hμn_dens : (fun x ↦ (μn.rnDeriv volume x).toReal)
      =ᵐ[volume] fun x ↦ convDensityAdd pnX pnY x := by
    have h := rnDeriv_map_condTrunc_sum_ae P hX hY hX_ac hY_ac hXY hpos
    filter_upwards [h] with x hx
    have hconv_nn : 0 ≤ convDensityAdd pnX pnY x :=
      integral_nonneg (fun y ↦ mul_nonneg (hpnX_nn y) (hpnY_nn (x - y)))
    rw [hμn_def, hx, ENNReal.toReal_ofReal hconv_nn]
  -- `(ν.rnDeriv vol).toReal =ᵐ convDensityAdd pX pY`.
  have hν_dens : (fun x ↦ (ν.rnDeriv volume x).toReal)
      =ᵐ[volume] fun x ↦ convDensityAdd pX pY x := by
    have h := rnDeriv_map_sum_ae P hX hY hX_ac hY_ac hXY
    filter_upwards [h] with x hx
    have hconv_nn : 0 ≤ convDensityAdd pX pY x :=
      integral_nonneg (fun y ↦ mul_nonneg (hpX_nn y) (hpY_nn (x - y)))
    rw [hν_def, hx, ENNReal.toReal_ofReal hconv_nn]
  -- the fixed-`n` dominating bound `convDensityAdd pnX pnY ≤ C · convDensityAdd pX pY` (a.e.).
  obtain ⟨C, hC_nn, hbound_conv⟩ :=
    convDensityAdd_condTrunc_le_const_mul_at P hX hY hXY hX_ac hY_ac hpos
  -- bound function on `volume`: `C · |negMulLog ((ν.rnDeriv vol).toReal)|`.
  set bnd : ℝ → ℝ := fun x ↦ C * |Real.negMulLog ((ν.rnDeriv volume x).toReal)| with hbnd_def
  have hbnd_int : Integrable bnd volume := hent_sum.abs.const_mul C
  -- measurability of the pulled-back integrand.
  have hF_meas : AEStronglyMeasurable
      (fun x ↦ (μn.rnDeriv volume x).toReal • g x) volume := by
    refine ((Measure.measurable_rnDeriv μn volume).ennreal_toReal.aestronglyMeasurable.smul ?_)
    exact ((Real.measurable_log.comp
      (Measure.measurable_rnDeriv ν volume).ennreal_toReal)).aestronglyMeasurable
  refine Integrable.mono' hbnd_int hF_meas ?_
  filter_upwards [hμn_dens, hν_dens, hbound_conv] with x hxμn hxν hxbd
  -- pointwise: `‖(μn.rnDeriv).toReal • g‖ ≤ C · |negMulLog ((ν.rnDeriv).toReal)|`.
  -- `hxμn : (μn.rnDeriv).toReal = convDensityAdd pnX pnY x`,
  -- `hxν  : (ν.rnDeriv).toReal  = convDensityAdd pX pY x`.
  have hr_nn : (0 : ℝ) ≤ (ν.rnDeriv volume x).toReal := ENNReal.toReal_nonneg
  rw [smul_eq_mul, norm_mul, Real.norm_of_nonneg (ENNReal.toReal_nonneg)]
  -- `(μn.rnDeriv).toReal ≤ C · (ν.rnDeriv).toReal` from the convolution bound.
  have hstep : (μn.rnDeriv volume x).toReal ≤ C * (ν.rnDeriv volume x).toReal := by
    rw [hxμn, hxν]; exact hxbd
  -- `(ν.rnDeriv).toReal · |log| = |negMulLog ((ν.rnDeriv).toReal)|`.
  have hr_log : (ν.rnDeriv volume x).toReal * ‖g x‖
      = |Real.negMulLog ((ν.rnDeriv volume x).toReal)| := by
    have hgx : g x = Real.log ((ν.rnDeriv volume x).toReal) := rfl
    rw [hgx, Real.norm_eq_abs, Real.negMulLog_eq_neg, abs_neg, abs_mul, abs_of_nonneg hr_nn]
  calc (μn.rnDeriv volume x).toReal * ‖g x‖
      ≤ (C * (ν.rnDeriv volume x).toReal) * ‖g x‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ = C * ((ν.rnDeriv volume x).toReal * ‖g x‖) := by ring
    _ = C * |Real.negMulLog ((ν.rnDeriv volume x).toReal)| := by rw [hr_log]
    _ = bnd x := by rw [hbnd_def]

/-- Per-`n` Gibbs upper bound: `∀ᶠ n, h(μ_n) ≤ RHS_n`, where `RHS_n = crossEntropySeq P X Y n`.
The generalized Gibbs inequality `differentialEntropy_le_cross_entropy` is applied with
`μ = μ_n`, `ν = P.map (X + Y)`, supplying the per-`n` regularity facts (`μ_n` absolutely
continuous, `μ_n ≪ ν`, finite entropy, and the cross-entropy integrability).
@audit:ok -/
theorem differentialEntropy_condTrunc_sum_le_crossEntropy (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x ↦ Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x ↦ Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    ∀ᶠ n in atTop,
      differentialEntropy ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω))
        ≤ crossEntropySeq P X Y n := by
  have hsum_meas : Measurable (fun ω ↦ X ω + Y ω) := hX.add hY
  have hν_ac : (P.map (fun ω ↦ X ω + Y ω)) ≪ volume := by
    have hconv : P.map (fun ω ↦ X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω ↦ X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  haveI : IsProbabilityMeasure ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω)) :=
    Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  haveI : IsProbabilityMeasure (P.map (fun ω ↦ X ω + Y ω)) :=
    Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  -- regularity facts for the Gibbs lemma.
  have hμ_ac : ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω)) ≪ volume :=
    map_condTrunc_absolutelyContinuous P hX hsum_meas hν_ac
  have hμν : ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω))
      ≪ (P.map (fun ω ↦ X ω + Y ω)) := by
    have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
    exact h_cond.map hsum_meas
  have hμ_ent : Integrable
      (fun x ↦ Real.negMulLog
        (((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume :=
    integrable_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hX_ent hY_ent hpos
  have hcross : Integrable
      (fun x ↦ Real.log ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal)
      ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω)) :=
    crossEntropy_integrable_condTrunc_sum P hX hY hXY hX_ac hY_ac hent_sum hpos
  exact differentialEntropy_le_cross_entropy hμ_ac hν_ac hμν hμ_ent hcross

/-- Convergence of the cross-entropy sequence: `RHS_n → h(ν)` with `ν = P.map (X + Y)`. Pulling
`RHS_n` back to `volume` as `∫ (-log (density of ν)) · (p_n ∗ q_n) dvolume`, the pointwise
convergence `p_n ∗ q_n → pX ∗ pY` together with the dominating function
`|log (density of ν)| · C² (pX ∗ pY)` (integrable from `hent_sum`) gives, via dominated
convergence, the limit `-∫ (pX ∗ pY) log (pX ∗ pY) = h(ν)`.
@audit:ok -/
theorem crossEntropySeq_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n ↦ crossEntropySeq P X Y n) atTop
      (𝓝 (differentialEntropy (P.map (fun ω ↦ X ω + Y ω)))) := by
  classical
  have hsum_meas : Measurable (fun ω ↦ X ω + Y ω) := hX.add hY
  set ν := P.map (fun ω ↦ X ω + Y ω) with hν_def
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  have hν_ac : ν ≪ volume := by
    have hconv : P.map (fun ω ↦ X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω ↦ X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hν_def, hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  -- abbreviations.
  set g : ℝ → ℝ := fun x ↦ Real.log ((ν.rnDeriv volume x).toReal) with hg_def
  set pX : ℝ → ℝ := fun y ↦ (P.map X).rnDeriv volume y |>.toReal with hpX_def
  set pY : ℝ → ℝ := fun y ↦ (P.map Y).rnDeriv volume y |>.toReal with hpY_def
  set pnX : ℕ → ℝ → ℝ :=
    fun n y ↦ ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal with hpnX_def
  set pnY : ℕ → ℝ → ℝ :=
    fun n y ↦ ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal with hpnY_def
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x ↦ ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x ↦ ENNReal.toReal_nonneg
  -- `(ν.rnDeriv vol).toReal =ᵐ convDensityAdd pX pY`.
  have hν_dens : (fun x ↦ (ν.rnDeriv volume x).toReal)
      =ᵐ[volume] fun x ↦ convDensityAdd pX pY x := by
    have h := rnDeriv_map_sum_ae P hX hY hX_ac hY_ac hXY
    filter_upwards [h] with x hx
    have hconv_nn : 0 ≤ convDensityAdd pX pY x :=
      integral_nonneg (fun y ↦ mul_nonneg (hpX_nn y) (hpY_nn (x - y)))
    rw [hν_def, hx, ENNReal.toReal_ofReal hconv_nn]
  -- the dominating bound from sub-helper A (eventual in `n`).
  obtain ⟨n₀, hpos₀⟩ := (eventually_measure_truncSet_pos P hX hY).exists
  obtain ⟨C, hC_nn, hAbound⟩ :=
    convDensity_condTrunc_le_const_mul P hX hY hXY hX_ac hY_ac (n₀ := n₀) hpos₀
  -- the pointwise convergence from sub-helper B.
  have hB := convDensity_condTrunc_tendsto P hX hY hXY hX_ac hY_ac
  -- bound function on `volume`: `C · |negMulLog ((ν.rnDeriv vol).toReal)|`, integrable.
  set bnd : ℝ → ℝ := fun x ↦ C * |Real.negMulLog ((ν.rnDeriv volume x).toReal)| with hbnd_def
  have hbnd_int : Integrable bnd volume := hent_sum.abs.const_mul C
  -- outer DCT: `∫ (convDensityAdd pnX pnY)·g → ∫ (convDensityAdd pX pY)·g`.
  have hDCT : Tendsto (fun n ↦ ∫ x, convDensityAdd (pnX n) (pnY n) x * g x ∂volume) atTop
      (𝓝 (∫ x, convDensityAdd pX pY x * g x ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence bnd ?_ ?_ hbnd_int ?_
    · -- `∀ᶠ n, AEStronglyMeasurable (fun x => convDensityAdd pnX pnY x · g x)`.
      refine Filter.Eventually.of_forall (fun n ↦ ?_)
      have hmX : Measurable (fun y ↦ pnX n y) :=
        (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have hmY : Measurable (fun y ↦ pnY n y) :=
        (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have hconv_sm : StronglyMeasurable (fun z ↦ convDensityAdd (pnX n) (pnY n) z) := by
        refine StronglyMeasurable.integral_prod_right (f := fun z x ↦ pnX n x * pnY n (z - x)) ?_
        have h1 : Measurable (fun p : ℝ × ℝ ↦ pnX n p.2) := hmX.comp measurable_snd
        have h2 : Measurable (fun p : ℝ × ℝ ↦ pnY n (p.1 - p.2)) :=
          hmY.comp (measurable_fst.sub measurable_snd)
        exact ((h1.mul h2)).stronglyMeasurable
      have hg_meas : Measurable g :=
        Real.measurable_log.comp (Measure.measurable_rnDeriv ν volume).ennreal_toReal
      exact (hconv_sm.aestronglyMeasurable.mul hg_meas.aestronglyMeasurable)
    · -- `∀ᶠ n, ∀ᵐ x, ‖convDensityAdd pnX pnY x · g x‖ ≤ bnd x`.
      filter_upwards [hAbound] with n hAn
      filter_upwards [hAn, hν_dens] with x hxA hxν
      rw [norm_mul]
      -- `convDensityAdd pnX pnY x ≥ 0`.
      have hconv_nn : 0 ≤ convDensityAdd (pnX n) (pnY n) x :=
        integral_nonneg (fun y ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      rw [Real.norm_of_nonneg hconv_nn]
      have hr_nn : (0 : ℝ) ≤ (ν.rnDeriv volume x).toReal := ENNReal.toReal_nonneg
      -- `convDensityAdd pnX pnY x ≤ C · convDensityAdd pX pY x = C · (ν.rnDeriv).toReal`.
      have hstep : convDensityAdd (pnX n) (pnY n) x ≤ C * (ν.rnDeriv volume x).toReal := by
        calc convDensityAdd (pnX n) (pnY n) x
            ≤ C * convDensityAdd pX pY x := hxA
          _ = C * (ν.rnDeriv volume x).toReal := by rw [← hxν]
      have hg_log : (ν.rnDeriv volume x).toReal * ‖g x‖
          = |Real.negMulLog ((ν.rnDeriv volume x).toReal)| := by
        have hgx : g x = Real.log ((ν.rnDeriv volume x).toReal) := rfl
        rw [hgx, Real.norm_eq_abs, Real.negMulLog_eq_neg, abs_neg, abs_mul, abs_of_nonneg hr_nn]
      calc convDensityAdd (pnX n) (pnY n) x * ‖g x‖
          ≤ (C * (ν.rnDeriv volume x).toReal) * ‖g x‖ :=
            mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
        _ = C * ((ν.rnDeriv volume x).toReal * ‖g x‖) := by ring
        _ = C * |Real.negMulLog ((ν.rnDeriv volume x).toReal)| := by rw [hg_log]
        _ = bnd x := by rw [hbnd_def]
    · -- `∀ᵐ x, convDensityAdd pnX pnY x · g x → convDensityAdd pX pY x · g x`.
      filter_upwards [hB] with x hxB
      exact hxB.mul_const (g x)
  -- pull-back: `crossEntropySeq n =ᶠ -∫ (convDensityAdd pnX pnY)·g` (positive-mass `n`).
  have hpull : (fun n ↦ crossEntropySeq P X Y n)
      =ᶠ[atTop] fun n ↦ -∫ x, convDensityAdd (pnX n) (pnY n) x * g x ∂volume := by
    filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
    haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
      isProbabilityMeasure_condTrunc P hX hY hpos
    set μn := (condTrunc P X Y n).map (fun ω ↦ X ω + Y ω) with hμn_def
    haveI : IsProbabilityMeasure μn := Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
    have hμn_ac : μn ≪ volume := map_condTrunc_absolutelyContinuous P hX hsum_meas hν_ac
    -- `crossEntropySeq n = -∫ g ∂μn = -∫ (μn.rnDeriv vol).toReal • g ∂vol`.
    have h1 : crossEntropySeq P X Y n = -∫ x, g x ∂μn := rfl
    rw [h1, ← integral_rnDeriv_smul (μ := μn) (ν := volume) hμn_ac (f := g)]
    -- `(μn.rnDeriv vol).toReal • g =ᵐ (convDensityAdd pnX pnY)·g`.
    have hμn_dens : (fun x ↦ (μn.rnDeriv volume x).toReal)
        =ᵐ[volume] fun x ↦ convDensityAdd (pnX n) (pnY n) x := by
      have h := rnDeriv_map_condTrunc_sum_ae P hX hY hX_ac hY_ac hXY hpos
      filter_upwards [h] with x hx
      have hconv_nn : 0 ≤ convDensityAdd (pnX n) (pnY n) x :=
        integral_nonneg (fun y ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      rw [hμn_def, hx, ENNReal.toReal_ofReal hconv_nn]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hμn_dens] with x hx
    rw [smul_eq_mul, hx]
  -- limit target: `-∫ (convDensityAdd pX pY)·g = differentialEntropy ν`.
  have htarget : -∫ x, convDensityAdd pX pY x * g x ∂volume = differentialEntropy ν := by
    rw [show differentialEntropy ν
        = ∫ x, Real.negMulLog ((ν.rnDeriv volume x).toReal) ∂volume from rfl]
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hν_dens] with x hxν
    have hgx : g x = Real.log ((ν.rnDeriv volume x).toReal) := rfl
    rw [← hxν, hgx, Real.negMulLog_eq_neg]
  -- assemble.
  rw [← htarget]
  exact Tendsto.congr' hpull.symm hDCT.neg


end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
