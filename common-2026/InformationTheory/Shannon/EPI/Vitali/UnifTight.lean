import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.Conv.DensityAssoc
import InformationTheory.Shannon.FisherConvBound

/-!
# EPI G2 Vitali witness — UnifTight (UT)

Genuine standalone implementation of the `hut` input for the layer-2 Vitali
machinery (`differentialEntropy_convDensity_integral_tendsto`). The main lemma
`negMulLog_convDensity_unifTight` has the *exact same signature* as the parked
`EPIG2HeatFlowContinuity.negMulLog_convDensity_unifTight` (`:161`), to which the parked
version delegates.

The strategy (inventory `epi-g2-vitali-witness-inventory.md`, category C):
`f_n := convDensityAdd pX g_{u n} = pX ∗ g_{u n}`. Take `s = Icc (-R) R`; on the tail
`{|x| > R}` the negMulLog of the smoothed density is controlled by the second moment
`∫ x² f_n = ∫ x² pX + u n` (additivity of variance for the independent sum). The tail
mass is driven via the measure-independent Markov inequality
`mul_meas_ge_le_lintegral` (works on `volume`, no `[IsFiniteMeasure]`).
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-- Gaussian first moment over `volume`: `∫ x · g_t(x) = 0` (centered at `0`).
@audit:ok -/
private theorem integral_id_mul_gaussianPDFReal {t : ℝ} (ht : 0 < t) :
    ∫ x, x * gaussianPDFReal 0 ⟨t, ht.le⟩ x ∂volume = 0 := by
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  calc ∫ x, x * gaussianPDFReal 0 ⟨t, ht.le⟩ x ∂volume
      = ∫ x, gaussianPDFReal 0 ⟨t, ht.le⟩ x • x ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [smul_eq_mul, mul_comm]
    _ = ∫ x, x ∂(gaussianReal 0 ⟨t, ht.le⟩) :=
        (integral_gaussianReal_eq_integral_smul (μ := 0) (f := fun x => x) hv_ne).symm
    _ = 0 := integral_id_gaussianReal

/-- Inner moment after Tonelli: `∫ x, x² · g_t(x - y) = y² + t`.
Substitution `x ↦ x + y` (translation-invariance of `volume`) + the three Gaussian
moments `∫ g_t = 1`, `∫ x g_t = 0`, `∫ x² g_t = t`.
@audit:ok -/
private theorem integral_sq_mul_gaussianPDFReal_shift {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∫ x, x ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ (x - y) ∂volume = y ^ 2 + t := by
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  -- substitute x ↦ x + y
  have hsub :
      ∫ x, x ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ (x - y) ∂volume
        = ∫ x, (x + y) ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ x ∂volume := by
    have := MeasureTheory.integral_add_right_eq_self
      (μ := volume) (fun x => x ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ (x - y)) y
    simp only [add_sub_cancel_right] at this
    rw [← this]
  rw [hsub]
  -- expand (x+y)² = x² + 2xy + y²
  have hg_int : Integrable (gaussianPDFReal 0 ⟨t, ht.le⟩) volume :=
    integrable_gaussianPDFReal 0 ⟨t, ht.le⟩
  have hsq_int : Integrable (fun x => x ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ x) volume :=
    InformationTheory.Shannon.FisherInfo.integrable_sq_mul_gaussianPDFReal ht
  have hid_int : Integrable (fun x => x * gaussianPDFReal 0 ⟨t, ht.le⟩ x) volume := by
    -- `id ∈ L¹(gaussianReal)`, transported to `volume` via the withDensity bridge.
    have hmem : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 ⟨t, ht.le⟩) := memLp_id_gaussianReal 1
    have hid_g : Integrable (fun u => u) (gaussianReal 0 ⟨t, ht.le⟩) := by
      have := (memLp_one_iff_integrable (μ := gaussianReal 0 ⟨t, ht.le⟩)
        (f := (id : ℝ → ℝ))).mp hmem
      simpa using this
    rw [gaussianReal_of_var_ne_zero _ hv_ne] at hid_g
    rw [integrable_withDensity_iff (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hid_g
    refine hid_g.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  have hexpand : ∀ x : ℝ,
      (x + y) ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ x
        = x ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ x
          + 2 * y * (x * gaussianPDFReal 0 ⟨t, ht.le⟩ x)
          + y ^ 2 * gaussianPDFReal 0 ⟨t, ht.le⟩ x := by
    intro x; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  rw [integral_add (by exact hsq_int.add ((hid_int.const_mul (2 * y)))) (hg_int.const_mul (y ^ 2)),
    integral_add hsq_int (hid_int.const_mul (2 * y)),
    integral_const_mul, integral_const_mul]
  rw [InformationTheory.Shannon.FisherInfo.integral_sq_mul_gaussianPDFReal ht,
    integral_id_mul_gaussianPDFReal ht, integral_gaussianPDFReal_eq_one 0 hv_ne]
  ring

/-- **Convolution-density second moment**.
For `f_t = pX ∗ g_t` (Gaussian kernel of variance `t`):
`∫ x², (convDensityAdd pX g_t) ∂volume = (∫ x², pX) + (∫ pX) · t`.
@audit:ok -/
theorem convDensityAdd_second_moment
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume
      = (∫ x, x ^ 2 * pX x ∂volume) + (∫ y, pX y ∂volume) * t := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  set p_t : ℝ → ℝ := convDensityAdd pX g with hp_def
  -- The nonneg double-integrand `K x y := x² · (pX y · g (x - y)) ≥ 0`.
  set K : ℝ → ℝ → ℝ := fun x y => x ^ 2 * (pX y * g (x - y)) with hK_def
  have hK_nn : ∀ x y, 0 ≤ K x y := fun x y =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _))
  -- joint measurability of `(x,y) ↦ ofReal (K x y)`.
  have hKofReal_meas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (K p.1 p.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine (measurable_fst.pow_const 2).mul ?_
    exact (hpX_meas.comp measurable_snd).mul
      ((measurable_gaussianPDFReal 0 ⟨t, ht.le⟩).comp (measurable_fst.sub measurable_snd))
  -- `p_t x ≥ 0`.
  have hp_nn : ∀ x, 0 ≤ p_t x := fun x =>
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- inner integrand `y ↦ pX y · g (x - y)` is integrable (convolution integrand).
  have hconv_int : ∀ x, Integrable (fun y => pX y * g (x - y)) volume := fun x => by
    refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨t, ht.le⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
      show gaussianPDFReal 0 ⟨t, ht.le⟩ (x - y) ≤ _
      rw [gaussianPDFReal]
      refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
      rw [neg_div]; exact neg_nonpos.mpr (by positivity)
  -- The shifted second-moment integrability for fixed `y`: `x ↦ x²·g(x-y)`.
  have hsq_mom_int : Integrable (fun u => u ^ 2 * g u) volume := by
    simpa [hg_def] using
      InformationTheory.Shannon.FisherInfo.integrable_sq_mul_gaussianPDFReal ht
  -- ── Step A: lift LHS to a double lintegral over `(x,y)`. ──
  -- `∫ x, x²·p_t x = ∫ x, ∫ y, K x y` (linearity of inner integral), and both sides nonneg.
  have hLHS_inner : ∀ x, x ^ 2 * p_t x = ∫ y, K x y ∂volume := by
    intro x
    rw [hp_def]; unfold convDensityAdd
    rw [← integral_const_mul]
  -- `∫⁻ x ofReal(x²·p_t x) = ∫⁻ x ∫⁻ y ofReal(K x y)` (each inner integral nonneg & integrable).
  have hLHS_lint : (∫⁻ x, ENNReal.ofReal (x ^ 2 * p_t x) ∂volume)
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂volume ∂volume := by
    refine lintegral_congr fun x => ?_
    rw [hLHS_inner x]
    refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun y => hK_nn x y)
    -- `y ↦ K x y = x²·(pX y · g(x-y))` integrable = const·(conv integrand).
    refine ((hconv_int x).const_mul (x ^ 2)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hK_def]
  -- ── Step B: Tonelli swap + inner Gaussian moment `∫_x x²·g(x-y) = y²+t`. ──
  have hswap : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂volume ∂volume)
      = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (K x y) ∂volume ∂volume :=
    lintegral_lintegral_swap hKofReal_meas.aemeasurable
  -- `x ↦ x²·g(x-y)` integrable: substitute `x = u+y`, expand `(u+y)² = u²+2uy+y²`,
  -- each term integrable against `g`.
  have hg_int : Integrable g volume := by
    rw [hg_def]; exact integrable_gaussianPDFReal 0 ⟨t, ht.le⟩
  have hid_g_int : Integrable (fun u => u * g u) volume := by
    have hmem : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 ⟨t, ht.le⟩) := memLp_id_gaussianReal 1
    have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
      intro h; exact ht.ne' (congrArg NNReal.toReal h)
    have hid_g : Integrable (fun u => u) (gaussianReal 0 ⟨t, ht.le⟩) := by
      have := (memLp_one_iff_integrable (μ := gaussianReal 0 ⟨t, ht.le⟩)
        (f := (id : ℝ → ℝ))).mp hmem
      simpa using this
    rw [gaussianReal_of_var_ne_zero _ hv_ne] at hid_g
    rw [integrable_withDensity_iff (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hid_g
    refine hid_g.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hg_def, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  have hsq_shift_int : ∀ y, Integrable (fun x => x ^ 2 * g (x - y)) volume := by
    intro y
    -- after `x = u + y`: `(u+y)²·g(u) = u²g(u) + 2y·(u g(u)) + y²·g(u)`.
    have hexp : Integrable (fun u => (u + y) ^ 2 * g u) volume := by
      have : Integrable
          (fun u => u ^ 2 * g u + 2 * y * (u * g u) + y ^ 2 * g u) volume :=
        (hsq_mom_int.add (hid_g_int.const_mul (2 * y))).add (hg_int.const_mul (y ^ 2))
      refine this.congr (Filter.Eventually.of_forall fun u => ?_); ring
    have := hexp.comp_sub_right y
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_add_cancel]
  -- inner moment: `∫⁻ x ofReal(K x y) = ofReal(pX y · (y²+t))`.
  have hxint : ∀ y, Integrable (fun x => K x y) volume := fun y => by
    refine ((hsq_shift_int y).const_mul (pX y)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hK_def]; ring
  have hinner : ∀ y, (∫⁻ x, ENNReal.ofReal (K x y) ∂volume)
      = ENNReal.ofReal (pX y * (y ^ 2 + t)) := by
    intro y
    rw [← ofReal_integral_eq_lintegral_ofReal (hxint y)
      (Filter.Eventually.of_forall fun x => hK_nn x y)]
    congr 1
    rw [show (fun x => K x y) = (fun x => pX y * (x ^ 2 * g (x - y))) from by
      funext x; simp only [hK_def]; ring, integral_const_mul]
    rw [hg_def, integral_sq_mul_gaussianPDFReal_shift ht y]
  -- ── Step C: outer integral over `y`. ──
  -- `∫⁻ y ofReal(pX y·(y²+t)) = ofReal(∫ y pX y·(y²+t))` (integrable: hpX_mom + hpX_int).
  have hpX_polymom_int : Integrable (fun y => pX y * (y ^ 2 + t)) volume := by
    have : Integrable (fun y => y ^ 2 * pX y + pX y * t) volume :=
      hpX_mom.add (hpX_int.mul_const t)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_); ring
  have houter : (∫⁻ y, ENNReal.ofReal (pX y * (y ^ 2 + t)) ∂volume)
      = ENNReal.ofReal (∫ y, pX y * (y ^ 2 + t) ∂volume) :=
    (ofReal_integral_eq_lintegral_ofReal hpX_polymom_int
      (Filter.Eventually.of_forall fun y =>
        mul_nonneg (hpX_nn y) (by positivity))).symm
  -- ── Assemble: both sides equal via `ofReal_integral` on LHS. ──
  -- The Bochner LHS `∫ x, x²·p_t x` is integrable (we get it from finiteness of the lintegral).
  have hLHS_int : Integrable (fun x => x ^ 2 * p_t x) volume := by
    -- AE-measurable + finite lintegral of its norm.
    have hmeas : AEStronglyMeasurable (fun x => x ^ 2 * p_t x) volume := by
      refine (measurable_id.pow_const 2).aestronglyMeasurable.mul ?_
      rw [hp_def]
      exact (convDensityAdd_pXpY_measurable pX g hpX_meas
        (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)).aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    -- `∫⁻ ‖x²·p_t x‖ₑ = ∫⁻ ofReal(x²·p_t x)` (nonneg), then = ofReal finite.
    have hnorm : (fun x => (‖x ^ 2 * p_t x‖ₑ : ℝ≥0∞))
        = (fun x => ENNReal.ofReal (x ^ 2 * p_t x)) := by
      funext x
      rw [Real.enorm_eq_ofReal (mul_nonneg (sq_nonneg _) (hp_nn x))]
    rw [hnorm, hLHS_lint, hswap]
    simp_rw [hinner]
    rw [houter]
    exact ENNReal.ofReal_lt_top
  -- Use injectivity of `ofReal` on nonneg reals.
  have hgoal_lint : ENNReal.ofReal (∫ x, x ^ 2 * p_t x ∂volume)
      = ENNReal.ofReal (∫ y, pX y * (y ^ 2 + t) ∂volume) := by
    rw [ofReal_integral_eq_lintegral_ofReal hLHS_int
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hp_nn x))]
    rw [hLHS_lint, hswap]
    simp_rw [hinner]
    rw [houter]
  have hLHS_nn : 0 ≤ ∫ x, x ^ 2 * p_t x ∂volume :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hp_nn x)
  have hRHS_nn : 0 ≤ ∫ y, pX y * (y ^ 2 + t) ∂volume :=
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (by positivity)
  have hval : (∫ x, x ^ 2 * p_t x ∂volume) = ∫ y, pX y * (y ^ 2 + t) ∂volume :=
    (ENNReal.ofReal_eq_ofReal_iff hLHS_nn hRHS_nn).mp hgoal_lint
  rw [hval]
  -- Final RHS reshape: `∫ y pX y·(y²+t) = ∫ y²pX + (∫pX)·t`.
  rw [show (fun y => pX y * (y ^ 2 + t)) = (fun y => y ^ 2 * pX y + pX y * t) from by
    funext y; ring]
  rw [integral_add hpX_mom (hpX_int.mul_const t), integral_mul_const]

/-- **Uniform second-moment bound (GENUINE sub-structure of the UT witness).**
For a bounded positive variance sequence `u`, the second moments
`∫ x², f_n = ∫ x² pX + (∫ pX)·u n` are uniformly bounded by
`V := (∫ x² pX) + (∫ pX)·B` where `B` is any upper bound of `u`. This is the
`n`-uniform majorant that drives the (parked) negMulLog tail estimate.
@audit:ok -/
theorem convDensityAdd_second_moment_unif_bdd
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u)) :
    ∃ V : ℝ, ∀ n,
      ∫ x, x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x ∂volume ≤ V := by
  obtain ⟨B, hB⟩ := hu_bdd
  have hB_nn : ∀ n, u n ≤ B := fun n => hB ⟨n, rfl⟩
  have hmass_nn : 0 ≤ ∫ y, pX y ∂volume := integral_nonneg hpX_nn
  refine ⟨(∫ x, x ^ 2 * pX x ∂volume) + (∫ y, pX y ∂volume) * B, fun n => ?_⟩
  rw [convDensityAdd_second_moment hpX_nn hpX_meas hpX_int hpX_mom (hu_pos n)]
  have : (∫ y, pX y ∂volume) * u n ≤ (∫ y, pX y ∂volume) * B :=
    mul_le_mul_of_nonneg_left (hB_nn n) hmass_nn
  linarith

/-! ## UT witness removed

The Vitali UnifTight witness `negMulLog_convDensity_unifTight` (parked under
`wall:approx-identity-L1`) was the layer-2 (`differentialEntropy_convDensity_integral_tendsto`)
input on the Vitali route. The layer-2 body has been re-derived genuinely via the
two-sided sandwich (Fatou-LSC `(α)` limsup upper bound + conditioning
`(β)` per-`n` lower bound, both `@audit:ok`), so the Vitali UI/UT witnesses are no
longer consumed and the orphan UT witness is deleted. The genuine helpers
`convDensityAdd_second_moment` (still consumed by the `(α)` machinery and
`EPIVitaliUI`) and `convDensityAdd_second_moment_unif_bdd` are retained. -/

end InformationTheory.Shannon
