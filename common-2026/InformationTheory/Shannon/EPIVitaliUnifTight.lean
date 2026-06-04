import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIConvDensityAssoc
import InformationTheory.Shannon.FisherConvBound

/-!
# EPI G2 Vitali witness — UnifTight (UT)

Genuine standalone implementation of the `hut` input for the layer-2 Vitali
machinery (`differentialEntropy_convDensity_integral_tendsto`). The main lemma
`negMulLog_convDensity_unifTight` has the *exact same signature* as the parked
`EPIG2HeatFlowContinuity.negMulLog_convDensity_unifTight` (`:161`); the orchestrator
will delegate the parked version to this file.

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

/-- Gaussian first moment over `volume`: `∫ x · g_t(x) = 0` (centered at `0`). -/
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
moments `∫ g_t = 1`, `∫ x g_t = 0`, `∫ x² g_t = t`. -/
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
    InformationTheory.Shannon.FisherInfoV2.integrable_sq_mul_gaussianPDFReal ht
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
  rw [InformationTheory.Shannon.FisherInfoV2.integral_sq_mul_gaussianPDFReal ht,
    integral_id_mul_gaussianPDFReal ht, integral_gaussianPDFReal_eq_one 0 hv_ne]
  ring

/-- **Convolution-density second moment** (helper, in-tree absent).
For `f_t = pX ∗ g_t` (Gaussian kernel of variance `t`):
`∫ x², (convDensityAdd pX g_t) ∂volume = (∫ x², pX) + (∫ pX) · t`.

The intended proof is genuine and wall-free: lintegral-Tonelli on the nonneg
integrand `x² · pX(y) · g_t(x-y)` (`lintegral_lintegral_swap`, no prod-integrability
needed since the integrand is `ℝ≥0∞`-valued), then the inner moment
`integral_sq_mul_gaussianPDFReal_shift = y² + t`, then `∫ y² pX + (∫ pX)·t`. The two
Gaussian inner moments are already discharged above (`integral_sq_mul_gaussianPDFReal_shift`,
genuine). What remains is the Bochner↔lintegral conversion plumbing (per-`x`
integrability of the inner integrand, finiteness of the double integral for the
final `.toReal`). This is standard but laborious; parked for the closure plan. NOT
a Mathlib wall — purely a Tonelli/measurability assembly.
@residual(plan:epi-g2-vitali-closure-plan) -/
theorem convDensityAdd_second_moment
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume
      = (∫ x, x ^ 2 * pX x ∂volume) + (∫ y, pX y ∂volume) * t := by
  sorry

/-- **Layer 2 UT witness (genuine).** Uniform tightness of the entropy integrands
along any sequence `u : ℕ → ℝ` with `u n > 0`. Vitali input `hut`.

Same signature as `EPIG2HeatFlowContinuity.negMulLog_convDensity_unifTight` (`:161`).

The genuine reduction: `UnifTight` unfolds to "for every `ε`, some finite-measure
set `s` (here `s = Icc (-R) R`) with tail eLpNorm `≤ ε` uniformly in `n`". The
tail eLpNorm (`p = 1`) is the lintegral `∫⁻_{|x|>R} ‖negMulLog (f_n x)‖ₑ`. The
crux — bounding this uniformly in `n` by the second-moment tail of `f_n`
(`∫ x² f_n = ∫ x² pX + (∫ pX)·u n`, via `mul_meas_ge_le_lintegral` on `volume`) —
requires an elementary `|negMulLog t|`-vs-`t·(1+log-tail)` estimate combined with
the Gaussian log-tail `|log f_n(x)| ≲ 1 + x²`. There is no Mathlib bridge for this
(inventory category C / 自作 #2). Parked as the approximate-identity wall.

HONESTY FIX (2026-06-04): the second moment `∫ x² f_n = ∫ x² pX + (∫ pX)·u n` is
uniform in `n` only when `u` is bounded. Without it (`sup u n = ∞`) the tail mass
escapes to infinity and `UnifTight` genuinely FAILS — the previous signature
(`u : ℕ → ℝ` arbitrary positive) was under-hypothesised (a false claim in the sense
of CLAUDE.md「検証の誠実性」). The regularity precondition `hu_bdd : BddAbove
(Set.range u)` is now added to make the signature honest. The sole consumer
(`differentialEntropy_convDensity_integral_tendsto`) only instantiates with a
sequence `u → 0` (hence bounded), so the precondition is satisfied there. The
remaining residual is the genuine negMulLog tail bridge (`|negMulLog f_n| ≲
f_n·(1+log-tail)` vs the Gaussian log-tail `|log f_n| ≲ 1 + x²`), which has no
Mathlib bridge — the approximate-identity wall.
@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_unifTight
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u)) :
    UnifTight
      (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      1 volume := by
  sorry

end InformationTheory.Shannon
