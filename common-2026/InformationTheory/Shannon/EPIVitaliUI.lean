import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Distributions.Gaussian.Real
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIConvDensityAssoc
import InformationTheory.Shannon.EPIConvDensityNormalization
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIVitaliUnifTight
import InformationTheory.Shannon.FisherInfoV2DeBruijnAssembly

/-!
# EPI G2 Vitali witness — UnifIntegrable (UI), standalone genuine attempt

Genuine standalone implementation of the `hui` input for the layer-2 Vitali
machinery (`differentialEntropy_convDensity_integral_tendsto`). The main lemma
`negMulLog_convDensity_unifIntegrable` has the *same signature* as the parked
`EPIG2HeatFlowContinuity.negMulLog_convDensity_unifIntegrable` (`:165`) plus an
added probability-mass normalization precondition `hpX_mass : ∫ pX = 1` (a
regularity precondition supplied by the layer-2 consumer). The orchestrator will
delegate the parked version to this file (removing the EPIG2 copy).

## Strategy (inventory `epi-g2-ui-bridge-inventory.md`, 4 steps)

`f_n := convDensityAdd pX g_{u n} = pX ∗ g_{u n}`.

* **Step 1** (Mathlib in): `unifIntegrable_of` reduces UI to a *uniform* indicator-tail
  estimate `∀ ε>0, ∃ C, ∀ n, eLpNorm ({C ≤ |negMulLog (f_n)|}.indicator (negMulLog∘f_n)) 1 volume ≤ ofReal ε`.
* **Step 2** (probability-measure framing, genuine, option b = `withDensity` direct):
  `μ_n := volume.withDensity (ofReal∘f_n)` is a probability measure (`∫ f_n = 1` via
  `integral_convDensityAdd_gaussian_eq_one`), `≪ volume`, and `rnDeriv = ofReal∘f_n`.
  Hence `differentialEntropy μ_n = ∫ negMulLog f_n`.
* **Step 3** (maxent upper bound, in-tree `@entry_point`):
  `differentialEntropy_le_gaussian_of_variance_le` applied to `μ_n` gives
  `∫ negMulLog f_n ≤ (1/2) log(2πe V_n)` with `V_n = (∫ x² pX) + u n` `n`-uniform.
  Combined with `negMulLog_le_one_sub_self` (positive part) this gives a uniform
  bound `M` on `∫ |negMulLog f_n|`.
* **Step 4** (★ de la Vallée-Poussin bridge core, Mathlib-absent): "`∫|negMulLog f_n|`
  uniformly bounded → `∫⁻_{C≤|negMulLog f_n|}|negMulLog f_n| ≤ ε` uniformly (C large)".
  This is the genuine de la Vallée-Poussin content (superlinear moment) which has no
  Mathlib lemma. **Parked** as `wall:approx-identity-L1`; Steps 1-3 are genuine.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-! ## Genuine framing helpers (Steps 2-3) -/

/-- Measurability of `f_t = convDensityAdd pX g_t`. Genuine. -/
theorem convDensityAdd_gaussian_measurable {pX : ℝ → ℝ} (hpX_meas : Measurable pX)
    {t : ℝ} (ht : 0 < t) :
    Measurable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) :=
  convDensityAdd_pXpY_measurable pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_meas
    (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)

/-- Nonnegativity of `f_t = convDensityAdd pX g_t`. Genuine. -/
theorem convDensityAdd_gaussian_nonneg {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x :=
  convDensityAdd_pXpY_nonneg pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_nn
    (fun y => gaussianPDFReal_nonneg 0 ⟨t, ht.le⟩ y) x

/-- The smoothed-density measure `μ_t := volume.withDensity (ofReal ∘ f_t)` is a
probability measure (Step 2). Genuine via `integral_convDensityAdd_gaussian_eq_one`.

Independent honesty audit 2026-06-04 (fresh subagent, commit 825154f): genuine,
own sorry 0, `#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx-free,
machine-checked). The probability-measure conclusion is reconstructed from
`withDensity_apply` + `ofReal_integral_eq_lintegral_ofReal` + the genuine mass
identity `integral_convDensityAdd_gaussian_eq_one`; no measure value is bundled into
a hypothesis. All `hpX_*` are pX regularity preconditions; `hpX_mass : ∫ pX = 1` is
the probability-density normalisation (regularity, not load-bearing). NOT circular /
load-bearing / degenerate.
@audit:ok -/
theorem convDensityAdd_gaussian_isProbabilityMeasure {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure
      (volume.withDensity (fun x =>
        ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x))) := by
  set f : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hf_def
  have hf_int : Integrable f volume :=
    convDensityAdd_pXpY_integrable pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_int hpX_meas
      (integrable_gaussianPDFReal 0 ⟨t, ht.le⟩) (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)
  have hf_nn : ∀ x, 0 ≤ f x := fun x => convDensityAdd_gaussian_nonneg hpX_nn ht x
  have hf_mass : ∫ x, f x ∂volume = 1 :=
    integral_convDensityAdd_gaussian_eq_one pX ht hpX_int hpX_mass
  have hf_meas : Measurable f := convDensityAdd_gaussian_measurable hpX_meas ht
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int (Eventually.of_forall hf_nn)]
  rw [hf_mass]
  simp

/-- The differential entropy of the smoothed-density measure equals the entropy
integral of the density (Step 2). Genuine via `rnDeriv_withDensity`.

Independent honesty audit 2026-06-04 (fresh subagent, commit 825154f): genuine,
own sorry 0, `#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx-free,
machine-checked). The entropy-integral identity is reconstructed from
`Measure.rnDeriv_withDensity` + `ENNReal.toReal_ofReal` pushed through
`integral_congr_ae`; no entropy value is bundled into a hypothesis. `hpX_meas`/`hpX_nn`
are regularity preconditions. NOT circular / load-bearing / degenerate.
@audit:ok -/
theorem differentialEntropy_convDensityAdd_gaussian_eq {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    {t : ℝ} (ht : 0 < t) :
    differentialEntropy
        (volume.withDensity (fun x =>
          ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)))
      = ∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) ∂volume := by
  set f : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hf_def
  have hf_meas : Measurable f := convDensityAdd_gaussian_measurable hpX_meas ht
  have hf_nn : ∀ x, 0 ≤ f x := fun x => convDensityAdd_gaussian_nonneg hpX_nn ht x
  have hofReal_meas : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf_meas
  have hrn : (volume.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv volume
      =ᵐ[volume] fun x => ENNReal.ofReal (f x) :=
    Measure.rnDeriv_withDensity volume hofReal_meas
  rw [differentialEntropy]
  refine integral_congr_ae ?_
  filter_upwards [hrn] with x hx
  rw [hx, ENNReal.toReal_ofReal (hf_nn x)]

/-- **Second-moment integrability of `f_t` (helper, GENUINELY CLOSED).**
`x ↦ x² · f_t(x)` is `volume`-integrable. Genuine via the same lintegral-Tonelli chain
that closes `convDensityAdd_second_moment` (value version): lift the nonneg integrand
`K x y := x²·(pX y · g(x-y))` to `ℝ≥0∞`, swap with `lintegral_lintegral_swap`, collapse
the inner integral via the inline Gaussian shift moment `∫ x, x²·g(x-y) = y²+t`
(reconstructed from `∫ g = 1`, `∫ x·g = 0`, `∫ x²·g = t`, all public API), then the
outer lintegral is finite from `hpX_mom`+`hpX_int`; the `Integrable` conclusion follows
from AEStronglyMeasurable + finite norm-lintegral.

`#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-checked
2026-06-04 with fresh olean). All `hpX_*` are pX regularity preconditions; the conclusion
is an `Integrable` output, not bundled into any hypothesis. NOT load-bearing / circular /
degenerate. Closes one of the two `plan:epi-g2-vitali-closure-plan` moment residuals.

Independent honesty audit 2026-06-04 (fresh subagent, commit `3ce6f51`): `plan:` →
`@audit:ok` promotion CONFIRMED. `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free, fresh olean via `lake build` refresh + `lake env lean`). Body
Tonelli chain is genuine (lintegral lift → swap → inline Gaussian shift moment `∫x²g(x-y)
=y²+t` from public API → finite outer). No hidden wall, no circularity (this is the
primitive; `_id_integrable` dominates via it, not vice versa). Sufficiency holds (`hpX_mom`
supplies the 2nd moment the conclusion needs). `hpX_*` regularity, conclusion is
`Integrable` output.
@audit:ok -/
theorem convDensityAdd_gaussian_sq_integrable {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  set p_t : ℝ → ℝ := convDensityAdd pX g with hp_def
  -- The nonneg double-integrand `K x y := x² · (pX y · g (x - y)) ≥ 0`.
  set K : ℝ → ℝ → ℝ := fun x y => x ^ 2 * (pX y * g (x - y)) with hK_def
  have hK_nn : ∀ x y, 0 ≤ K x y := fun x y =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _))
  have hKofReal_meas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (K p.1 p.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine (measurable_fst.pow_const 2).mul ?_
    exact (hpX_meas.comp measurable_snd).mul
      ((measurable_gaussianPDFReal 0 ⟨t, ht.le⟩).comp (measurable_fst.sub measurable_snd))
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
  have hsq_mom_int : Integrable (fun u => u ^ 2 * g u) volume := by
    simpa [hg_def] using
      InformationTheory.Shannon.FisherInfoV2.integrable_sq_mul_gaussianPDFReal ht
  -- ── Step A: lift LHS to a double lintegral over `(x,y)`. ──
  have hLHS_inner : ∀ x, x ^ 2 * p_t x = ∫ y, K x y ∂volume := by
    intro x
    rw [hp_def]; unfold convDensityAdd
    rw [← integral_const_mul]
  have hLHS_lint : (∫⁻ x, ENNReal.ofReal (x ^ 2 * p_t x) ∂volume)
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂volume ∂volume := by
    refine lintegral_congr fun x => ?_
    rw [hLHS_inner x]
    refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun y => hK_nn x y)
    refine ((hconv_int x).const_mul (x ^ 2)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hK_def]
  -- ── Step B: Tonelli swap + inner Gaussian moment `∫_x x²·g(x-y) = y²+t`. ──
  have hswap : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂volume ∂volume)
      = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (K x y) ∂volume ∂volume :=
    lintegral_lintegral_swap hKofReal_meas.aemeasurable
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
    have hexp : Integrable (fun u => (u + y) ^ 2 * g u) volume := by
      have : Integrable
          (fun u => u ^ 2 * g u + 2 * y * (u * g u) + y ^ 2 * g u) volume :=
        (hsq_mom_int.add (hid_g_int.const_mul (2 * y))).add (hg_int.const_mul (y ^ 2))
      refine this.congr (Filter.Eventually.of_forall fun u => ?_); ring
    have := hexp.comp_sub_right y
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_add_cancel]
  have hxint : ∀ y, Integrable (fun x => K x y) volume := fun y => by
    refine ((hsq_shift_int y).const_mul (pX y)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hK_def]; ring
  -- inner Gaussian shift moment `∫ x, x²·g(x-y) = y²+t` (reconstructed inline, public API).
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  have hid_mom0 : ∫ x, x * g x ∂volume = 0 := by
    calc ∫ x, x * g x ∂volume
        = ∫ x, g x • x ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [hg_def, smul_eq_mul, mul_comm]
      _ = ∫ x, x ∂(gaussianReal 0 ⟨t, ht.le⟩) := by
          rw [hg_def]
          exact (integral_gaussianReal_eq_integral_smul (μ := 0) (f := fun x => x) hv_ne).symm
      _ = 0 := ProbabilityTheory.integral_id_gaussianReal
  have hsq_mom0 : ∫ x, x ^ 2 * g x ∂volume = t := by
    simpa [hg_def] using
      InformationTheory.Shannon.FisherInfoV2.integral_sq_mul_gaussianPDFReal ht
  have hg_mom0 : ∫ x, g x ∂volume = 1 := by
    rw [hg_def]; exact integral_gaussianPDFReal_eq_one 0 hv_ne
  have hshift : ∀ y, ∫ x, x ^ 2 * g (x - y) ∂volume = y ^ 2 + t := by
    intro y
    have hsub : ∫ x, x ^ 2 * g (x - y) ∂volume
        = ∫ x, (x + y) ^ 2 * g x ∂volume := by
      have := MeasureTheory.integral_add_right_eq_self
        (μ := volume) (fun x => x ^ 2 * g (x - y)) y
      simp only [add_sub_cancel_right] at this
      rw [← this]
    rw [hsub]
    have hexpand : ∀ x : ℝ,
        (x + y) ^ 2 * g x
          = x ^ 2 * g x + 2 * y * (x * g x) + y ^ 2 * g x := by
      intro x; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
    rw [integral_add (by exact hsq_mom_int.add ((hid_g_int.const_mul (2 * y)))) (hg_int.const_mul (y ^ 2)),
      integral_add hsq_mom_int (hid_g_int.const_mul (2 * y)),
      integral_const_mul, integral_const_mul]
    rw [hsq_mom0, hid_mom0, hg_mom0]
    ring
  have hinner : ∀ y, (∫⁻ x, ENNReal.ofReal (K x y) ∂volume)
      = ENNReal.ofReal (pX y * (y ^ 2 + t)) := by
    intro y
    rw [← ofReal_integral_eq_lintegral_ofReal (hxint y)
      (Filter.Eventually.of_forall fun x => hK_nn x y)]
    congr 1
    rw [show (fun x => K x y) = (fun x => pX y * (x ^ 2 * g (x - y))) from by
      funext x; simp only [hK_def]; ring, integral_const_mul]
    rw [hshift y]
  -- ── Step C: outer integral over `y`. ──
  have hpX_polymom_int : Integrable (fun y => pX y * (y ^ 2 + t)) volume := by
    have : Integrable (fun y => y ^ 2 * pX y + pX y * t) volume :=
      hpX_mom.add (hpX_int.mul_const t)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_); ring
  have houter : (∫⁻ y, ENNReal.ofReal (pX y * (y ^ 2 + t)) ∂volume)
      = ENNReal.ofReal (∫ y, pX y * (y ^ 2 + t) ∂volume) :=
    (ofReal_integral_eq_lintegral_ofReal hpX_polymom_int
      (Filter.Eventually.of_forall fun y =>
        mul_nonneg (hpX_nn y) (by positivity))).symm
  -- ── Assemble: `Integrable` via AEStronglyMeasurable + finite lintegral of norm. ──
  have hmeas : AEStronglyMeasurable (fun x => x ^ 2 * p_t x) volume := by
    refine (measurable_id.pow_const 2).aestronglyMeasurable.mul ?_
    rw [hp_def]
    exact (convDensityAdd_pXpY_measurable pX g hpX_meas
      (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hnorm : (fun x => (‖x ^ 2 * p_t x‖ₑ : ℝ≥0∞))
      = (fun x => ENNReal.ofReal (x ^ 2 * p_t x)) := by
    funext x
    rw [Real.enorm_eq_ofReal (mul_nonneg (sq_nonneg _) (hp_nn x))]
  rw [hnorm, hLHS_lint, hswap]
  simp_rw [hinner]
  rw [houter]
  exact ENNReal.ofReal_lt_top

/-- **First-moment integrability of `f_t` (helper, GENUINELY CLOSED).**
`x ↦ x · f_t(x)` is `volume`-integrable. Genuine via majorant domination
(`Integrable.mono'`): since `f_t ≥ 0` and `|x| ≤ (1 + x²)/2`, we have
`‖x·f_t x‖ = |x|·f_t x ≤ (f_t x + x²·f_t x)/2`, and the majorant is integrable from
`f_t` integrability (`convDensityAdd_pXpY_integrable`) + second-moment integrability
(`convDensityAdd_gaussian_sq_integrable`, above). No Gaussian absolute-moment computation
needed.

`#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-checked
2026-06-04 with fresh olean). All `hpX_*` are pX regularity preconditions; the conclusion
is an `Integrable` output, not bundled into any hypothesis. NOT load-bearing / circular /
degenerate. Closes the second `plan:epi-g2-vitali-closure-plan` moment residual.

Independent honesty audit 2026-06-04 (fresh subagent, commit `3ce6f51`): `plan:` →
`@audit:ok` promotion CONFIRMED. `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free, fresh olean). Majorant `(f_t + x²·f_t)/2` is genuine: `f_t`
integrable (`convDensityAdd_pXpY_integrable`) + sq version (`_sq_integrable`, just
promoted, sorryAx-free). No circular dependency. Sufficiency holds (`|x| ≤ (1+x²)/2`
domination is correct). `hpX_*` regularity, conclusion is `Integrable` output.
@audit:ok -/
theorem convDensityAdd_gaussian_id_integrable {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => x * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  set p_t : ℝ → ℝ := convDensityAdd pX g with hp_def
  have hp_nn : ∀ x, 0 ≤ p_t x := fun x => convDensityAdd_gaussian_nonneg hpX_nn ht x
  have hf_int : Integrable p_t volume := by
    rw [hp_def]
    exact convDensityAdd_pXpY_integrable pX g hpX_int hpX_meas
      (integrable_gaussianPDFReal 0 ⟨t, ht.le⟩) (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)
  have hsq_int : Integrable (fun x => x ^ 2 * p_t x) volume := by
    rw [hp_def]
    exact convDensityAdd_gaussian_sq_integrable hpX_nn hpX_meas hpX_int hpX_mom ht
  -- Majorant `|x|·p_t x ≤ (p_t x + x²·p_t x)/2` (from `|x| ≤ (1+x²)/2`, `p_t ≥ 0`).
  have hmaj_int : Integrable (fun x => (p_t x + x ^ 2 * p_t x) / 2) volume :=
    (hf_int.add hsq_int).div_const 2
  refine Integrable.mono' hmaj_int ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (measurable_id.mul (convDensityAdd_gaussian_measurable hpX_meas ht)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hp_nn x)]
    have habs_le : |x| ≤ (1 + x ^ 2) / 2 := by nlinarith [sq_nonneg (|x| - 1), abs_nonneg x, sq_abs x]
    calc |x| * p_t x ≤ ((1 + x ^ 2) / 2) * p_t x :=
          mul_le_mul_of_nonneg_right habs_le (hp_nn x)
      _ = (p_t x + x ^ 2 * p_t x) / 2 := by ring

/-- **Maxent upper bound (Step 3, GENUINELY CLOSED).** The entropy integral
`∫ negMulLog f_t` is bounded above by the Gaussian max-entropy `(1/2) log(2πe·V)` with
`V = (∫ x² pX) + t`. Genuine via `differentialEntropy_le_gaussian_of_variance_le` on
`μ_t`. The variance moments are supplied by `convDensityAdd_second_moment` (value) and
the now-genuine moment-integrability helpers `convDensityAdd_gaussian_sq_integrable` /
`_id_integrable`; the maxent application itself is a genuine reduction.

`#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-checked
2026-06-04 with fresh olean, after closing the two moment-integrability helpers). Own
body is `sorry`-free; the variance bound is built from `convDensityAdd_second_moment`
(genuine) via `withDensity` moment transfer, NOT bundled into a hypothesis. `hV`/`hV0`
constrain the auxiliary variance majorant `V` (regularity for the maxent application,
not a bundled entropy value). NOT load-bearing / circular; sufficiency holds (maxent
inequality follows from the variance bound).

Independent honesty audit 2026-06-04 (fresh subagent, commit `3ce6f51`): transitive
`@audit:ok` promotion CONFIRMED. `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free, fresh olean) — the two moment helpers' closure genuinely
discharged the transitive residuals, and the entropy-integrand `hbase` consumer
`FisherInfoV2.convDensityAdd_negMulLog_integrable` is itself `@audit:ok` (entropy-finiteness
wall CLOSED). Maxent application `differentialEntropy_le_gaussian_of_variance_le`
(DifferentialEntropy.lean:520) is genuine (no sorry leaked). Sufficiency holds: conclusion
is the Gaussian maxent bound, follows from `h_var : ∫(x-m)² ∂μ ≤ V`; `hV`/`hV0` constrain
the auxiliary majorant `V`, not the entropy value. Conclusion is an upper-bound inequality,
not bundled into any hypothesis.
@audit:ok -/
theorem negMulLog_convDensityAdd_gaussian_entropy_upper {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t)
    {V : ℝ≥0} (hV : (∫ x, x ^ 2 * pX x ∂volume) + t ≤ (V : ℝ)) (hV0 : V ≠ 0) :
    (∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) ∂volume)
      ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * V) := by
  classical
  -- Establish all facts about the convolution density `f` and the framing measure `μ`
  -- *before* making them opaque, then `clear_value` to stop downstream tactics
  -- (`measure_univ`, `integral_const`, typeclass search) from unfolding `μ`/`f` to the
  -- convolution density (which blows up `isDefEq`). The defining equations
  -- `hf_def`/`hμ_def` remain available as ordinary hypotheses.
  have hf_nn : ∀ x, 0 ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x :=
    fun x => convDensityAdd_gaussian_nonneg hpX_nn ht x
  have hf_meas : Measurable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) :=
    convDensityAdd_gaussian_measurable hpX_meas ht
  have hf_int : Integrable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) volume :=
    convDensityAdd_pXpY_integrable pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_int hpX_meas
      (integrable_gaussianPDFReal 0 ⟨t, ht.le⟩) (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)
  have hf_mass : ∫ x, convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume = 1 :=
    integral_convDensityAdd_gaussian_eq_one pX ht hpX_int hpX_mass
  set f : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hf_def
  set μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (f x)) with hμ_def
  haveI hμ_prob : IsProbabilityMeasure μ := by
    rw [hμ_def, hf_def]
    exact convDensityAdd_gaussian_isProbabilityMeasure hpX_nn hpX_meas hpX_int hpX_mass ht
  have hμ_ac : μ ≪ volume := withDensity_absolutelyContinuous volume _
  have hofReal_lt : ∀ᵐ x ∂volume, ENNReal.ofReal (f x) < ∞ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  clear_value μ f
  -- `∫ g ∂μ = ∫ f · g ∂volume` for any `g`.
  have htransfer : ∀ g : ℝ → ℝ, ∫ x, g x ∂μ = ∫ x, f x * g x ∂volume := by
    intro g
    have hstep : ∫ x, g x ∂μ
        = ∫ x, (ENNReal.ofReal (f x)).toReal • g x ∂volume := by
      rw [hμ_def]
      exact integral_withDensity_eq_integral_toReal_smul
        (ENNReal.measurable_ofReal.comp hf_meas) hofReal_lt g
    rw [hstep]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul]
  -- Moments transferred to `volume`.
  set m : ℝ := ∫ x, x ∂μ with hm_def
  have hsq_int : Integrable (fun x => x ^ 2 * f x) volume := by
    rw [hf_def]; exact convDensityAdd_gaussian_sq_integrable hpX_nn hpX_meas hpX_int hpX_mom ht
  have hid_int : Integrable (fun x => x * f x) volume := by
    rw [hf_def]; exact convDensityAdd_gaussian_id_integrable hpX_nn hpX_meas hpX_int hpX_mom ht
  have hsq_val : ∫ x, x ^ 2 * f x ∂volume = (∫ x, x ^ 2 * pX x ∂volume) + t := by
    have h := convDensityAdd_second_moment hpX_nn hpX_meas hpX_int hpX_mom ht
    rw [hf_def, h, hpX_mass]; ring
  -- `∫ x ∂μ = m` (definition).
  have h_mean : ∫ x, x ∂μ = m := rfl
  -- `∫ x² ∂μ = ∫ x² f`.
  have hsqμ : ∫ x, x ^ 2 ∂μ = (∫ x, x ^ 2 * pX x ∂volume) + t := by
    rw [htransfer (fun x => x ^ 2)]
    simp only [mul_comm (f _)]
    rw [hsq_val]
  -- `∫ x ∂μ = ∫ x f`, integrable transfer for variance expansion.
  have hidμ_eq : ∫ x, x ∂μ = ∫ x, x * f x ∂volume := by
    rw [htransfer (fun x => x)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_); ring
  -- Variance ≤ second moment: `∫ (x-m)² ∂μ = ∫ x² ∂μ - m² ≤ ∫ x² ∂μ`.
  -- Integrability of `x ↦ (x - m)²` wrt `μ`.
  have hvar_int_vol : Integrable (fun x => f x * (x - m) ^ 2) volume := by
    have hexp : ∀ x, f x * (x - m) ^ 2
        = (x ^ 2 * f x) - (2 * m) * (x * f x) + (m ^ 2) * f x := by
      intro x; ring
    rw [integrable_congr (Eventually.of_forall hexp)]
    exact (hsq_int.sub (hid_int.const_mul (2 * m))).add (hf_int.const_mul (m ^ 2))
  have hvar_int : Integrable (fun x => (x - m) ^ 2) μ := by
    have hiff := integrable_withDensity_iff_integrable_smul₀'
      (μ := volume) (f := fun x => ENNReal.ofReal (f x))
      (ENNReal.measurable_ofReal.comp hf_meas).aemeasurable hofReal_lt (g := fun x => (x - m) ^ 2)
    rw [hμ_def]
    refine hiff.mpr (hvar_int_vol.congr (Eventually.of_forall fun x => ?_))
    simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul]
  -- Variance bound.
  have h_var : ∫ x, (x - m) ^ 2 ∂μ ≤ (V : ℝ) := by
    have hvar_eq : ∫ x, (x - m) ^ 2 ∂μ = (∫ x, x ^ 2 ∂μ) - m ^ 2 := by
      have hxsq_int : Integrable (fun x => x ^ 2) μ := by
        have hiff := integrable_withDensity_iff_integrable_smul₀'
          (μ := volume) (f := fun x => ENNReal.ofReal (f x))
          (ENNReal.measurable_ofReal.comp hf_meas).aemeasurable hofReal_lt (g := fun x => x ^ 2)
        rw [hμ_def]
        refine hiff.mpr ((hsq_int).congr (Eventually.of_forall fun x => ?_))
        simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul, mul_comm]
      have hx_int : Integrable (fun x => x) μ := by
        have hiff := integrable_withDensity_iff_integrable_smul₀'
          (μ := volume) (f := fun x => ENNReal.ofReal (f x))
          (ENNReal.measurable_ofReal.comp hf_meas).aemeasurable hofReal_lt (g := fun x => x)
        rw [hμ_def]
        refine hiff.mpr ((hid_int).congr (Eventually.of_forall fun x => ?_))
        simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul, mul_comm]
      have hexpand : ∀ x : ℝ, (x - m) ^ 2 = (x ^ 2 - (2 * m) * x) + m ^ 2 := by
        intro x; ring
      calc ∫ x, (x - m) ^ 2 ∂μ
          = ∫ x, (fun x => x ^ 2 - (2 * m) * x) x + (fun _ => m ^ 2) x ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_); simpa using hexpand x
        _ = (∫ x, (x ^ 2 - (2 * m) * x) ∂μ) + ∫ _, m ^ 2 ∂μ :=
            integral_add ((hxsq_int).sub (hx_int.const_mul (2 * m))) (integrable_const _)
        _ = ((∫ x, x ^ 2 ∂μ) - ∫ x, (2 * m) * x ∂μ) + ∫ _, m ^ 2 ∂μ := by
            rw [integral_sub hxsq_int (hx_int.const_mul (2 * m))]
        _ = ((∫ x, x ^ 2 ∂μ) - (2 * m) * (∫ x, x ∂μ)) + m ^ 2 := by
            rw [integral_const_mul, integral_const, probReal_univ]
            simp only [smul_eq_mul, one_mul]
        _ = (∫ x, x ^ 2 ∂μ) - m ^ 2 := by
            rw [← h_mean, ← hm_def]; ring
    rw [hvar_eq, hsqμ]
    have hm_sq_nonneg : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
    linarith [hV]
  -- `h_ent_int`: integrability of the entropy integrand.
  have h_ent_int : Integrable
      (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume := by
    have hrn : (μ.rnDeriv volume) =ᵐ[volume] fun x => ENNReal.ofReal (f x) := by
      rw [hμ_def]; exact Measure.rnDeriv_withDensity volume (ENNReal.measurable_ofReal.comp hf_meas)
    have hbase : Integrable (fun x => Real.negMulLog (f x)) volume := by
      rw [hf_def]
      exact InformationTheory.Shannon.FisherInfoV2.convDensityAdd_negMulLog_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
    refine hbase.congr ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (hf_nn x)]
  -- Apply maxent.
  have hmaxent := differentialEntropy_le_gaussian_of_variance_le
    (μ := μ) hμ_ac m hV0 h_mean h_var hvar_int h_ent_int
  -- Rewrite `differentialEntropy μ = ∫ negMulLog f`.
  have hent_eq : differentialEntropy μ
      = ∫ x, Real.negMulLog (f x) ∂volume := by
    rw [hμ_def, hf_def]
    exact differentialEntropy_convDensityAdd_gaussian_eq hpX_nn hpX_meas ht
  rw [hent_eq, hf_def] at hmaxent
  rw [hf_def]
  exact hmaxent

/-! ## de la Vallée-Poussin bridge core (Step 4, parked) -/

/-- **de la Vallée-Poussin bridge core (Step 4, ★ Mathlib-absent).**
The uniform indicator-tail input required by `unifIntegrable_of`: for every `ε > 0`,
there is a threshold `C` such that the tail eLpNorm of `negMulLog (f_n)` above `C` is
`≤ ε` uniformly in `n`. The maxent upper bound (Step 3) controls `∫ negMulLog f_n`
uniformly, but the de la Vallée-Poussin step — turning a uniform bound on
`∫ |negMulLog f_n|` into a uniform tail `∫⁻_{C ≤ |negMulLog f_n|} |negMulLog f_n| → 0`
— requires a superlinear-moment argument absent from Mathlib (inventory category B,
loogle: 0 hits for any de la Vallée-Poussin / superlinear-moment → UnifIntegrable
lemma). Parked as the approximate-identity wall.

Independent honesty audit 2026-06-04 (fresh subagent, commit 825154f): honest_residual,
`wall:approx-identity-L1` classification CORRECT. The wall is loogle-confirmed Mathlib-
absent: `Real.negMulLog` + `MeasureTheory.Integrable` = 0 declarations;
`MeasureTheory.UnifTight` returns only structural lemmas (`aeeq`/`neg`/`const`/`finite`),
no de la Vallée-Poussin superlinear-moment constructor. Signature is honest: the
conclusion is the genuine intermediate proposition "uniform indicator-tail eLpNorm ≤ ε"
(a tail-smallness statement), NOT the `UnifIntegrable` conclusion bundled as a
hypothesis — `negMulLog_convDensity_unifIntegrable` genuinely reduces TO this via
`unifIntegrable_of`. All `hpX_*`/`hu_*` are regularity preconditions. NOT load-bearing.
@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_indicatorTail_uniform
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      eLpNorm
        ({ x | C ≤ ‖Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)‖₊ }.indicator
          (fun x => Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)))
        1 volume ≤ ENNReal.ofReal ε := by
  sorry

/-! ## Main UI witness (Step 1, genuine reduction to Step 4) -/

/-- **Layer 2 UI witness.** Uniform integrability of the entropy integrands along any
sequence `u : ℕ → ℝ` with `u n > 0` and bounded range. Vitali input `hui`.

Same signature as `EPIG2HeatFlowContinuity.negMulLog_convDensity_unifIntegrable`
(`:165`) plus the probability-mass normalization precondition `hpX_mass : ∫ pX = 1`
(regularity, supplied by the layer-2 consumer). The genuine reduction (`unifIntegrable_of`,
`[IsFiniteMeasure]`-free) delegates the uniform indicator-tail input to the parked de
la Vallée-Poussin bridge core `negMulLog_convDensity_indicatorTail_uniform`
(`wall:approx-identity-L1`). The framing/maxent helpers (Steps 2-3) are genuine.

NOT load-bearing: this body is the genuine Step-1 reduction. Its only own residual is
transitive, through the parked de la Vallée-Poussin bridge core
(`wall:approx-identity-L1`); the framing/maxent helpers (Steps 2-3) are genuine modulo
the parked moment-integrability plumbing (`plan:epi-g2-vitali-closure-plan`).

Independent honesty audit 2026-06-04 (fresh subagent, commit 825154f): honest_residual
(transitive only), PASS. Own body is the genuine Step-1 reduction: `unifIntegrable_of`
(`[IsFiniteMeasure]`-free, so valid on infinite `volume`) discharges the
AEStronglyMeasurable side via `continuous_negMulLog.comp_aestronglyMeasurable`, and
delegates the uniform indicator-tail input genuinely to the parked de la Vallée-Poussin
core `negMulLog_convDensity_indicatorTail_uniform`. The `UnifIntegrable` conclusion is
NOT bundled into any hypothesis — it is genuinely reconstructed by the constructor; the
single hard step (uniform tail) is the parked core, a genuine intermediate proposition
(not the UI conclusion). `#print axioms` carries `sorryAx` purely transitively through
that wall. `hpX_mass : ∫ pX = 1` (probability framing) and `hu_bdd` are regularity
preconditions, not load-bearing. "genuine but transitive residual" is the honest
shape (audit-tags.md tier 2 / transitive-sorry): own sorry 0, residual via the parked
core. NOT load-bearing / circular / degenerate; sufficiency holds. -/
theorem negMulLog_convDensity_unifIntegrable
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u)) :
    UnifIntegrable
      (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      1 volume := by
  -- Step 1: reduce UnifIntegrable to the uniform indicator-tail estimate via
  -- `unifIntegrable_of` (`[IsFiniteMeasure]`-free, so usable on `volume`).
  refine unifIntegrable_of (le_refl 1) ENNReal.one_ne_top (fun n => ?_) (fun ε hε => ?_)
  · -- AEStronglyMeasurable of `negMulLog ∘ f_n`.
    refine Real.continuous_negMulLog.comp_aestronglyMeasurable ?_
    exact (convDensityAdd_gaussian_measurable hpX_meas (hu_pos n)).aestronglyMeasurable
  · -- The uniform indicator-tail input is the parked de la Vallée-Poussin bridge core.
    exact negMulLog_convDensity_indicatorTail_uniform hpX_nn hpX_meas hpX_int hpX_mass
      hpX_mom u hu_pos hu_bdd hε

end InformationTheory.Shannon
