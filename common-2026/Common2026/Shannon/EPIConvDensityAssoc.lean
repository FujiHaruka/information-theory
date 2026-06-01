import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.EPIConvDensityNormalization
import Common2026.Shannon.EPIBlachmanGaussianWitness
import Common2026.Shannon.FisherInfoV2DeBruijnAssembly
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Prod

/-!
# Convolution-density associativity + 4-fold interchange bridge (EPI A-5 precondition (3))

Closes the `int_fisherZ` retreat of `EPIBlachmanGeneralDensity.lean`: the conv-of-conv
`convDensityAdd (convDensityAdd pX g_t) (convDensityAdd pY g_t)` equals
`convDensityAdd (convDensityAdd pX pY) g_{2t}` (variance-2t conv-with-Gaussian), which
then closes Fisher integrability via `convDensityAdd_fisher_integrand_integrable`.

## Route

1. **`convDensityAdd_assoc`** — `conv(conv(a,b),c) = conv(a,conv(b,c))`, via the bridge
   `convDensityAdd = ⋆[mul ℝ ℝ, volume]` (definitional, from the normalization file) and
   Mathlib `MeasureTheory.convolution_assoc` (all four bilinear maps `= mul ℝ ℝ`,
   compatibility `(x*y)*z = x*(y*z)` is `mul_assoc`). The `ConvolutionExistsAt` side
   conditions reduce to integrand integrability, supplied for nonneg integrable functions
   with a bounded (Gaussian-kernel) factor.
2. **`convDensityAdd_convGaussian_interchange`** — assoc + `convDensityAdd_comm` rearrange
   `(pX∗g)∗(pY∗g) = (pX∗pY)∗(g∗g)`, then variance-doubling `g_t ∗ g_t = g_{2t}` via
   `convDensityAdd_gaussian_closed_form` (`mX=mY=0`, `vX=vY=⟨t,_⟩`, sum `⟨2t,_⟩`).

## Regularity helpers (Part B consumer needs these for `convDensityAdd pX pY`)

`convDensityAdd_pXpY_nonneg` / `_measurable` / `_integrable` / `_integral_eq` — the
`convDensityAdd (convDensityAdd pX pY) g_{2t}` arm needs `pX∗pY` to be a normalized
probability density (nonneg, measurable, integrable, mass 1).

@audit:ok (file-level, regularity helpers) — independent honesty audit (2026-06-01):
`convolutionExistsAt_of_integrable_bdd`, `convDensityAdd_pXpY_measurable`,
`convDensityAdd_bdd_of_integrable_bdd`, `convDensityAdd_pXpY_nonneg`,
`convDensityAdd_pXpY_integrable`, `convDensityAdd_pXpY_integral_eq` are all constructive
regularity lemmas (integrand integrability / measurability / global bound / nonneg / mass)
with only regularity hypotheses; no circular / `:True` / bundled-core / degenerate shape.
sorryAx-free transitively (the consuming `convDensityAdd_convGaussian_interchange` is
machine-confirmed `[propext, Classical.choice, Quot.sound]`).
-/

namespace InformationTheory.Shannon.EPIConvDensity

open MeasureTheory Real ProbabilityTheory
open scoped NNReal Convolution

/-- **Convolution-density bridge**: `convDensityAdd a b = a ⋆[mul ℝ ℝ, volume] b`
(definitional, via `ContinuousLinearMap.mul_apply'`).
@audit:ok — independent honesty audit (2026-06-01): definitional unfold, no hypotheses,
sorryAx-free (transitively via the consuming bridge). -/
theorem convDensityAdd_eq_convolution (a b : ℝ → ℝ) :
    convDensityAdd a b = fun z => (convolution a b (ContinuousLinearMap.mul ℝ ℝ) volume) z := by
  funext z
  unfold convDensityAdd convolution
  simp only [ContinuousLinearMap.mul_apply']

/-- `ConvolutionExistsAt` for two integrable functions, one of which is bounded. -/
theorem convolutionExistsAt_of_integrable_bdd (a b : ℝ → ℝ)
    (ha_int : Integrable a volume) (hb_meas : Measurable b)
    (hb_bdd : ∃ M, ∀ x, |b x| ≤ M) (z : ℝ) :
    ConvolutionExistsAt a b z (ContinuousLinearMap.mul ℝ ℝ) volume := by
  obtain ⟨M, hM⟩ := hb_bdd
  have : Integrable (fun x => a x * b (z - x)) volume :=
    ha_int.mul_bdd
      ((hb_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (c := M) (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hM (z - x))
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using this

/-- Measurability of `convDensityAdd pX pY`. -/
theorem convDensityAdd_pXpY_measurable (pX pY : ℝ → ℝ)
    (hpX_meas : Measurable pX) (hpY_meas : Measurable pY) :
    Measurable (convDensityAdd pX pY) := by
  have huncurry :
      StronglyMeasurable
        (Function.uncurry fun z x => pX x * pY (z - x)) := by
    apply Measurable.stronglyMeasurable
    apply (hpX_meas.comp measurable_snd).mul
    exact hpY_meas.comp ((measurable_fst).sub measurable_snd)
  have h := huncurry.integral_prod_right (ν := volume)
  simpa only [convDensityAdd] using h.measurable

/-- Global bound of `convDensityAdd a b` when one factor is bounded:
`|conv a b z| ≤ (∫|a|)·M`. (Stated for `a` nonneg so `∫|a| = ∫a`.) -/
theorem convDensityAdd_bdd_of_integrable_bdd (a b : ℝ → ℝ)
    (ha_nn : ∀ x, 0 ≤ a x) (ha_int : Integrable a volume)
    (hb_bdd : ∃ M, ∀ x, |b x| ≤ M) :
    ∃ M, ∀ z, |convDensityAdd a b z| ≤ M := by
  obtain ⟨M, hM⟩ := hb_bdd
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  refine ⟨(∫ x, a x ∂volume) * M, fun z => ?_⟩
  have hge : ∀ x, |a x * b (z - x)| ≤ a x * M := by
    intro x
    rw [abs_mul, abs_of_nonneg (ha_nn x)]
    exact mul_le_mul_of_nonneg_left (hM (z - x)) (ha_nn x)
  calc |convDensityAdd a b z| = |∫ x, a x * b (z - x) ∂volume| := rfl
    _ ≤ ∫ x, |a x * b (z - x)| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ x, a x * M ∂volume := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => abs_nonneg _) (ha_int.mul_const M)
          (Filter.Eventually.of_forall hge)
    _ = (∫ x, a x ∂volume) * M := by rw [integral_mul_const]

/-- **Associativity of the convolution density**: `conv(conv(a,b),c) = conv(a,conv(b,c))`.
Via the bridge `convDensityAdd = ⋆[mul ℝ ℝ, volume]` and Mathlib `convolution_assoc`.
Requires nonneg + integrable data; only the **third** factor `c` need be bounded (so that
the `‖b‖ ⋆ ‖c‖`-at-`x₀` existence holds everywhere). The `a ⋆ b` and `‖b‖ ⋆ ‖c‖` existence
are a.e. from `Integrable.ae_convolution_exists` (`a`, `b` may both be unbounded `L¹`).
@audit:ok — independent honesty audit (2026-06-01): all hypotheses are regularity
(nonneg / Integrable / Measurable / bounded-third-factor); the conclusion (assoc equality)
follows genuinely from Mathlib `convolution_assoc` (loogle-confirmed present) with all four
bilinear maps `= mul ℝ ℝ` and compatibility discharged by `ring`. The bounded-third-factor
restriction is an honest *sufficient* condition for the `ConvolutionExistsAt` side conditions
(a.e. existence via `Integrable.ae_convolution_exists`), not a false-as-framed weakening —
no counterexample for the stated hypotheses. sorryAx-free (transitive via bridge). -/
theorem convDensityAdd_assoc (a b c : ℝ → ℝ)
    (ha_nn : ∀ x, 0 ≤ a x) (ha_int : Integrable a volume) (ha_meas : Measurable a)
    (hb_nn : ∀ x, 0 ≤ b x) (hb_int : Integrable b volume) (hb_meas : Measurable b)
    (hc_nn : ∀ x, 0 ≤ c x) (hc_int : Integrable c volume) (hc_meas : Measurable c)
    (hc_bdd : ∃ M, ∀ x, |c x| ≤ M) :
    convDensityAdd (convDensityAdd a b) c = convDensityAdd a (convDensityAdd b c) := by
  classical
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ with hL_def
  -- `|b|`, `|c|`, `|a|` agree with `b`, `c`, `a` (nonneg), so norm-convolutions equal plain ones.
  have hb_abs : (fun x => ‖b x‖) = b := by funext x; rw [Real.norm_eq_abs, abs_of_nonneg (hb_nn x)]
  have hc_abs : (fun x => ‖c x‖) = c := by funext x; rw [Real.norm_eq_abs, abs_of_nonneg (hc_nn x)]
  have ha_abs : (fun x => ‖a x‖) = a := by funext x; rw [Real.norm_eq_abs, abs_of_nonneg (ha_nn x)]
  -- Identify both convDensityAdd sides with Mathlib convolution.
  have hbridge : ∀ u v : ℝ → ℝ, convDensityAdd u v = (u ⋆[L, volume] v) :=
    fun u v => convDensityAdd_eq_convolution u v
  rw [hbridge, hbridge, hbridge, hbridge]
  funext x₀
  refine MeasureTheory.convolution_assoc L L L L
    (fun x y z => by simp only [hL_def, ContinuousLinearMap.mul_apply']; ring)
    ha_meas.aestronglyMeasurable hb_meas.aestronglyMeasurable hc_meas.aestronglyMeasurable
    (MeasureTheory.Integrable.ae_convolution_exists L ha_int hb_int) ?_ ?_
  · -- hgk: ∀ᵐ x, ConvolutionExistsAt ‖b‖ ‖c‖ x (mul) volume
    rw [hb_abs, hc_abs]
    exact MeasureTheory.Integrable.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ)
      hb_int hc_int
  · -- hfgk: ConvolutionExistsAt ‖a‖ (‖b‖ ⋆ ‖c‖) x₀ (mul) volume
    rw [ha_abs, hb_abs, hc_abs]
    have hbc_eq : (b ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] c) = convDensityAdd b c :=
      (convDensityAdd_eq_convolution b c).symm
    rw [hbc_eq]
    refine convolutionExistsAt_of_integrable_bdd a (convDensityAdd b c) ha_int
      (convDensityAdd_pXpY_measurable b c hb_meas hc_meas) ?_ x₀
    exact convDensityAdd_bdd_of_integrable_bdd b c hb_nn hb_int hc_bdd

/-- Nonnegativity of `convDensityAdd pX pY` (pointwise). -/
theorem convDensityAdd_pXpY_nonneg (pX pY : ℝ → ℝ)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpY_nn : ∀ x, 0 ≤ pY x) (z : ℝ) :
    0 ≤ convDensityAdd pX pY z :=
  integral_nonneg fun y => mul_nonneg (hpX_nn y) (hpY_nn _)

/-- Integrability of `convDensityAdd pX pY` when one factor is bounded. -/
theorem convDensityAdd_pXpY_integrable (pX pY : ℝ → ℝ)
    (hpX_int : Integrable pX volume) (hpX_meas : Measurable pX)
    (hpY_int : Integrable pY volume) (hpY_meas : Measurable pY) :
    Integrable (convDensityAdd pX pY) volume :=
  Common2026.Shannon.FisherInfoV2.convDensityAdd_envelope_integrable
    pX pY hpX_int hpX_meas hpY_int hpY_meas

/-- `∫ convDensityAdd pX pY = (∫ pX)·(∫ pY)`; with both normalized, `= 1`. -/
theorem convDensityAdd_pXpY_integral_eq (pX pY : ℝ → ℝ)
    (hpX_int : Integrable pX volume) (hpY_int : Integrable pY volume) :
    ∫ z, convDensityAdd pX pY z ∂volume = (∫ x, pX x ∂volume) * (∫ x, pY x ∂volume) := by
  rw [convDensityAdd_eq_convolution]
  exact MeasureTheory.integral_convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) hpX_int hpY_int

/-- **Variance-doubling**: `g_t ∗ g_t = g_{2t}` (`g_s = gaussianPDFReal 0 ⟨s, _⟩`).
@audit:ok — independent honesty audit (2026-06-01): genuine consequence of
`convDensityAdd_gaussian_closed_form` (`mX+mY = 0`, `vX+vY = ⟨2t,_⟩` via NNReal add),
no hypotheses beyond `0 < t`, sorryAx-free (transitive via bridge). -/
theorem convDensityAdd_gaussian_variance_double {t : ℝ} (ht : 0 < t) :
    convDensityAdd (gaussianPDFReal 0 ⟨t, ht.le⟩) (gaussianPDFReal 0 ⟨t, ht.le⟩)
      = gaussianPDFReal 0 ⟨2 * t, by positivity⟩ := by
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  have hvsum : (⟨t, ht.le⟩ : ℝ≥0) + ⟨t, ht.le⟩ = ⟨2 * t, by positivity⟩ := by
    ext
    show t + t = 2 * t
    ring
  rw [Common2026.Shannon.EPIBlachmanGaussianWitness.convDensityAdd_gaussian_closed_form hv_ne hv_ne,
    add_zero]
  congr 1

/-- **4-fold interchange bridge** (consumed by `int_fisherZ`):
`conv(conv(pX,g_t), conv(pY,g_t)) = conv(conv(pX,pY), g_{2t})`.
@audit:ok — independent honesty audit (2026-06-01): the equality follows genuinely from
the algebraic rearrangement assoc(×3) + comm(×1) + variance-doubling `g_t ∗ g_t = g_{2t}`
(`convDensityAdd_gaussian_variance_double`, traced step-by-step: (pX∗g)∗(pY∗g) → pX∗(g∗(pY∗g))
→ pX∗((pY∗g)∗g) → pX∗(pY∗(g∗g)) → (pX∗pY)∗(g∗g) → (pX∗pY)∗g_{2t}). All hypotheses regularity
(nonneg / Measurable / Integrable). `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-confirmed). -/
theorem convDensityAdd_convGaussian_interchange (pX pY : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY) (hpY_int : Integrable pY volume) :
    convDensityAdd
        (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
        (convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = convDensityAdd
          (convDensityAdd pX pY)
          (gaussianPDFReal 0 ⟨2 * t, by positivity⟩) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  -- regularity of the Gaussian heat kernel `g`
  have hg_nn : ∀ x, 0 ≤ g x := fun x => gaussianPDFReal_nonneg _ _ _
  have hg_meas : Measurable g := measurable_gaussianPDFReal _ _
  have hg_int : Integrable g volume := integrable_gaussianPDFReal _ _
  have hg_bdd : ∃ M, ∀ x, |g x| ≤ M :=
    Common2026.Shannon.EPIBlachmanGaussianWitness.bdd_gaussianPDFReal _ _
  -- regularity of `pY ∗ g`
  have hpYg_nn : ∀ x, 0 ≤ convDensityAdd pY g x :=
    fun x => convDensityAdd_pXpY_nonneg pY g hpY_nn hg_nn x
  have hpYg_meas : Measurable (convDensityAdd pY g) :=
    convDensityAdd_pXpY_measurable pY g hpY_meas hg_meas
  have hpYg_int : Integrable (convDensityAdd pY g) volume :=
    convDensityAdd_pXpY_integrable pY g hpY_int hpY_meas hg_int hg_meas
  have hpYg_bdd : ∃ M, ∀ x, |convDensityAdd pY g x| ≤ M :=
    convDensityAdd_bdd_of_integrable_bdd pY g hpY_nn hpY_int hg_bdd
  -- regularity of `g ∗ g`
  have hgg_nn : ∀ x, 0 ≤ convDensityAdd g g x :=
    fun x => convDensityAdd_pXpY_nonneg g g hg_nn hg_nn x
  have hgg_meas : Measurable (convDensityAdd g g) :=
    convDensityAdd_pXpY_measurable g g hg_meas hg_meas
  have hgg_int : Integrable (convDensityAdd g g) volume :=
    convDensityAdd_pXpY_integrable g g hg_int hg_meas hg_int hg_meas
  have hgg_bdd : ∃ M, ∀ x, |convDensityAdd g g x| ≤ M :=
    convDensityAdd_bdd_of_integrable_bdd g g hg_nn hg_int hg_bdd
  -- algebraic rearrangement: (pX∗g)∗(pY∗g) = (pX∗pY)∗(g∗g)
  -- step 1: (pX∗g)∗(pY∗g) = pX∗(g∗(pY∗g))   (assoc, c = pY∗g bounded)
  rw [convDensityAdd_assoc pX g (convDensityAdd pY g)
      hpX_nn hpX_int hpX_meas hg_nn hg_int hg_meas hpYg_nn hpYg_int hpYg_meas
      hpYg_bdd]
  -- step 2: g∗(pY∗g) = (pY∗g)∗g  (comm)
  rw [convDensityAdd_comm g (convDensityAdd pY g)]
  -- step 3: (pY∗g)∗g = pY∗(g∗g)  (assoc, c = g bounded)
  rw [convDensityAdd_assoc pY g g
      hpY_nn hpY_int hpY_meas hg_nn hg_int hg_meas hg_nn hg_int hg_meas
      hg_bdd]
  -- step 4: pX∗(pY∗(g∗g)) = (pX∗pY)∗(g∗g)  (assoc reverse, c = g∗g bounded)
  rw [← convDensityAdd_assoc pX pY (convDensityAdd g g)
      hpX_nn hpX_int hpX_meas hpY_nn hpY_int hpY_meas hgg_nn hgg_int hgg_meas
      hgg_bdd]
  -- step 5: g∗g = g_{2t}
  rw [show convDensityAdd g g = gaussianPDFReal 0 ⟨2 * t, by positivity⟩ from
    convDensityAdd_gaussian_variance_double ht]

end InformationTheory.Shannon.EPIConvDensity
