import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Meta.EntryPoint
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Extended entropy power

A two-layer redefinition of entropy power on `EReal` that removes the degeneracy of the
real-valued `entropyPower` (under which a singular measure satisfies `entropyPower = exp 0 = 1`).

* `differentialEntropyExt : Measure ℝ → EReal` returns `⊥` for a singular measure and, for
  `μ ≪ volume`, the genuine extended differential entropy as the `EReal` difference of the
  positive and negative parts. It evaluates to `⊤` for an infinite-entropy a.c. density
  (`h = +∞`), to `⊥` for a tall peaked density (`h = −∞`), and to the workhorse
  `differentialEntropy` value when finite.
* `entropyPowerExt : Measure ℝ → ℝ≥0∞` is the non-branching `EReal.exp (2 * differentialEntropyExt μ)`,
  with `EReal.exp` absorbing `exp ⊥ = 0`, `exp ⊤ = ∞`, and `exp ↑x = ofReal (exp x)` in one function.

## Main definitions

* `differentialEntropyExt` — the extended differential entropy valued in `EReal`.
* `entropyPowerExt` — the extended entropy power valued in `ℝ≥0∞`.

## Implementation notes

The a.c. branch must distinguish signs: coercing `differentialEntropy μ` directly is false as
stated for infinite-entropy inputs, because the Bochner integral returns `0` when the integrand is
non-integrable, collapsing `h = ±∞` to `entropyPowerExt = 1`. Taking the `EReal` difference of the
positive part `∫⁻ ofReal(negMulLog f)` and the negative part `∫⁻ ofReal(-(negMulLog f))` produces
`+∞` / `−∞` / a finite value correctly. Following `klDiv`, the a.c. test is made definitional via
`open Classical in` together with `irreducible_def`.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

open Classical in
/-- The extended differential entropy: `⊥` for a singular measure and, for `μ ≪ volume`, the
`EReal` difference `A − B` of the positive part `A := ∫⁻ ofReal(negMulLog f)` and the negative part
`B := ∫⁻ ofReal(-(negMulLog f))` of `negMulLog ∘ f`, where `f` is the density. When both `A` and `B`
are finite this equals the workhorse `differentialEntropy μ`; `A = ⊤` (heavy tail) gives `⊤`,
`B = ⊤` (tall peak) gives `⊥`, and `A = B = ⊤` gives `⊥` (the EPI-safe side of `⊤ − ⊤`).

@audit:ok -/
noncomputable irreducible_def differentialEntropyExt (μ : Measure ℝ) : EReal :=
  if μ ≪ volume then
    (((∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume : ℝ≥0∞) : EReal)
      - ((∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal)))
          ∂volume : ℝ≥0∞) : EReal))
  else ⊥

/-- The extended entropy power valued in `ℝ≥0∞`: `0` for a singular measure or `h = −∞`, `∞` for
`h = +∞`, and `ofReal (exp (2h))` for a finite a.c. entropy, via the non-branching
`EReal.exp (2 * differentialEntropyExt μ)`. -/
noncomputable def entropyPowerExt (μ : Measure ℝ) : ℝ≥0∞ :=
  EReal.exp (2 * differentialEntropyExt μ)

/-- The a.c.-branch value of `differentialEntropyExt` as the `EReal` difference of positive and
negative parts.
@audit:ok -/
theorem differentialEntropyExt_of_ac {μ : Measure ℝ} (h : μ ≪ volume) :
    differentialEntropyExt μ
      = (((∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume : ℝ≥0∞)
            : EReal)
        - ((∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal)))
            ∂volume : ℝ≥0∞) : EReal)) := by
  rw [differentialEntropyExt]; exact if_pos h

/-- When `μ ≪ volume` and `negMulLog ∘ density` is integrable (finite differential entropy),
`differentialEntropyExt` equals the workhorse `differentialEntropy`.
@audit:ok -/
theorem differentialEntropyExt_of_ac_integrable {μ : Measure ℝ} (hac : μ ≪ volume)
    (hint : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropyExt μ = (differentialEntropy μ : EReal) := by
  rw [differentialEntropyExt_of_ac hac]
  set g : ℝ → ℝ := fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal) with hg
  have hbound : ∀ (f : ℝ → ℝ), Integrable f volume →
      (∫⁻ x, ENNReal.ofReal (f x) ∂volume) ≠ ⊤ := by
    intro f hf
    refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hAfin : (∫⁻ x, ENNReal.ofReal (g x) ∂volume) ≠ ⊤ := hbound g hint
  have hBfin : (∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume) ≠ ⊤ := hbound _ hint.neg
  have hwork : differentialEntropy μ
      = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (g x) ∂volume)
        - ENNReal.toReal (∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume) := by
    rw [differentialEntropy]
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  rw [hwork, EReal.coe_sub, EReal.coe_ennreal_toReal hAfin, EReal.coe_ennreal_toReal hBfin]

/-- The singular-branch value of `differentialEntropyExt` is `⊥`.
@audit:ok -/
theorem differentialEntropyExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) :
    differentialEntropyExt μ = ⊥ := by
  rw [differentialEntropyExt]
  exact if_neg h

/-- The finite a.c.-branch value of `entropyPowerExt` is `ENNReal.ofReal (exp (2h))`.
@audit:ok -/
theorem entropyPowerExt_of_ac_integrable {μ : Measure ℝ} (hac : μ ≪ volume)
    (hint : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ)) := by
  unfold entropyPowerExt
  rw [differentialEntropyExt_of_ac_integrable hac hint,
    show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast, ← EReal.coe_mul,
    EReal.exp_coe]

/-- If `differentialEntropyExt μ = ⊤` (i.e. `h = +∞`) then `entropyPowerExt μ = ⊤`.
@audit:ok -/
theorem entropyPowerExt_eq_top_of_diffEntExt_top {μ : Measure ℝ}
    (h : differentialEntropyExt μ = ⊤) : entropyPowerExt μ = ⊤ := by
  unfold entropyPowerExt
  rw [h, EReal.mul_top_of_pos (by norm_num), EReal.exp_top]

/-- The singular-branch (and `h = −∞`) value of `entropyPowerExt` is `0`.
@audit:ok -/
theorem entropyPowerExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) :
    entropyPowerExt μ = 0 := by
  unfold entropyPowerExt
  rw [differentialEntropyExt_singular h, EReal.mul_bot_of_pos (by norm_num), EReal.exp_bot]

/-- The entropy power of a Dirac measure is `0` (where the real-valued `entropyPower` degenerates
to `1`).
@audit:ok -/
@[entry_point]
theorem entropyPowerExt_dirac (m : ℝ) : entropyPowerExt (Measure.dirac m) = 0 := by
  apply entropyPowerExt_singular
  intro h_ac
  have h_sing : Measure.dirac m ⟂ₘ (volume : Measure ℝ) := mutuallySingular_dirac m volume
  have h_zero : (Measure.dirac m : Measure ℝ) = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h_ac h_sing
  exact (NeZero.ne' (Measure.dirac m)).symm h_zero

/-- `negMulLog` of a Gaussian density is volume-integrable (finite differential entropy), via the
a.e. identity `negMulLog(gaussianPDF) = gaussianPDF · c₁ + gaussianPDF · (x-m)²/(2v)` with the
density integrable and the second moment finite.
@audit:ok -/
theorem integrable_negMulLog_gaussianReal_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => Real.negMulLog ((gaussianReal m v).rnDeriv volume x).toReal) volume := by
  -- pointwise: negMulLog(pdf) = pdf · (c₁ + (x-m)²/(2v))  (a.e. via density identification)
  have h_ae : (fun x => Real.negMulLog ((gaussianReal m v).rnDeriv volume x).toReal)
      =ᵐ[volume] (fun x => gaussianPDFReal m v x * ((1/2) * Real.log (2 * Real.pi * v))
        + gaussianPDFReal m v x * ((x - m)^2 / (2 * v))) := by
    filter_upwards [rnDeriv_gaussianReal m v] with x hx
    rw [hx, toReal_gaussianPDF]
    unfold Real.negMulLog
    rw [log_gaussianPDFReal_eq m hv x]
    ring
  rw [integrable_congr h_ae]
  -- term 1: pdf · const
  have h_pdf : Integrable (gaussianPDFReal m v) volume := integrable_gaussianPDFReal m v
  have h_t1 : Integrable
      (fun x => gaussianPDFReal m v x * ((1/2) * Real.log (2 * Real.pi * v))) volume :=
    h_pdf.mul_const _
  -- term 2: pdf · (x-m)²/(2v).  `pdf · (x-m)²` integrable against volume = `(x-m)²` integrable
  -- against `gaussianReal = volume.withDensity (ofReal ∘ pdf)`.
  have h2mom : Integrable (fun x => (x - m)^2) (gaussianReal m v) := by
    have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal m v) :=
      (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable_sq
    have h_id : Integrable (fun y : ℝ => y) (gaussianReal m v) := by
      simpa using (memLp_id_gaussianReal (μ := m) (v := v) 1).integrable (by norm_num)
    have h_eq : (fun y : ℝ => (y - m) ^ 2) = fun y => y ^ 2 - 2 * m * y + m ^ 2 := by
      funext y; ring
    rw [h_eq]
    exact ((h_sq.sub (h_id.const_mul (2 * m))).add (integrable_const (m ^ 2)))
  have hgvol : gaussianReal m v
      = volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal m v x)) :=
    gaussianReal_of_var_ne_zero m hv
  rw [hgvol, integrable_withDensity_iff (by measurability)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)] at h2mom
  have h_t2 : Integrable (fun x => gaussianPDFReal m v x * ((x - m)^2 / (2 * v))) volume := by
    have hc := (h2mom.const_mul (1 / (2 * (v : ℝ))))
    refine hc.congr (Filter.Eventually.of_forall fun x => ?_)
    show 1 / (2 * (v : ℝ)) * ((x - m) ^ 2 * (ENNReal.ofReal (gaussianPDFReal m v x)).toReal)
        = gaussianPDFReal m v x * ((x - m) ^ 2 / (2 * v))
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m v x)]
    ring
  exact h_t1.add h_t2

/-- The entropy power of a Gaussian (`v ≠ 0`, a.c.) is `2πe·v`, hence does not collapse to `0`.
@audit:ok -/
@[entry_point]
theorem entropyPowerExt_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPowerExt (gaussianReal m v)
      = ENNReal.ofReal (2 * Real.pi * Real.exp 1 * (v : ℝ)) := by
  have h_ac : gaussianReal m v ≪ volume := gaussianReal_absolutelyContinuous m hv
  rw [entropyPowerExt_of_ac_integrable h_ac (integrable_negMulLog_gaussianReal_density m hv)]
  congr 1
  rw [differentialEntropy_gaussianReal m hv]
  rw [show (2 : ℝ) * ((1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)))
        = Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) by ring]
  rw [Real.exp_log]
  positivity

end InformationTheory.Shannon
