import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.EPIBridge
import InformationTheory.Shannon.FisherInfo.V2DeBruijnGenuine
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.G2.HeatFlowContinuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Stam → EPI: Csiszár ratio path-derivative cluster

This file holds the Csiszár-coupling ratio path-derivative lemmas — the `AntitoneOn` and continuity
chain along the heat-flow path — consumed by the entropy power inequality case-1 closure.

## Main statements

* `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` — entropy-power chain-rule helper.
* `csiszarLogRatioGap_hasDerivAt` — the log-ratio gap path-derivative.
* `csiszarLogRatioGap_deriv_le_zero` — the derivative is `≤ 0` from the 1-source Stam inequality.
* `epi_of_csiszarLogRatioGap_zero_nonneg` — recovery of the entropy power inequality from
  nonnegativity of the gap at `t = 0`.
* `csiszarLogRatioGap_antitoneOn_Ici_zero` — antitonicity of the gap on the heat-flow ray.
-/

namespace InformationTheory.Shannon.EPIStamToBridge

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.StamEPIBridge
open InformationTheory.Shannon.EPIL3Integration

/-! ## §2'' — Path-derivative of the 1-source gap -/

/-- Entropy-power chain-rule helper: if `f` has derivative `d` at `t`, then the entropy-power
composition `s ↦ Real.exp (2 · f s)` has derivative `Real.exp (2 · f t) · (2 · d)` at `t`. Used to
lift the V2 de Bruijn identity to entropy-power form.
@audit:ok -/
@[entry_point]
theorem entropyPower_hasDerivAt_of_diffEnt_hasDerivAt
    {f : ℝ → ℝ} {d t : ℝ} (h : HasDerivAt f d t) :
    HasDerivAt (fun s => Real.exp (2 * f s)) (Real.exp (2 * f t) * (2 * d)) t :=
  (h.const_mul 2).exp

/-! ## §2''' — 1-source Stam reduction `g'(t) ≤ 0` -/

/-- Ratio-gap derivative core (pure arithmetic): from the harmonic Stam inequality
`1 / J_sum ≥ 1 / J_X + 1 / J_Y` and positivity of the entropy powers `N_X, N_Y`, the log-ratio gap
derivative `J_sum − (N_X · J_X + N_Y · J_Y) / (N_X + N_Y)` is `≤ 0`, equivalently
`J_sum · (N_X + N_Y) ≤ N_X · J_X + N_Y · J_Y`.

This is the factor-1 inequality (coefficient `1` on `J_sum`), a true real-arithmetic inequality
over the free variables. The analogous factor-2 statement is false from harmonic Stam and
positivity alone; the factor mismatch for the genuine `𝒩(0, 2)` sum coupling lives in the de Bruijn
lift, not in this lemma.
@audit:ok -/
theorem csiszar_ratio_deriv_le_zero_arith
    (J_X J_Y J_sum N_X N_Y : ℝ)
    (hJX : 0 < J_X) (hJY : 0 < J_Y) (hJsum : 0 < J_sum)
    (hNX : 0 < N_X) (hNY : 0 < N_Y)
    (h_stam : 1 / J_sum ≥ 1 / J_X + 1 / J_Y) :
    J_sum - (N_X * J_X + N_Y * J_Y) / (N_X + N_Y) ≤ 0 := by
  have hNsum : 0 < N_X + N_Y := add_pos hNX hNY
  -- Clear the harmonic Stam inequality to a polynomial form:
  -- `1/J_sum ≥ 1/J_X + 1/J_Y` ⟺ `J_X*J_Y ≥ J_sum*(J_X+J_Y)`.
  have h_stam_poly : J_sum * (J_X + J_Y) ≤ J_X * J_Y := by
    have h := h_stam
    rw [ge_iff_le, div_add_div _ _ (ne_of_gt hJX) (ne_of_gt hJY)] at h
    rw [div_le_div_iff₀ (by positivity) hJsum] at h
    nlinarith [h]
  -- Goal ⟺ `J_sum*(N_X+N_Y) ≤ N_X*J_X + N_Y*J_Y`.
  rw [sub_nonpos, le_div_iff₀ hNsum]
  -- After clearing `(J_X+J_Y)`: `J_X*J_Y*(N_X+N_Y) ≤ (N_X*J_X+N_Y*J_Y)*(J_X+J_Y)`,
  -- whose difference is `N_X*J_X² + N_Y*J_Y² ≥ 0`.
  nlinarith [mul_nonneg (le_of_lt hNX) (sq_nonneg (J_X - J_Y)),
    mul_nonneg (le_of_lt hNY) (sq_nonneg (J_X - J_Y)),
    mul_pos hJX hJY, mul_pos hNX hJX, mul_pos hNY hJY,
    mul_nonneg (le_of_lt hNsum) (le_of_lt (mul_pos hJX hJY)),
    h_stam_poly, mul_le_mul_of_nonneg_right h_stam_poly (le_of_lt hNsum)]

/-- The log-ratio gap derivative: `csiszarLogRatioGap X Y Z_X Z_Y P` has derivative
`J_sum − (N_X · J_X + N_Y · J_Y) / (N_X + N_Y)` at any `t > 0`, where
`N_i = entropyPower (P.map path_i t)` and `J_i = fisherInfoOfDensityReal ((h_reg_i.reg_at t ht).density_t)`.
Built from the three per-term entropy-power derivatives (via the de Bruijn V2 identity and the
chain-rule helper), `HasDerivAt.log` for the two log terms, composed by `HasDerivAt.sub`. The
`h_reg_*` are regularity preconditions.

The conclusion is the factor-1 derivative, correct under the stated hypotheses: `h_reg_sum`'s
`Z_law` field asserts `P.map (Z_X + Z_Y) = gaussianReal 0 1`. For the genuine sum coupling with
independent unit-variance noises the sum law is `gaussianReal 0 2`, so `h_reg_sum` is then
uninhabitable; honest closure of the sum line uses the two-time route, where `X` and `Y` are
perturbed with separate unit-variance noises and the variance-2 view never arises.
@audit:ok -/
theorem csiszarLogRatioGap_hasDerivAt
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_sum : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp Y Z_Y P)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P s)
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at t ht).density_t)
        - (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_X.reg_at t ht).density_t)
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_Y.reg_at t ht).density_t))
          / (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))) t := by
  -- Per-term de Bruijn V2 derivatives (same building blocks as the
  -- difference-version path-derivative that was deleted with the dead subgraph).
  have h_dB_X :
      HasDerivAt
        (fun s : ℝ => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z_X s)))
        ((1/2) * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_X.reg_at t ht).density_t)) t :=
    InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2 X Z_X hX hZX hXZX ht
      (h_reg_X.reg_at t ht)
  have h_dB_Y :
      HasDerivAt
        (fun s : ℝ => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Y Z_Y s)))
        ((1/2) * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_Y.reg_at t ht).density_t)) t :=
    InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2 Y Z_Y hY hZY hYZY ht
      (h_reg_Y.reg_at t ht)
  have h_dB_sum :
      HasDerivAt
        (fun s : ℝ => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) s)))
        ((1/2) * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at t ht).density_t)) t :=
    InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2
      (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω)
      (hX.add hY) (hZX.add hZY) hXYZXY ht (h_reg_sum.reg_at t ht)
  -- Lift to entropy-power form via the A-2-2 chain rule.
  have h_eP_X := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB_X
  have h_eP_Y := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB_Y
  have h_eP_sum := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB_sum
  -- Abbreviations.
  set J_X := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_X.reg_at t ht).density_t) with hJX_def
  set J_Y := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_Y.reg_at t ht).density_t) with hJY_def
  set J_sum := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_sum.reg_at t ht).density_t) with hJsum_def
  -- Normalize each per-term derivative to `entropyPower (P.map path_i) · J_i`.
  -- `entropyPower μ = exp (2 * differentialEntropy μ)` is rfl, and
  -- `gaussianConvolution X Z s = fun ω => X ω + √s · Z ω` is rfl, so the function
  -- bodies already match `entropyPower (P.map (fun ω => ...))`. The derivative
  -- value `exp(2h) * (2 * ((1/2) * J))` simplifies to `entropyPower · J`.
  have hN_X :
      HasDerivAt (fun s : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt s * Z_X ω)))
        (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X) t := by
    have h_val :
        entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X
          = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
              (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z_X t)))
            * (2 * ((1/2) * J_X)) := by
      unfold entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]
    exact h_eP_X
  have hN_Y :
      HasDerivAt (fun s : ℝ => entropyPower (P.map (fun ω => Y ω + Real.sqrt s * Z_Y ω)))
        (entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y) t := by
    have h_val :
        entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y
          = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
              (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Y Z_Y t)))
            * (2 * ((1/2) * J_Y)) := by
      unfold entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]
    exact h_eP_Y
  have hN_sum :
      HasDerivAt (fun s : ℝ => entropyPower
          (P.map (fun ω => X ω + Y ω + Real.sqrt s * (Z_X ω + Z_Y ω))))
        (entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) * J_sum) t := by
    have h_val :
        entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) * J_sum
          = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
              (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
                        (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) t)))
            * (2 * ((1/2) * J_sum)) := by
      unfold entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]
    exact h_eP_sum
  -- Positivity of the entropy powers (for the `log` side conditions).
  have hNX_pos : 0 < entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) :=
    entropyPower_pos _
  have hNY_pos : 0 < entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) :=
    entropyPower_pos _
  have hNsum_pos : 0 < entropyPower
      (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) := entropyPower_pos _
  -- `log N_sum` derivative: `(N_sum · J_sum) / N_sum = J_sum`.
  have h_log_sum :
      HasDerivAt (fun s : ℝ => Real.log (entropyPower
          (P.map (fun ω => X ω + Y ω + Real.sqrt s * (Z_X ω + Z_Y ω)))))
        J_sum t := by
    have h := hN_sum.log (ne_of_gt hNsum_pos)
    rwa [mul_comm, mul_div_assoc, div_self (ne_of_gt hNsum_pos), mul_one] at h
  -- `log (N_X + N_Y)` derivative: `(N_X·J_X + N_Y·J_Y)/(N_X+N_Y)`.
  have h_add :
      HasDerivAt (fun s : ℝ =>
          entropyPower (P.map (fun ω => X ω + Real.sqrt s * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt s * Z_Y ω)))
        (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X
          + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y) t :=
    hN_X.add hN_Y
  have h_log_add :
      HasDerivAt (fun s : ℝ => Real.log
          (entropyPower (P.map (fun ω => X ω + Real.sqrt s * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt s * Z_Y ω))))
        ((entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y)
          / (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))) t :=
    h_add.log (ne_of_gt (add_pos hNX_pos hNY_pos))
  -- Combine via `.sub` and match the `csiszarLogRatioGap` body.
  have h_combined := h_log_sum.sub h_log_add
  unfold InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
  exact h_combined

/-- The log-ratio gap derivative is `≤ 0` from the 1-source Stam inequality: the value
`J_sum − (N_X · J_X + N_Y · J_Y) / (N_X + N_Y) ≤ 0` follows from the harmonic Stam inequality
`1 / J_sum ≥ 1 / J_X + 1 / J_Y` (extracted from `h_stam`) plus positivity, via the arithmetic core
`csiszar_ratio_deriv_le_zero_arith`. Unlike the difference-gap form, the ratio form is closable from
harmonic Stam (weights `α = N_X / (N_X + N_Y)`, `β = N_Y / (N_X + N_Y)`, with `α² ≤ α`).

The harmonic Stam inequality is extracted by applying the producer `h_stam` at the three path
densities, using the Fisher identifications `J_i = (fisherInfoOfMeasureV2 (P.map _) f_i).toReal`
(`rfl`, since `fisherInfoOfMeasureV2` ignores its measure argument) together with the
caller-supplied regularity preconditions (`IsRegularDensityV2`, the normalizations, the pointwise
convolution identification, and the `IsBlachmanConvReady` bundle). The inequality core lives in the
producer; none of the preconditions bundle it.
@audit:ok -/
@[entry_point]
theorem csiszarLogRatioGap_deriv_le_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg_sum : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp Y Z_Y P)
    {t : ℝ} (ht : 0 < t)
    (hJX_pos : 0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                      ((h_reg_X.reg_at t ht).density_t))
    (hJY_pos : 0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                      ((h_reg_Y.reg_at t ht).density_t))
    (hJsum_pos : 0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                        ((h_reg_sum.reg_at t ht).density_t))
    (h_stam : InformationTheory.Shannon.StamEPIBridge.IsStamInequalityHyp
                (fun ω => X ω + Real.sqrt t * Z_X ω)
                (fun ω => Y ω + Real.sqrt t * Z_Y ω) P)
    -- caller-supplied regularity preconditions for applying `h_stam`.
    (h_regdens_X : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
                      ((h_reg_X.reg_at t ht).density_t))
    (h_regdens_Y : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
                      ((h_reg_Y.reg_at t ht).density_t))
    (h_norm_X : ∫ x, (h_reg_X.reg_at t ht).density_t x ∂MeasureTheory.volume = 1)
    (h_norm_Y : ∫ x, (h_reg_Y.reg_at t ht).density_t x ∂MeasureTheory.volume = 1)
    (h_conv_id : ∀ x, (h_reg_sum.reg_at t ht).density_t x
                    = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                        ((h_reg_X.reg_at t ht).density_t)
                        ((h_reg_Y.reg_at t ht).density_t) x)
    (h_blachman : InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
                    ((h_reg_X.reg_at t ht).density_t)
                    ((h_reg_Y.reg_at t ht).density_t)) :
    InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at t ht).density_t)
        - (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_X.reg_at t ht).density_t)
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_Y.reg_at t ht).density_t))
          / (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))
      ≤ 0 := by
  -- Abbreviations for the three Fisher infos and two entropy powers.
  set J_X := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_X.reg_at t ht).density_t) with hJX_def
  set J_Y := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_Y.reg_at t ht).density_t) with hJY_def
  set J_sum := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_sum.reg_at t ht).density_t) with hJsum_def
  set N_X := entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) with hNX_def
  set N_Y := entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) with hNY_def
  -- Positivity of the entropy powers.
  have hNX_pos : 0 < N_X := entropyPower_pos _
  have hNY_pos : 0 < N_Y := entropyPower_pos _
  -- Harmonic Stam `1/J_sum ≥ 1/J_X + 1/J_Y` extracted from
  -- `h_stam`. We apply the ∀-quantified producer `Prop` at the three
  -- path densities `f_i = (h_reg_*.reg_at t ht).density_t`. The Fisher
  -- identifications `J_i = (fisherInfoOfMeasureV2 (P.map _) f_i).toReal` are `rfl`
  -- (`fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f`,
  -- `fisherInfoOfDensityReal f = (fisherInfoOfDensity f).toReal`); the remaining
  -- regularity inputs are the caller-supplied preconditions.
  have h_plain_stam : 1 / J_sum ≥ 1 / J_X + 1 / J_Y := by
    refine h_stam J_X J_Y J_sum
      ((h_reg_X.reg_at t ht).density_t)
      ((h_reg_Y.reg_at t ht).density_t)
      ((h_reg_sum.reg_at t ht).density_t)
      hJX_pos hJY_pos hJsum_pos ?_ ?_ ?_ h_regdens_X h_regdens_Y
      h_norm_X h_norm_Y h_conv_id h_blachman
    · -- `J_X = (fisherInfoOfMeasureV2 (P.map (X+√t·Z_X)) fX).toReal`
      rw [hJX_def]
      rfl
    · -- `J_Y = (fisherInfoOfMeasureV2 (P.map (Y+√t·Z_Y)) fY).toReal`
      rw [hJY_def]
      rfl
    · -- `J_sum = (fisherInfoOfMeasureV2 (P.map ((X+√t·Z_X)+(Y+√t·Z_Y))) fXY).toReal`
      rw [hJsum_def]
      rfl
  -- The genuine arithmetic core closes the goal from plain Stam + positivity.
  exact csiszar_ratio_deriv_le_zero_arith J_X J_Y J_sum N_X N_Y
    hJX_pos hJY_pos hJsum_pos hNX_pos hNY_pos h_plain_stam

/-- Entropy power inequality recovery from nonnegativity of the gap at `t = 0`. The log-ratio gap
at `t = 0` is `log (eP(X + Y)) − log (eP X + eP Y)`; since both arguments are strictly positive,
`0 ≤ r(0)` is equivalent to `eP X + eP Y ≤ eP(X + Y)` by `Real.log_le_log_iff`. -/
theorem epi_of_csiszarLogRatioGap_zero_nonneg
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    (h_nonneg : 0 ≤ InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P 0) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  rw [InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap_at_zero] at h_nonneg
  -- `0 ≤ log A − log B` ⟺ `log B ≤ log A`.
  have h_log_le : Real.log (entropyPower (P.map X) + entropyPower (P.map Y))
      ≤ Real.log (entropyPower (P.map (fun ω => X ω + Y ω))) := by linarith
  -- Positivity of both `log` arguments.
  have hA_pos : 0 < entropyPower (P.map (fun ω => X ω + Y ω)) := entropyPower_pos _
  have hB_pos : 0 < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  -- `log B ≤ log A ⟺ B ≤ A` (both positive).
  rw [Real.log_le_log_iff hB_pos hA_pos] at h_log_le
  exact h_log_le

/-- `csiszarLogRatioGap X Y Z_X Z_Y P` is differentiable on the interior
`Set.Ioi 0 = interior (Set.Ici 0)`, via `csiszarLogRatioGap_hasDerivAt` and
`HasDerivAt.differentiableAt`.
@audit:ok -/
theorem csiszarLogRatioGap_differentiableOn_interior
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_sum : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp Y Z_Y P) :
    DifferentiableOn ℝ
      (fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P t)
      (interior (Set.Ici (0 : ℝ))) := by
  rw [interior_Ici]
  intro t ht
  have ht_pos : (0 : ℝ) < t := ht
  exact ((csiszarLogRatioGap_hasDerivAt X Y Z_X Z_Y P
    hX hZX hXZX hY hZY hYZY hXYZXY
    h_reg_sum h_reg_X h_reg_Y ht_pos).differentiableAt).differentiableWithinAt

/-- Endpoint continuity `ContinuousWithinAt (Set.Ioi 0) 0` of `csiszarLogRatioGap X Y Z_X Z_Y P`,
by composing the endpoint continuity of the three heat-flow entropy powers
(`heatFlowEntropyPower_continuousWithinAt_zero`) through `ContinuousWithinAt.log` / `.add` / `.sub`
(with `entropyPower_pos` / `add_pos` discharging the `≠ 0` premises). The interior `t > 0`
continuity is supplied separately by `csiszarLogRatioGap_differentiableOn_interior`. -/
theorem csiszarLogRatioGap_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P) :
    ContinuousWithinAt
      (fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P t)
      (Set.Ioi (0 : ℝ)) 0 := by
  have h_sum := heatFlowEntropyPower_continuousWithinAt_zero
    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P h_endpt_sum
  have h_X := heatFlowEntropyPower_continuousWithinAt_zero X Z_X P h_endpt_X
  have h_Y := heatFlowEntropyPower_continuousWithinAt_zero Y Z_Y P h_endpt_Y
  unfold InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
  exact (h_sum.log (entropyPower_pos _).ne').sub
    ((h_X.add h_Y).log (add_pos (entropyPower_pos _) (entropyPower_pos _)).ne')

/-- The log-ratio gap `csiszarLogRatioGap X Y Z_X Z_Y P` is antitone on the heat-flow ray
`Set.Ici 0`. Applies `antitoneOn_of_deriv_nonpos` on the convex domain, with interior
differentiability (`csiszarLogRatioGap_differentiableOn_interior`), endpoint continuity
(`csiszarLogRatioGap_continuousWithinAt_zero`), and the per-`t` `deriv ≤ 0` from
`csiszarLogRatioGap_hasDerivAt` and `csiszarLogRatioGap_deriv_le_zero`. -/
theorem csiszarLogRatioGap_antitoneOn_Ici_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_sum : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P)
    (h_pos_stam : ∀ (t : ℝ) (ht : 0 < t),
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_X.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_Y.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_sum.reg_at t ht).density_t)) ∧
      InformationTheory.Shannon.StamEPIBridge.IsStamInequalityHyp
        (fun ω => X ω + Real.sqrt t * Z_X ω)
        (fun ω => Y ω + Real.sqrt t * Z_Y ω) P ∧
      -- per-`t` caller-supplied regularity preconditions threaded to the derivative-bound lemma.
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_X.reg_at t ht).density_t) ∧
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_Y.reg_at t ht).density_t) ∧
      (∫ x, (h_reg_X.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∫ x, (h_reg_Y.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∀ x, (h_reg_sum.reg_at t ht).density_t x
            = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                ((h_reg_X.reg_at t ht).density_t)
                ((h_reg_Y.reg_at t ht).density_t) x) ∧
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X.reg_at t ht).density_t)
        ((h_reg_Y.reg_at t ht).density_t)) :
    AntitoneOn
      (fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P t)
      (Set.Ici (0 : ℝ)) := by
  -- Derive `AntitoneOn` on the interior `Set.Ioi 0` (continuity there is
  -- `differentiableOn.continuousOn`), then re-attach the endpoint `0` via
  -- `csiszarLogRatioGap_continuousWithinAt_zero` + `AntitoneOn.insert_of_continuousWithinAt`.
  set f := fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
    X Y Z_X Z_Y P t with hf_def
  -- Genuine interior differentiability (= continuity) on `Set.Ioi 0`.
  have h_diff_Ioi : DifferentiableOn ℝ f (Set.Ioi 0) := by
    have := csiszarLogRatioGap_differentiableOn_interior X Y Z_X Z_Y P
      hX hZX hXZX hY hZY hYZY hXYZXY h_reg_sum h_reg_X h_reg_Y
    rwa [interior_Ici] at this
  -- `AntitoneOn f (Set.Ioi 0)`, genuine (no wall): continuity on `Ioi 0` is the
  -- interior differentiability, `interior (Ioi 0) = Ioi 0`, deriv ≤ 0 from R-2 + R-3.
  have h_anti_Ioi : AntitoneOn f (Set.Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) h_diff_Ioi.continuousOn
      (by rw [interior_Ioi]; exact h_diff_Ioi) ?_
    intro t ht
    rw [interior_Ioi] at ht
    have ht_pos : (0 : ℝ) < t := ht
    obtain ⟨hJX_pos, hJY_pos, hJsum_pos, h_stam, h_regdens_X, h_regdens_Y,
            h_norm_X, h_norm_Y, h_conv_id, h_blachman⟩ := h_pos_stam t ht_pos
    have h_deriv := csiszarLogRatioGap_hasDerivAt X Y Z_X Z_Y P
      hX hZX hXZX hY hZY hYZY hXYZXY
      h_reg_sum h_reg_X h_reg_Y ht_pos
    have h_le := csiszarLogRatioGap_deriv_le_zero X Y Z_X Z_Y P
      h_reg_sum h_reg_X h_reg_Y ht_pos hJX_pos hJY_pos hJsum_pos h_stam
      h_regdens_X h_regdens_Y h_norm_X h_norm_Y h_conv_id h_blachman
    rw [h_deriv.deriv]
    exact h_le
  -- Endpoint `0` is a (left) cluster point of `Set.Ioi 0`.
  have h_cluster : ClusterPt (0 : ℝ) (Filter.principal (Set.Ioi 0)) := by
    rw [← mem_closure_iff_clusterPt, closure_Ioi]
    exact Set.self_mem_Ici
  -- Endpoint continuity from the shrunk wall atom (R-5-b').
  have h_cont_zero : ContinuousWithinAt f (Set.Ioi 0) 0 :=
    csiszarLogRatioGap_continuousWithinAt_zero X Y Z_X Z_Y P
      h_endpt_sum h_endpt_X h_endpt_Y
  -- Insert the endpoint: `insert 0 (Ioi 0) = Ici 0`.
  have := h_anti_Ioi.insert_of_continuousWithinAt h_cluster h_cont_zero
  rwa [Set.Ioi_insert] at this

/-! ## §5 — Predicate manipulation: symmetry, congruence, pass-through -/

/-! ## §6 — Chain forms (3-arg / 4-arg) via scaling decomposition -/

/-! ## §7 — Round-trip / sanity-check theorems -/

end InformationTheory.Shannon.EPIStamToBridge