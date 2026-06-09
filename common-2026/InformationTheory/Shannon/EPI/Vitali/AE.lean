import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.Conv.DensityAssoc
import InformationTheory.Shannon.EPI.ApproxIdentityL1

/-!
# G2 Vitali witness — a.e. pointwise convergence of the entropy integrands (subsequence)

This file supplies the **genuine** a.e.-convergence building block consumed by the
layer-2 machinery `differentialEntropy_convDensity_integral_tendsto` in
`EPIG2HeatFlowContinuity.lean`. Along any sequence `u → 0⁺`, the entropy
integrands `negMulLog (convDensityAdd pX g_{u n})` converge to `negMulLog pX`
**a.e. along a subsequence** `n ↦ u (ns n)` (`StrictMono ns`).

## Why a subsequence (and why that is enough)

The genuine scaffolding is the **layer-1 L¹ convergence**
`convDensityAdd_tendsto_L1_zero` (`EPIApproxIdentityL1.lean`, `@audit:ok`,
sorryAx-free). Composing it with `hu_lim` and feeding it through
`tendstoInMeasure_of_tendsto_eLpNorm` (Lp → measure) and
`TendstoInMeasure.exists_seq_tendsto_ae` (measure → a.e.) yields a.e. convergence
of `convDensityAdd pX g_{u n} → pX` **along a subsequence** `f (ns i)`
(`StrictMono ns`), composed through the continuous map `Real.negMulLog`.

Mathlib has no *full-sequence* a.e. lemma from L¹/measure convergence for the
Gaussian kernel (every route — `TendstoInMeasure.exists_seq_tendsto_ae` /
`exists_seq_tendsto_ae'` — is subsequence-only; the only full-sequence a.e.
mollifier lemma `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`
is compact-support-bump-limited, and `gaussianPDFReal` is not a `ContDiffBump`).
Rather than carry a parked *full-sequence* witness, the layer-2 consumer is shaped
to use this **subsequence** statement directly via `tendsto_of_subseq_tendsto`
(the same device Mathlib's own `tendsto_Lp_of_tendstoInMeasure` uses): the entropy
integral limit is proved by showing every subsequence has a further a.e.-convergent
sub-subsequence, which this lemma supplies. No full-sequence a.e. fact is needed,
so there is no residual here — the file is fully genuine.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-- **Genuine subsequence a.e. convergence** (the layer-2 Vitali a.e. building
block).

Along any sequence `u → 0⁺`, the entropy integrands
`negMulLog (convDensityAdd pX g_{u n})` converge to `negMulLog (pX)`
**a.e. along a subsequence** `n ↦ u (ns n)` (`StrictMono ns`).

Genuine route: layer-1 L¹ convergence `convDensityAdd_tendsto_L1_zero`
(`@audit:ok`, sorryAx-free) reparameterised to the sequence `u` via `hu_lim`,
then `tendstoInMeasure_of_tendsto_eLpNorm` (Lp → measure) and
`TendstoInMeasure.exists_seq_tendsto_ae` (measure → a.e. subsequence), and finally
the continuous map `Real.negMulLog` composed pointwise. No own `sorry`.
@audit:ok -/
theorem negMulLog_convDensity_tendsto_ae_subseq
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂volume,
      Tendsto (fun i =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u (ns i), (hu_pos (ns i)).le⟩) x))
        atTop (𝓝 (Real.negMulLog (pX x))) := by
  classical
  -- The smoothed densities, indexed by the sequence `u`.
  set f : ℕ → ℝ → ℝ :=
    fun n => convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) with hf_def
  -- Layer-1 L¹ convergence, reparameterised from the continuous filter to the
  -- sequence `u` and rewritten from `(u n).toNNReal` to `⟨u n, _⟩`.
  have hL1 : Tendsto (fun n => eLpNorm (f n - pX) 1 volume) atTop (𝓝 0) := by
    have hcomp :
        Tendsto
          (fun n => eLpNorm
            (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 (u n).toNNReal) - pX) 1 volume)
          atTop (𝓝 0) :=
      (convDensityAdd_tendsto_L1_zero hpX_nn hpX_meas hpX_int hpX_mom).comp hu_lim
    refine hcomp.congr (fun n => ?_)
    have hwit : (u n).toNNReal = (⟨u n, (hu_pos n).le⟩ : ℝ≥0) :=
      NNReal.coe_injective (Real.coe_toNNReal _ (hu_pos n).le)
    rw [hf_def, hwit]
  -- Measurability of every member (and of the limit) — needed for measure convergence.
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) volume := fun n =>
    (EPIConvDensity.convDensityAdd_pXpY_measurable pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩)
      hpX_meas (measurable_gaussianPDFReal _ _)).aestronglyMeasurable
  have hpX_aesm : AEStronglyMeasurable pX volume := hpX_meas.aestronglyMeasurable
  -- L¹ convergence ⟹ convergence in measure.
  have hmeas : TendstoInMeasure volume f atTop pX :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf_meas hpX_aesm hL1
  -- Convergence in measure ⟹ a.e. convergence along a subsequence.
  obtain ⟨ns, hns_mono, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨ns, hns_mono, ?_⟩
  -- Compose the pointwise density convergence with the continuous map `negMulLog`.
  filter_upwards [hns_ae] with x hx
  exact (Real.continuous_negMulLog.tendsto (pX x)).comp hx

end InformationTheory.Shannon
