import InformationTheory.Shannon.EntropyPower.Ext
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Construction
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# TruncationLimit — core part

Foundational layer for the truncation + monotone-limit route.

## Main definitions

* `truncW` — conditioning `P` on the `W`-event `{|W| ≤ n}` (single-variable truncation).
* `crossPos` / `crossNeg` — the positive and negative parts of the cross-entropy, as `ℝ≥0∞`-valued
  `lintegral`s.

## Main statements

* `rnDeriv_cond_eq` — Radon–Nikodym derivative of a conditioned measure.
* `ennreal_gibbs_rearranged` — a `⊤`-tolerant `ℝ≥0∞` rearrangement of the Gibbs inequality.
* `conv_eq_withDensity_translate_average` — the sum law as a translate-average `withDensity`,
  needing only the left factor a.c.
* `condDistrib_ae_absolutelyContinuous_indep_add` — per-fibre absolute continuity of the
  affine-shift fibre against the sum marginal.
* `negPart_negMulLog_conv_single_ne_top` — single-component negative-part finiteness of the sum law.

## Implementation notes

* The cross-entropy is kept as `ℝ≥0∞`-valued positive/negative parts (`crossPos` / `crossNeg`)
  rather than an `ℝ`-valued difference, so that the Gibbs inequality can be stated in a rearranged
  form that avoids the `⊤ - ⊤` indeterminacy and remains valid when `h(μ) = ⊤`.

Re-exported by the umbrella `InformationTheory.Shannon.EPI.Unconditional.TruncationLimit`; the
downstream `Mono` / `Limit` parts import this.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Single-variable truncation: `truncW P W n` conditions `P` on the event `{ω | |W ω| ≤ n}`, i.e.
on `W` taking values in `[-n, n]`. Each `truncW P W n` has compact support (hence finite variance
and finite entropy) and preserves absolute continuity.

@audit:ok -/
noncomputable def truncW (P : Measure Ω) (W : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P {ω | |W ω| ≤ (n : ℝ)}

/-- Radon–Nikodym derivative of a conditioned measure: for a probability measure `μ` and a
measurable set `s` of positive mass,
`(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`.

@audit:ok -/
theorem rnDeriv_cond_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) :
    (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] fun x ↦ (μ s)⁻¹ * s.indicator (μ.rnDeriv volume) x := by
  have hr : (μ s)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpos
  have h1 : (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume := by
    show ((μ s)⁻¹ • μ.restrict s).rnDeriv volume =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume
    exact Measure.rnDeriv_smul_left_of_ne_top (μ.restrict s) volume hr
  have h2 : (μ.restrict s).rnDeriv volume =ᵐ[volume] s.indicator (μ.rnDeriv volume) :=
    Measure.rnDeriv_restrict μ volume hs
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [Pi.smul_apply, hx, smul_eq_mul]

/-- **truncated sum law is dominated by the full sum law (measure level)**: pushing the truncated
measure `truncW P W n = P[| {|W| ≤ n}]` forward through `W + V` is bounded above by the inverse-mass
scaled pushforward of `P` through `W + V`. Pure measure monotonicity (no convolution / density):
`cond P E = (P E)⁻¹ • P.restrict E ≤ (P E)⁻¹ • P` via `restrict_le_self`, then push forward
(`Measure.map_smul` + `Measure.map_mono`). Used downstream for the klDiv expansion of the truncated
sum law. (`hn` is a regularity precondition kept for API symmetry; the `≤` direction does not use
it, since `cond P E = 0 ≤ anything` when `P E = 0`.)
@audit:ok -/
theorem map_truncW_add_le_smul_map_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (n : ℕ)
    (_hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    (truncW P W n).map (fun ω ↦ W ω + V ω)
      ≤ (P {ω | |W ω| ≤ (n : ℝ)})⁻¹ • P.map (fun ω ↦ W ω + V ω) := by
  set g : Ω → ℝ := fun ω ↦ W ω + V ω with hg_def
  have hg : Measurable g := hW.add hV
  set E : Set Ω := {ω | |W ω| ≤ (n : ℝ)} with hE_def
  -- Expand `truncW P W n = cond P E = (P E)⁻¹ • P.restrict E`, push forward, and dominate.
  have hcond : (truncW P W n).map g = (P E)⁻¹ • (P.restrict E).map g := by
    rw [truncW]
    show ((P E)⁻¹ • P.restrict E).map g = (P E)⁻¹ • (P.restrict E).map g
    exact Measure.map_smul (P E)⁻¹ (P.restrict E) g
  rw [hcond]
  -- `(P.restrict E).map g ≤ P.map g` (restrict_le_self + map_mono), then scale by `(P E)⁻¹`.
  have hle : (P.restrict E).map g ≤ P.map g :=
    Measure.map_mono Measure.restrict_le_self hg
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (hle s) _

/-- **a.c. corollary of the truncated-sum-law domination**: the truncated sum law `truncW P W n`
pushed through `W + V` is absolutely continuous w.r.t. the full sum law `P.map (W + V)`. Immediate
from `map_truncW_add_le_smul_map_add` via `absolutelyContinuous_of_le_smul` (`μ' ≤ c • μ → μ' ≪ μ`,
unconditional in `c`). Used downstream for the klDiv expansion of the truncated truncW sum law.
@audit:ok -/
theorem map_truncW_add_absolutelyContinuous_map_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (n : ℕ)
    (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    (truncW P W n).map (fun ω ↦ W ω + V ω) ≪ P.map (fun ω ↦ W ω + V ω) := by
  exact Measure.absolutelyContinuous_of_le_smul
    (map_truncW_add_le_smul_map_add W V P hW hV n hn)

/-! ### Finiteness-free `ℝ≥0∞` cross-entropy (Gibbs)

The Gibbs inequality `h(μ) ≤ crossEnt(μ, ν)` is built in an `ℝ≥0∞`-`lintegral` form that requires no
finiteness, rather than in the in-tree `ℝ`-valued `differentialEntropy_le_cross_entropy` (which
needs a finite cross-integral and breaks down at `⊤`).

The cross-entropy is split into its positive and negative parts (`ℝ≥0∞`), with
`fν x := (ν.rnDeriv volume x).toReal`:

* `crossPos μ ν := ∫⁻ x, ofReal (-log fν x) ∂μ` — picks up the negative part of `log fν`.
* `crossNeg μ ν := ∫⁻ x, ofReal (log fν x) ∂μ` — picks up the positive part.

Then `crossEnt(μ, ν) = -∫ log fν ∂μ = crossPos - crossNeg`, handled in rearranged form over `ℝ≥0∞`
to avoid the `⊤ - ⊤` indeterminacy. The `⊤`-case Gibbs lands via the universal bound
`∫⁻ ofReal(-log r) ∂μ ≤ 1` (the content of `klFun ≥ 0`, from `-r log r ≤ 1`). -/

/-- Positive part of the cross-entropy (`ℝ≥0∞`):
`∫⁻ x, ofReal (-log ((ν.rnDeriv volume x).toReal)) ∂μ`,
integrating the negative values of the log-density of `ν` against `μ`. -/
noncomputable def crossPos (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂μ

/-- Negative part of the cross-entropy (`ℝ≥0∞`):
`∫⁻ x, ofReal (log ((ν.rnDeriv volume x).toReal)) ∂μ`,
integrating the positive values of the log-density of `ν` against `μ`. -/
noncomputable def crossNeg (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂μ

/-- Self-identity (positive part): the cross-entropy positive part of `ν` against itself equals the
positive part `A(ν) = ∫⁻ x, ofReal (negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume` of the a.c.
branch of `differentialEntropyExt`. Obtained by change of measure (`lintegral_rnDeriv_mul`).

@audit:ok -/
theorem crossPos_self (ν : Measure ℝ) [SigmaFinite ν] (hν : ν ≪ volume) :
    crossPos ν ν
      = ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume := by
  rw [crossPos]
  -- change of measure: `∫⁻ f ∂ν = ∫⁻ (ν.rnDeriv vol)·f ∂vol`.
  rw [← lintegral_rnDeriv_mul hν
    (f := fun x ↦ ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)))
    ((Real.measurable_log.comp
      (ν.measurable_rnDeriv volume).ennreal_toReal).neg.ennreal_ofReal.aemeasurable)]
  -- pointwise: `(ν.rnDeriv vol x)·ofReal(-log fν) = ofReal(negMulLog fν)` a.e. vol.
  refine lintegral_congr_ae ?_
  filter_upwards [ν.rnDeriv_lt_top volume] with x hx
  set t : ℝ := (ν.rnDeriv volume x).toReal with ht
  have ht_nn : 0 ≤ t := ENNReal.toReal_nonneg
  -- rewrite the multiplier `ν.rnDeriv vol x = ofReal t`.
  rw [show ν.rnDeriv volume x = ENNReal.ofReal t from (ENNReal.ofReal_toReal hx.ne).symm,
    ← ENNReal.ofReal_mul ht_nn, Real.negMulLog_def]
  congr 1
  ring

/-- Self-identity (negative part): the cross-entropy negative part of `ν` against itself equals the
negative part `B(ν) = ∫⁻ x, ofReal (-(negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume` of the a.c.
branch of `differentialEntropyExt`. The sign-flipped analogue of `crossPos_self`.

@audit:ok -/
theorem crossNeg_self (ν : Measure ℝ) [SigmaFinite ν] (hν : ν ≪ volume) :
    crossNeg ν ν
      = ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume := by
  rw [crossNeg]
  -- change of measure: `∫⁻ f ∂ν = ∫⁻ (ν.rnDeriv vol)·f ∂vol`.
  rw [← lintegral_rnDeriv_mul hν
    (f := fun x ↦ ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)))
    ((Real.measurable_log.comp
      (ν.measurable_rnDeriv volume).ennreal_toReal).ennreal_ofReal.aemeasurable)]
  -- pointwise: `(ν.rnDeriv vol x)·ofReal(log fν) = ofReal(-(negMulLog fν))` a.e. vol.
  refine lintegral_congr_ae ?_
  filter_upwards [ν.rnDeriv_lt_top volume] with x hx
  set t : ℝ := (ν.rnDeriv volume x).toReal with ht
  have ht_nn : 0 ≤ t := ENNReal.toReal_nonneg
  rw [show ν.rnDeriv volume x = ENNReal.ofReal t from (ENNReal.ofReal_toReal hx.ne).symm,
    ← ENNReal.ofReal_mul ht_nn, Real.negMulLog_def]
  congr 1
  ring

theorem integrable_of_lintegral_ofReal_pos_neg_ne_top {m : Measure ℝ} {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f m)
    (hpos : (∫⁻ x, ENNReal.ofReal (f x) ∂m) ≠ ⊤)
    (hneg : (∫⁻ x, ENNReal.ofReal (-(f x)) ∂m) ≠ ⊤) :
    Integrable f m := by
  refine ⟨hf_meas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hsplit : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x) + ENNReal.ofReal (-(f x)) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_or_gt 0 (f x) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_eq_zero.2 (by linarith : -(f x) ≤ 0), add_zero]
    · rw [abs_of_neg h, ENNReal.ofReal_eq_zero.2 (by linarith : f x ≤ 0), zero_add]
  calc (∫⁻ x, ‖f x‖ₑ ∂m)
      = ∫⁻ x, (ENNReal.ofReal (f x) + ENNReal.ofReal (-(f x))) ∂m := lintegral_congr hsplit
    _ = (∫⁻ x, ENNReal.ofReal (f x) ∂m) + ∫⁻ x, ENNReal.ofReal (-(f x)) ∂m :=
        lintegral_add_left' hf_meas.aemeasurable.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hpos.lt_top, hneg.lt_top⟩

/-- Rearranged `ℝ≥0∞` Gibbs inequality, finite-entropy branch: for `μ ≪ ν ≪ volume` (both
probability measures) with `μ` of finite differential entropy and the cross-entropy `μ`-integrable,
`A(μ) + crossNeg μ ν ≤ crossPos μ ν + B(μ)`. Here all four `lintegral`s are finite, so the bound
descends to the `ℝ`-valued Gibbs inequality and lifts back. The `A(μ) = ⊤` branch is handled by the
consumer form `ennreal_gibbs_rearranged`.

@audit:ok -/
private theorem ennreal_gibbs_rearranged_of_finite_ent {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_ac : μ ≪ volume) (hν_ac : ν ≪ volume) (hμν : μ ≪ ν)
    (hμ_ent : Integrable (fun x ↦ Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume)
    (h_cross_int : Integrable (fun x ↦ Real.log ((ν.rnDeriv volume x).toReal)) μ) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
        + crossNeg μ ν
      ≤ crossPos μ ν
        + ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume := by
  -- abbreviations for the four lintegrals (all finite under the regularity preconditions).
  set A : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume with hA
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB
  -- finiteness of all four from the integrability preconditions
  -- (`∫⁻ ofReal f ≤ ∫⁻ ‖f‖ₑ = hasFiniteIntegral`).
  have hbound : ∀ (f : ℝ → ℝ) (m : Measure ℝ), Integrable f m →
      (∫⁻ x, ENNReal.ofReal (f x) ∂m) ≠ ⊤ := by
    intro f m hf
    refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x ↦ ?_)
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hA_fin : A ≠ ⊤ := hbound _ _ hμ_ent
  have hB_fin : B ≠ ⊤ := hbound _ _ hμ_ent.neg
  have hCP_fin : crossPos μ ν ≠ ⊤ := by
    rw [crossPos]
    exact hbound _ _ h_cross_int.neg
  have hCN_fin : crossNeg μ ν ≠ ⊤ := by
    rw [crossNeg]
    exact hbound _ _ h_cross_int
  -- ℝ-valued Gibbs: `differentialEntropy μ ≤ -∫ log fν ∂μ`.
  have hgibbs : differentialEntropy μ ≤ - ∫ x, Real.log ((ν.rnDeriv volume x).toReal) ∂μ :=
    EPIInfiniteVarianceTruncation.differentialEntropy_le_cross_entropy
      hμ_ac hν_ac hμν hμ_ent h_cross_int
  -- decompose `differentialEntropy μ = A.toReal - B.toReal`.
  have hself : differentialEntropy μ = A.toReal - B.toReal := by
    rw [differentialEntropy, hA, hB]
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hμ_ent
  -- decompose `-∫ log fν ∂μ = crossPos.toReal - crossNeg.toReal`.
  have hcross : - ∫ x, Real.log ((ν.rnDeriv volume x).toReal) ∂μ
      = (crossPos μ ν).toReal - (crossNeg μ ν).toReal := by
    rw [← integral_neg, crossPos, crossNeg]
    have h := integral_eq_lintegral_pos_part_sub_lintegral_neg_part h_cross_int.neg
    simp only [Pi.neg_apply, neg_neg] at h
    exact h
  -- ℝ inequality with all four reals.
  rw [hself, hcross] at hgibbs
  -- lift to ℝ≥0∞: `A + crossNeg ≤ crossPos + B`.
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add hA_fin hCN_fin, ENNReal.toReal_add hCP_fin hB_fin]
  linarith

/-- Rearranged `ℝ≥0∞` Gibbs inequality (consumer form): for `μ ≪ ν ≪ volume` (both probability
measures) with `B(μ)` and `crossNeg μ ν` finite, `A(μ) + crossNeg μ ν ≤ crossPos μ ν + B(μ)`, where
`A(μ) = ∫⁻ ofReal(negMulLog fμ) ∂vol` and `B(μ) = ∫⁻ ofReal(-(negMulLog fμ)) ∂vol`. This version
allows `A(μ) = ⊤` (i.e. `h(μ) = +∞`): the proof splits on `A(μ)`, delegating the finite branch to
`ennreal_gibbs_rearranged_of_finite_ent` and closing the `⊤` branch via the universal bound
`∫⁻ ofReal(-log r) ∂μ ≤ 1` (the content of `klFun ≥ 0`), which forces `crossPos μ ν = ⊤`.

@audit:ok -/
theorem ennreal_gibbs_rearranged {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_ac : μ ≪ volume) (hν_ac : ν ≪ volume) (hμν : μ ≪ ν)
    (hμ_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤)
    (hCN_fin : crossNeg μ ν ≠ ⊤) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
        + crossNeg μ ν
      ≤ crossPos μ ν
        + ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume := by
  set A : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume with hA
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB
  by_cases hA_top : A = ⊤
  · -- A(μ) = ⊤ branch. LHS = `⊤ + crossNeg = ⊤`; goal needs `crossPos μ ν = ⊤`, then RHS = ⊤.
    -- ⊤-case Gibbs: `A(μ) = ⊤ ⟹ crossPos μ ν = ⊤` via pointwise subadditivity
    -- (`-log fμ = -log fν + -log r`, `r := dμ/dν`) + **negative part 1-bounded** (`-r log r ≤ 1`,
    -- = klFun ≥ 0 content). This needs no finiteness precondition.
    have hCP_top : crossPos μ ν = ⊤ := by
      -- The `dμ/dν` density as a real and the `μ`-a.e. chain `log fμ = log r + log fν`.
      set r : ℝ → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal with hr_def
      have h_rn_chain_μ : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[μ] μ.rnDeriv volume :=
        hμ_ac.ae_le (Measure.rnDeriv_mul_rnDeriv hμν)
      have h_rn_μν_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := Measure.rnDeriv_pos hμν
      have h_rn_μν_lt_top : ∀ᵐ x ∂μ, μ.rnDeriv ν x < ∞ :=
        hμν.ae_le (Measure.rnDeriv_lt_top μ ν)
      have h_rn_μvol_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv volume x := Measure.rnDeriv_pos hμ_ac
      have h_rn_νvol_lt_top : ∀ᵐ x ∂μ, ν.rnDeriv volume x < ∞ :=
        hμ_ac.ae_le (Measure.rnDeriv_lt_top ν volume)
      -- Step 2 (μ-a.e.): `ofReal(-log fμ) ≤ ofReal(-log fν) + ofReal(-log r)`.
      have hsub : ∀ᵐ x ∂μ,
          ENNReal.ofReal (-Real.log ((μ.rnDeriv volume x).toReal))
            ≤ ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal))
              + ENNReal.ofReal (-Real.log (r x)) := by
        filter_upwards [h_rn_chain_μ, h_rn_μν_pos, h_rn_μν_lt_top, h_rn_μvol_pos, h_rn_νvol_lt_top]
          with x h_chain h_μν_pos h_μν_lt_top h_μvol_pos h_νvol_lt_top
        have h_combine : μ.rnDeriv volume x = μ.rnDeriv ν x * ν.rnDeriv volume x := by
          rw [← h_chain]; rfl
        have hr_pos : 0 < r x := ENNReal.toReal_pos h_μν_pos.ne' h_μν_lt_top.ne
        have hν_vol_ne : ν.rnDeriv volume x ≠ 0 := by
          intro h0; rw [h_combine, h0, mul_zero] at h_μvol_pos; exact lt_irrefl 0 h_μvol_pos
        have hν_vol_pos : 0 < (ν.rnDeriv volume x).toReal :=
          ENNReal.toReal_pos hν_vol_ne h_νvol_lt_top.ne
        -- `log fμ = log r + log fν`.
        have hlog : Real.log ((μ.rnDeriv volume x).toReal)
            = Real.log (r x) + Real.log ((ν.rnDeriv volume x).toReal) := by
          rw [h_combine, ENNReal.toReal_mul,
            Real.log_mul (ENNReal.toReal_pos h_μν_pos.ne' h_μν_lt_top.ne).ne' hν_vol_pos.ne']
        rw [show -Real.log ((μ.rnDeriv volume x).toReal)
            = -Real.log ((ν.rnDeriv volume x).toReal) + -Real.log (r x) by rw [hlog]; ring]
        exact ENNReal.ofReal_add_le
      -- Step 3: integrate. `A(μ) = crossPos μ μ ≤ crossPos μ ν + ∫⁻ ofReal(-log r) ∂μ`.
      have hA_eq : A = crossPos μ μ := (crossPos_self μ hμ_ac).symm
      have hint_mono : crossPos μ μ
          ≤ ∫⁻ x, (ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal))
              + ENNReal.ofReal (-Real.log (r x))) ∂μ := by
        rw [crossPos]; exact lintegral_mono_ae hsub
      have hsplit : (∫⁻ x, (ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal))
            + ENNReal.ofReal (-Real.log (r x))) ∂μ)
          = crossPos μ ν + ∫⁻ x, ENNReal.ofReal (-Real.log (r x)) ∂μ := by
        rw [crossPos]
        exact lintegral_add_left'
          ((Real.measurable_log.comp (ν.measurable_rnDeriv volume).ennreal_toReal).neg
            |>.ennreal_ofReal.aemeasurable) _
      -- Step 4: `∫⁻ ofReal(-log r) ∂μ ≤ 1` (negative part 1-bounded, klFun ≥ 0).
      have hneg_le_one : (∫⁻ x, ENNReal.ofReal (-Real.log (r x)) ∂μ) ≤ 1 := by
        -- change of measure to ν: `∫⁻ f ∂μ = ∫⁻ (μ.rnDeriv ν)·f ∂ν`.
        rw [← lintegral_rnDeriv_mul hμν
          (f := fun x ↦ ENNReal.ofReal (-Real.log (r x)))
          ((Real.measurable_log.comp (μ.measurable_rnDeriv ν).ennreal_toReal).neg
            |>.ennreal_ofReal.aemeasurable)]
        calc (∫⁻ x, μ.rnDeriv ν x * ENNReal.ofReal (-Real.log (r x)) ∂ν)
            ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂ν := by
              refine lintegral_mono_ae ?_
              filter_upwards [μ.rnDeriv_lt_top ν] with x hx
              -- `μ.rnDeriv ν x = ofReal (r x)`, then
              -- `ofReal(r)·ofReal(-log r) = ofReal(-r log r) ≤ 1`.
              rw [hr_def, show μ.rnDeriv ν x = ENNReal.ofReal (μ.rnDeriv ν x).toReal from
                (ENNReal.ofReal_toReal hx.ne).symm,
                ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
              refine (ENNReal.ofReal_le_ofReal ?_).trans (by rw [ENNReal.ofReal_one])
              -- `(μ.rnDeriv ν x).toReal · (-log (μ.rnDeriv ν x).toReal) ≤ 1`.
              set s : ℝ := (μ.rnDeriv ν x).toReal with hs
              show s * -Real.log s ≤ 1
              rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := μ.rnDeriv ν x)) with hs0 | hs_pos
              · rw [show s = 0 from hs0.symm, zero_mul]; norm_num
              · -- `-s log s ≤ 1 - s ≤ 1` via `log (1/s) ≤ 1/s - 1`.
                have hlog_inv : Real.log (1 / s) ≤ 1 / s - 1 :=
                  Real.log_le_sub_one_of_pos (by positivity)
                rw [Real.log_div one_ne_zero hs_pos.ne', Real.log_one, zero_sub] at hlog_inv
                have : s * (-Real.log s) ≤ s * (1 / s - 1) := by
                  apply mul_le_mul_of_nonneg_left hlog_inv hs_pos.le
                have hsimp : s * (1 / s - 1) = 1 - s := by
                  rw [mul_sub, mul_one_div, div_self hs_pos.ne', mul_one]
                rw [hsimp] at this
                linarith
          _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
      -- assemble: `A = crossPos μ μ ≤ crossPos μ ν + (∫⁻ ofReal(-log r) ∂μ) ≤ crossPos μ ν + 1`.
      have hA_le : A ≤ crossPos μ ν + 1 := by
        calc A = crossPos μ μ := hA_eq
          _ ≤ crossPos μ ν + ∫⁻ x, ENNReal.ofReal (-Real.log (r x)) ∂μ := by
                rw [← hsplit]; exact hint_mono
          _ ≤ crossPos μ ν + 1 := by gcongr
      -- `A = ⊤` forces `crossPos μ ν = ⊤` (since `crossPos μ ν + 1 = ⊤` and `1 ≠ ⊤`).
      rw [hA_top] at hA_le
      by_contra hne
      have : crossPos μ ν + 1 < ⊤ :=
        ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hne, ENNReal.one_lt_top⟩
      exact this.ne (top_le_iff.1 hA_le)
    rw [hCP_top, top_add]; exact le_top
  · -- A(μ) < ⊤ branch: derive finite differential entropy of μ, delegate to `_of_finite_ent`.
    have hμ_ent : Integrable (fun x ↦ Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume := by
      refine integrable_of_lintegral_ofReal_pos_neg_ne_top
        ((Real.continuous_negMulLog.measurable.comp
          (μ.measurable_rnDeriv volume).ennreal_toReal).aestronglyMeasurable) ?_ ?_
      · exact hA_top
      · exact hμ_negPart_fin
    by_cases hCP_top : crossPos μ ν = ⊤
    · rw [hCP_top, top_add]; exact le_top
    · -- crossPos μ ν < ⊤: derive cross-entropy integrability, delegate.
      have h_cross_int :
          Integrable (fun x ↦ Real.log ((ν.rnDeriv volume x).toReal)) μ := by
        refine integrable_of_lintegral_ofReal_pos_neg_ne_top
          ((Real.measurable_log.comp
            (ν.measurable_rnDeriv volume).ennreal_toReal).aestronglyMeasurable) ?_ ?_
        · rw [crossNeg] at hCN_fin; exact hCN_fin
        · rw [crossPos] at hCP_top; exact hCP_top
      exact ennreal_gibbs_rearranged_of_finite_ent hμ_ac hν_ac hμν hμ_ent h_cross_int

/-- Translation invariance of per-fibre entropy integrability: if `negMulLog (rnDeriv ν volume)` is
integrable for `ν ≪ volume`, then so is the corresponding integrand for the translate
`ν.map (· + y)`, by Lebesgue translation invariance.

@audit:ok -/
theorem integrable_negMulLog_rnDeriv_map_add_const
    {ν : Measure ℝ} [SigmaFinite ν] (y : ℝ)
    (hν_ent : Integrable (fun x ↦ Real.negMulLog ((ν.rnDeriv volume x).toReal)) volume) :
    Integrable
      (fun x ↦ Real.negMulLog (((ν.map (fun x ↦ x + y)).rnDeriv volume x).toReal)) volume := by
  have hf : MeasurableEmbedding (fun x : ℝ ↦ x + y) := measurableEmbedding_addRight y
  have h_map_vol : (volume : Measure ℝ).map (fun x ↦ x + y) = volume :=
    MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) y
  -- `(· + y)` is measure-preserving on Lebesgue.
  have hmp : MeasurePreserving (fun x : ℝ ↦ x + y) volume volume :=
    ⟨hf.measurable, h_map_vol⟩
  -- rnDeriv after the shift, evaluated at `x + y`, equals rnDeriv before the shift.
  have h_rn := hf.rnDeriv_map ν (volume : Measure ℝ)
  rw [h_map_vol] at h_rn
  -- It suffices to prove integrability of the composition `g ∘ (· + y)` and then transfer.
  have hcomp_int : Integrable
      (fun x ↦ Real.negMulLog ((((ν.map (fun x ↦ x + y)).rnDeriv volume) (x + y)).toReal))
      volume := by
    refine hν_ent.congr ?_
    filter_upwards [h_rn] with x hx
    rw [hx]
  -- transfer along the measure-preserving embedding `(· + y)`.
  exact (hmp.integrable_comp_emb hf).mp hcomp_int

/-- **convolution density as translate-average** (only the LEFT factor a.c.): for `μW ≪ volume`
the sum law `μW ∗ μV` is `volume.withDensity (z ↦ ∫⁻ v, f_W (z - v) ∂μV)`
where `f_W = μW.rnDeriv vol`.
Unlike the route-T `convDensityAdd` machinery (`EPIConvDensity`, which requires **both** components
a.c.), this only needs `μW` a.c.; `μV` is a general (probability) measure.
`lintegral_conv` (Tonelli)
+ `withDensity_rnDeriv_eq` (recover `μW = vol.withDensity f_W`) + translation invariance.
@audit:ok -/
theorem conv_eq_withDensity_translate_average
    (μW μV : Measure ℝ) [SFinite μW] [SFinite μV] (hμW : μW ≪ volume) :
    μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z ↦ ∫⁻ v, μW.rnDeriv volume (z - v) ∂μV) := by
  set g : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hg_def
  have hg_meas : Measurable g := Measure.measurable_rnDeriv _ _
  have hμW_wd : μW = (volume : Measure ℝ).withDensity g :=
    (Measure.withDensity_rnDeriv_eq μW volume hμW).symm
  refine Measure.ext fun A hA ↦ ?_
  have hind : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  have hinner_meas : Measurable (fun x ↦ ∫⁻ v, A.indicator 1 (x + v) ∂μV) :=
    (hind.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'
  have hL : (μW ∗ μV) A = ∫⁻ x, (∫⁻ v, A.indicator 1 (x + v) ∂μV) ∂μW := by
    rw [← lintegral_indicator_one hA, Measure.lintegral_conv hind]
  have hR : ((volume : Measure ℝ).withDensity (fun z ↦ ∫⁻ v, g (z - v) ∂μV)) A
      = ∫⁻ z, A.indicator 1 z * (∫⁻ v, g (z - v) ∂μV) ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    apply lintegral_congr; intro z
    by_cases hz : z ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hL, hR, hμW_wd,
    lintegral_withDensity_eq_lintegral_mul₀ hg_meas.aemeasurable hinner_meas.aemeasurable]
  calc ∫⁻ x, (g * fun x ↦ ∫⁻ v, A.indicator 1 (x + v) ∂μV) x ∂volume
      = ∫⁻ x, ∫⁻ v, g x * A.indicator 1 (x + v) ∂μV ∂volume := by
        apply lintegral_congr; intro x
        rw [Pi.mul_apply]
        exact (lintegral_const_mul (g x)
          (hind.comp ((measurable_const (a := x)).add measurable_id))).symm
    _ = ∫⁻ v, ∫⁻ x, g x * A.indicator 1 (x + v) ∂volume ∂μV := by
        rw [lintegral_lintegral_swap]
        exact ((hg_meas.comp measurable_fst).mul
          (hind.comp (measurable_fst.add measurable_snd))).aemeasurable
    _ = ∫⁻ v, ∫⁻ z, g (z - v) * A.indicator 1 z ∂volume ∂μV := by
        apply lintegral_congr; intro v
        rw [← lintegral_add_right_eq_self
          (μ := (volume : Measure ℝ)) (fun z ↦ g (z - v) * A.indicator 1 z) v]
        apply lintegral_congr; intro x; rw [add_sub_cancel_right]
    _ = ∫⁻ v, ∫⁻ z, A.indicator 1 z * g (z - v) ∂volume ∂μV := by
        apply lintegral_congr; intro v; apply lintegral_congr; intro z; rw [mul_comm]
    _ = ∫⁻ z, A.indicator 1 z * (∫⁻ v, g (z - v) ∂μV) ∂volume := by
        rw [lintegral_lintegral_swap
          (by exact ((hind.comp measurable_snd).mul
            (hg_meas.comp (measurable_snd.sub measurable_fst))).aemeasurable)]
        apply lintegral_congr; intro z
        exact lintegral_const_mul (A.indicator 1 z)
          (hg_meas.comp ((measurable_const (a := z)).sub measurable_id))

/-- **translate of an a.c. measure as withDensity**: `(vol.withDensity f).map (·+z) =
vol.withDensity (f (·-z))`. Lebesgue translation invariance. Used to express the
affine-shift fibre `(Q.map W).map(·+z)` as a `withDensity` for the per-fibre a.c. argument.
@audit:ok -/
theorem map_add_const_withDensity (f : ℝ → ℝ≥0∞) (z : ℝ) :
    ((volume : Measure ℝ).withDensity f).map (fun x ↦ x + z)
      = (volume : Measure ℝ).withDensity (fun x ↦ f (x - z)) := by
  have hmap : Measurable (fun x : ℝ ↦ x + z) := measurable_id.add_const z
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply hmap hA, withDensity_apply _ (hmap hA), withDensity_apply _ hA,
    ← lintegral_indicator (hmap hA), ← lintegral_indicator hA]
  rw [← lintegral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun x ↦ A.indicator (fun y ↦ f (y - z)) x) z]
  apply lintegral_congr; intro x
  by_cases hx : x + z ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by simpa using hx), add_sub_cancel_right]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa using hx)]

/-- **per-fibre a.c. (continuous disintegration, sum structure)**: for `W ⊥ V` under `Q` with
`Q.map W ≪ volume`, the affine-shift fibre `(Q.map W).map (·+z)` (= the per-fibre conditional law
of `W+V` given `V=z`, via `affineShiftKernel`) is a.c. w.r.t. the sum marginal
`(Q.map W) ∗ (Q.map V)`
for a.e. `z ∂(Q.map V)`. This is the **continuous** version of the general disintegration fact
`condDistrib z ≪ μ.map X` (Mathlib's general/non-discrete version is absent; the in-tree
`Bridge.condDistrib_ae_absolutelyContinuous_map` is `[Countable X]`-only, unusable for `X = ℝ`).

The argument uses the sum density `r(x) = ∫⁻ v, f_W(x-v) ∂μ_V` and the translate density
`f_W(·-z)`: a Fubini argument gives `(μ_V × vol)({(z,x) : r(x) = 0 ∧ 0 < f_W(x-z)}) = 0`, and a swap
yields `{r = 0} ⊆ {f_W(·-z) = 0}` vol-a.e. for a.e. `z`, which converts to absolute continuity
between the `withDensity` measures.
@audit:ok -/
theorem condDistrib_ae_absolutelyContinuous_indep_add
    {μW μV : Measure ℝ} [SFinite μW] [SFinite μV] [IsProbabilityMeasure μV] (hμW_ac : μW ≪ volume) :
    ∀ᵐ z ∂μV, (μW.map (fun x ↦ x + z)) ≪ (μW ∗ μV) := by
  have hconv : μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z ↦ ∫⁻ v, μW.rnDeriv volume (z - v) ∂μV) :=
    conv_eq_withDensity_translate_average μW μV hμW_ac
  have htrans : ∀ z : ℝ, μW.map (fun x ↦ x + z)
      = (volume : Measure ℝ).withDensity (fun x ↦ μW.rnDeriv volume (x - z)) := by
    intro z
    conv_lhs => rw [show μW = (volume : Measure ℝ).withDensity (μW.rnDeriv volume) from
      (Measure.withDensity_rnDeriv_eq μW volume hμW_ac).symm]
    rw [map_add_const_withDensity (μW.rnDeriv volume) z]
  set f : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hf_def
  have hf_meas : Measurable f := Measure.measurable_rnDeriv _ _
  set r : ℝ → ℝ≥0∞ := fun z ↦ ∫⁻ v, f (z - v) ∂μV with hr_def
  have hr_meas : Measurable r :=
    (hf_meas.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | r p.2 = 0 ∧ 0 < f (p.2 - p.1)} with hS_def
  have hSmeas : MeasurableSet S :=
    ((hr_meas.comp measurable_snd) (measurableSet_singleton 0)).inter
      (measurableSet_lt measurable_const (hf_meas.comp (measurable_snd.sub measurable_fst)))
  have hslice_x : ∀ x : ℝ, μV {v | r x = 0 ∧ 0 < f (x - v)} = 0 := by
    intro x
    by_cases hrx : r x = 0
    · have hfae : ∀ᵐ v ∂μV, f (x - v) = 0 :=
        (lintegral_eq_zero_iff (hf_meas.comp (measurable_const.sub measurable_id))).mp hrx
      have hfzero : μV {v | ¬ (f (x - v) = 0)} = 0 := hfae
      exact measure_mono_null (fun v hv ↦ pos_iff_ne_zero.mp hv.2) hfzero
    · have : {v | r x = 0 ∧ 0 < f (x - v)} = ∅ := by ext v; simp [hrx]
      rw [this]; simp
  have hkey : ∫⁻ z, (volume : Measure ℝ) (Prod.mk z ⁻¹' S) ∂μV = 0 := by
    rw [← Measure.prod_apply hSmeas, Measure.prod_apply_symm hSmeas]
    simp_rw [show ∀ x : ℝ, (fun v ↦ (v, x)) ⁻¹' S = {v | r x = 0 ∧ 0 < f (x - v)} from
        fun _ ↦ rfl,
      hslice_x, lintegral_zero]
  have hae_slice : ∀ᵐ z ∂μV, (volume : Measure ℝ) (Prod.mk z ⁻¹' S) = 0 :=
    (lintegral_eq_zero_iff (measurable_measure_prodMk_left hSmeas)).mp hkey
  filter_upwards [hae_slice] with z hz
  rw [htrans z, hconv]
  have hfz_meas : Measurable (fun x : ℝ ↦ f (x - z)) := hf_meas.comp (measurable_id.sub_const z)
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 ↦ ?_
  rw [withDensity_apply _ hA] at hA0 ⊢
  rw [setLIntegral_eq_zero_iff hA hr_meas] at hA0
  rw [setLIntegral_eq_zero_iff hA hfz_meas]
  have hnull2 : ∀ᵐ x ∂volume, ¬ (r x = 0 ∧ 0 < f (x - z)) := by
    rw [ae_iff]
    convert (hz : (volume : Measure ℝ) (Prod.mk z ⁻¹' S) = 0) using 2; ext x; simp [hS_def]
  filter_upwards [hA0, hnull2] with x hx0 hxsub hxA
  by_contra hne
  exact hxsub ⟨hx0 hxA, pos_iff_ne_zero.mpr hne⟩

/-- Per-`z` Jensen a.e. bound feeding `negPart_negMulLog_conv_single_ne_top`:
`max (φ (r z)) 0 ≤ ∫ v, max (φ (fW (z - v))) 0 ∂μV` a.e., where `φ t = t log t`,
`fW = toReal ∘ μW.rnDeriv`, `r = toReal ∘ (μW ∗ μV).rnDeriv`. -/
theorem convDensity_jensen_negMulLog_ae_bound
    (μW μV : Measure ℝ) [IsFiniteMeasure μW] [IsProbabilityMeasure μV]
    (hr_conv : (fun x ↦ ((μW ∗ μV).rnDeriv volume x).toReal)
      =ᵐ[volume] fun z ↦ ∫ v, (μW.rnDeriv volume (z - v)).toReal ∂μV)
    (hsec_Cq : ∀ᵐ z ∂volume,
      Integrable (fun v ↦ max ((μW.rnDeriv volume (z - v)).toReal
        * Real.log ((μW.rnDeriv volume (z - v)).toReal)) 0) μV)
    (hsec_fW : ∀ᵐ z ∂volume,
      Integrable (fun v ↦ (μW.rnDeriv volume (z - v)).toReal) μV) :
    ∀ᵐ z ∂volume,
      max (((μW ∗ μV).rnDeriv volume z).toReal * Real.log (((μW ∗ μV).rnDeriv volume z).toReal)) 0
        ≤ ∫ v, max ((μW.rnDeriv volume (z - v)).toReal
            * Real.log ((μW.rnDeriv volume (z - v)).toReal)) 0 ∂μV := by
  set fW : ℝ → ℝ := fun x ↦ (μW.rnDeriv volume x).toReal with hfW_def
  set r : ℝ → ℝ := fun x ↦ ((μW ∗ μV).rnDeriv volume x).toReal with hr_def
  set φ : ℝ → ℝ := fun t ↦ t * Real.log t with hφ_def
  have hφ_eq : ∀ t, -(Real.negMulLog t) = φ t := by
    intro t; show -(-t * Real.log t) = t * Real.log t; ring
  have hfW_meas : Measurable fW := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hfW_nn : ∀ x, 0 ≤ fW x := fun _ ↦ ENNReal.toReal_nonneg
  have hφ_meas : Measurable φ := measurable_id.mul (Real.measurable_log.comp measurable_id)
  set Cq : ℝ → ℝ := fun w ↦ max (φ (fW w)) 0 with hCq_def
  have hCq_nn : ∀ w, 0 ≤ Cq w := fun _ ↦ le_max_right _ _
  set G : ℝ → ℝ := fun z ↦ max (φ (r z)) 0 with hG_def
  filter_upwards [hr_conv, hsec_Cq, hsec_fW] with z hz hzCq hzfW
  -- abbreviation `f v = fW (z - v)`.
  set f : ℝ → ℝ := fun v ↦ fW (z - v) with hf_def
  have hf_nn : ∀ v, 0 ≤ f v := fun _ ↦ hfW_nn _
  -- `max (φ (f v)) 0 = Cq (z - v)` and `(φ∘f)⁻ = Cm (z - v)`.
  have hCqf_int : Integrable (fun v ↦ max (φ (f v)) 0) μV := hzCq
  set Cm : ℝ → ℝ := fun v ↦ max (-(φ (f v))) 0 with hCm_def
  -- `Cm v = (negMulLog (f v))⁺ ≤ 1` pointwise (since `negMulLog t ≤ 1 - t ≤ 1` for `t ≥ 0`),
  -- and constant `1` is integrable over the **probability** measure `μV`.
  have hCm_meas : Measurable Cm :=
    ((hφ_meas.comp (hfW_meas.comp (measurable_const.sub measurable_id))).neg).max measurable_const
  have hCm_le_one : ∀ v, Cm v ≤ 1 := by
    intro v
    rw [hCm_def]
    refine max_le ?_ (by norm_num)
    have hnml : -(φ (f v)) = Real.negMulLog (f v) := by rw [← hφ_eq (f v), neg_neg]
    rw [hnml]
    calc Real.negMulLog (f v) ≤ 1 - f v := Real.negMulLog_le_one_sub_self (hf_nn v)
      _ ≤ 1 := by have := hf_nn v; linarith
  have hCm_int : Integrable Cm μV := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hCm_meas.aestronglyMeasurable ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hCm_le_one v
  -- `φ ∘ f = (φ∘f)⁺ - (φ∘f)⁻`, hence integrable.
  have hφf_eq : (fun v ↦ φ (f v)) = fun v ↦ max (φ (f v)) 0 - Cm v := by
    funext v
    show φ (f v) = max (φ (f v)) 0 - max (-(φ (f v))) 0
    rcases le_or_gt 0 (φ (f v)) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -(φ (f v)) ≤ 0)]; ring
    · rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(φ (f v)))]; ring
  have hf_int : Integrable f μV := hzfW
  have hφf_int : Integrable (fun v ↦ φ (f v)) μV := by
    rw [hφf_eq]; exact hCqf_int.sub hCm_int
  -- Jensen:  `φ (∫ f ∂μV) ≤ ∫ φ∘f ∂μV`.
  have hjz : φ (∫ v, f v ∂μV) ≤ ∫ v, φ (f v) ∂μV := by
    have := Real.convexOn_mul_log.map_integral_le
      (μ := μV) (f := f) (g := φ)
      Real.continuous_mul_log.continuousOn
      isClosed_Ici
      (Filter.Eventually.of_forall (fun v ↦ hf_nn v))
      hf_int hφf_int
    simpa only [hφ_def] using this
  -- `r z = ∫ v, f v ∂μV`  (the convolution-density identity `hz`).
  have hrz_eq : r z = ∫ v, f v ∂μV := hz
  have hstep1 : φ (r z) ≤ ∫ v, φ (f v) ∂μV := by rw [hrz_eq]; exact hjz
  have hstep2 : (∫ v, φ (f v) ∂μV) ≤ ∫ v, max (φ (f v)) 0 ∂μV :=
    integral_mono hφf_int hCqf_int (fun v ↦ le_max_left _ _)
  have hstep3 : (∫ v, max (φ (f v)) 0 ∂μV) = ∫ v, Cq (z - v) ∂μV := rfl
  have hCq_int_z : (0 : ℝ) ≤ ∫ v, Cq (z - v) ∂μV :=
    integral_nonneg (fun v ↦ hCq_nn _)
  show max (φ (r z)) 0 ≤ ∫ v, Cq (z - v) ∂μV
  exact max_le (by rw [← hstep3]; exact le_trans hstep1 hstep2) hCq_int_z

/-- Single-component negative-part finiteness of the sum law: `B(μW ∗ μV) < ⊤` from `B(μW) < ⊤`.
The averaging is over the general probability measure `μV` (no absolute continuity on `μV` needed,
so it works even when `V` is non-a.c.), bounding the W-marginal negative part `B(μW)`. The core is a
per-`z` Jensen bound on the convex `t ↦ t log t` against the convolution density, followed by a
Tonelli collapse using translation invariance.

@audit:ok -/
theorem negPart_negMulLog_conv_single_ne_top
    (μW μV : Measure ℝ) [IsFiniteMeasure μW] [IsProbabilityMeasure μV] (hμW : μW ≪ volume)
    (hμW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μW.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((μW ∗ μV).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := by
  -- densities and `φ t = t log t = -(negMulLog t)`.
  set fW : ℝ → ℝ := fun x ↦ (μW.rnDeriv volume x).toReal with hfW_def
  set r : ℝ → ℝ := fun x ↦ ((μW ∗ μV).rnDeriv volume x).toReal with hr_def
  set φ : ℝ → ℝ := fun t ↦ t * Real.log t with hφ_def
  have hφ_eq : ∀ t, -(Real.negMulLog t) = φ t := by
    intro t; show -(-t * Real.log t) = t * Real.log t; ring
  -- basic measurability / nonnegativity.
  have hfW_meas : Measurable fW := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hfW_nn : ∀ x, 0 ≤ fW x := fun _ ↦ ENNReal.toReal_nonneg
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hr_nn : ∀ x, 0 ≤ r x := fun _ ↦ ENNReal.toReal_nonneg
  have hφ_meas : Measurable φ := measurable_id.mul (Real.measurable_log.comp measurable_id)
  -- `Cq w = (φ (fW w))⁺`.  `C = ∫⁻ ofReal Cq = ∫⁻ ofReal (-(negMulLog fW)) = hμW_negPart_fin`.
  set Cq : ℝ → ℝ := fun w ↦ max (φ (fW w)) 0 with hCq_def
  have hCq_nn : ∀ w, 0 ≤ Cq w := fun _ ↦ le_max_right _ _
  have hCq_meas : Measurable Cq := (hφ_meas.comp hfW_meas).max measurable_const
  set C : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (Cq w) ∂volume with hC_def
  -- `∫⁻ ofReal Cq = ∫⁻ ofReal (-(negMulLog fW))`  (the `max ... 0` is killed by `ofReal`).
  have hC_eq : C = ∫⁻ w, ENNReal.ofReal (-(Real.negMulLog (fW w))) ∂volume := by
    rw [hC_def]; apply lintegral_congr; intro w
    show ENNReal.ofReal (max (φ (fW w)) 0) = ENNReal.ofReal (-(Real.negMulLog (fW w)))
    rw [← hφ_eq (fW w)]
    rcases le_or_gt 0 (-(Real.negMulLog (fW w))) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_of_nonpos (le_refl 0)]
  have hC_lt_top : C ≠ ⊤ := by rw [hC_eq]; exact hμW_negPart_fin
  -- the sum law is `vol.withDensity (z ↦ ∫⁻ v, f_W(z-v) ∂μV)` (left-factor a.c. only).
  set fWe : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hfWe_def
  have hfWe_meas : Measurable fWe := Measure.measurable_rnDeriv _ _
  have hconv : μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z ↦ ∫⁻ v, fWe (z - v) ∂μV) :=
    conv_eq_withDensity_translate_average μW μV hμW
  have hrho_meas : Measurable (fun z ↦ ∫⁻ v, fWe (z - v) ∂μV) :=
    (hfWe_meas.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  -- `r =ᵐ[vol] fun z => ∫ v, fW (z-v) ∂μV`
  -- (toReal of the convolution density, μV is a prob measure).
  have hr_conv : r =ᵐ[volume] fun z ↦ ∫ v, fW (z - v) ∂μV := by
    have h_rn : (μW ∗ μV).rnDeriv volume =ᵐ[volume] fun z ↦ ∫⁻ v, fWe (z - v) ∂μV := by
      rw [hconv]; exact Measure.rnDeriv_withDensity volume hrho_meas
    have h_lt : ∀ᵐ z ∂volume, (μW ∗ μV).rnDeriv volume z < ∞ :=
      Measure.rnDeriv_lt_top (μW ∗ μV) volume
    filter_upwards [h_rn, h_lt] with z hz hz_lt
    show ((μW ∗ μV).rnDeriv volume z).toReal = ∫ v, fW (z - v) ∂μV
    -- `∫⁻ v, fWe(z-v) ∂μV < ∞` ⟹ `fWe(z-v) < ∞` μV-a.e. (finite integral ⟹ a.e. finite).
    have hfWe_z_meas : Measurable (fun v ↦ fWe (z - v)) := by fun_prop
    have hint_lt : (∫⁻ v, fWe (z - v) ∂μV) < ∞ := hz ▸ hz_lt
    have hae_lt : ∀ᵐ v ∂μV, fWe (z - v) < ∞ :=
      ae_lt_top' hfWe_z_meas.aemeasurable hint_lt.ne
    rw [hz]
    exact (integral_toReal hfWe_z_meas.aemeasurable hae_lt).symm
  -- ============================================================================
  -- Tonelli identity:  `∫⁻ z ∫⁻ v ofReal (g (z - v)) ∂μV ∂vol = (μV univ)·(∫⁻ ofReal g)`,
  -- for nonneg measurable `g`, via translation invariance + swap.
  -- ============================================================================
  have hkernel_lint : ∀ g : ℝ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
      ∫⁻ z, ∫⁻ v, ENNReal.ofReal (g (z - v)) ∂μV ∂volume
        = (μV Set.univ) * (∫⁻ w, ENNReal.ofReal (g w) ∂volume) := by
    intro g hg hg_nn
    -- swap to `∫⁻ v ∫⁻ z`, translate `z ↦ z + v`, factor.
    have hswap : ∫⁻ z, ∫⁻ v, ENNReal.ofReal (g (z - v)) ∂μV ∂volume
        = ∫⁻ v, ∫⁻ z, ENNReal.ofReal (g (z - v)) ∂volume ∂μV := by
      rw [lintegral_lintegral_swap]
      exact (hg.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal.aemeasurable
    rw [hswap]
    have hinner : ∀ v, ∫⁻ z, ENNReal.ofReal (g (z - v)) ∂volume
        = ∫⁻ w, ENNReal.ofReal (g w) ∂volume := fun v ↦
      lintegral_sub_right_eq_self (fun w ↦ ENNReal.ofReal (g w)) v
    simp_rw [hinner]
    rw [lintegral_const, mul_comm]
  -- product-measure integrability of `K (z, v) = fW (z - v)` (needed for the per-z section
  -- integrability of `v ↦ Cq (z - v)`).
  have hkernel_int : ∀ g : ℝ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
      (∫⁻ w, ENNReal.ofReal (g w) ∂volume) ≠ ⊤ →
      Integrable (fun p : ℝ × ℝ ↦ g (p.1 - p.2)) (volume.prod μV) := by
    intro g hg hg_nn hg_fin
    have hgp_meas : Measurable (fun p : ℝ × ℝ ↦ g (p.1 - p.2)) :=
      hg.comp (measurable_fst.sub measurable_snd)
    refine ⟨hgp_meas.aestronglyMeasurable, ?_⟩
    have hnn : ∀ᵐ p : ℝ × ℝ ∂(volume.prod μV), 0 ≤ g (p.1 - p.2) :=
      Filter.Eventually.of_forall (fun p ↦ hg_nn _)
    rw [hasFiniteIntegral_iff_ofReal hnn,
      lintegral_prod _ hgp_meas.ennreal_ofReal.aemeasurable,
      hkernel_lint g hg hg_nn, measure_univ, one_mul]
    exact lt_of_le_of_ne le_top hg_fin
  -- per-`z` section integrability: `v ↦ Cq (z - v)` integrable w.r.t. `μV`  (a.e. `z`).
  have hsec_Cq : ∀ᵐ z ∂volume, Integrable (fun v ↦ Cq (z - v)) μV := by
    have := (hkernel_int Cq hCq_meas hCq_nn (by rw [← hC_def]; exact hC_lt_top)).prod_right_ae
    exact this
  -- per-`z` section integrability of `v ↦ fW (z - v)` (the Jensen integrand `f`).
  have hsec_fW : ∀ᵐ z ∂volume, Integrable (fun v ↦ fW (z - v)) μV := by
    have := (hkernel_int fW hfW_meas hfW_nn (by
      -- `∫⁻ ofReal fW = μW univ = 1`  (probability density of `μW`).
      have hae_eq : (fun x ↦ ENNReal.ofReal (fW x)) =ᵐ[volume] μW.rnDeriv volume := by
        filter_upwards [μW.rnDeriv_ne_top volume] with x hx
        rw [hfW_def]; exact ENNReal.ofReal_toReal hx
      rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hμW]
      exact measure_ne_top _ _)).prod_right_ae
    exact this
  -- ============================================================================
  -- per-`z` Jensen bound:  `max (φ (r z)) 0 ≤ ∫ v, Cq (z - v) ∂μV`  (a.e. `z`).
  -- ============================================================================
  set G : ℝ → ℝ := fun z ↦ max (φ (r z)) 0 with hG_def
  have hG_nn : ∀ z, 0 ≤ G z := fun _ ↦ le_max_right _ _
  have hjensen : ∀ᵐ z ∂volume, G z ≤ ∫ v, Cq (z - v) ∂μV :=
    convDensity_jensen_negMulLog_ae_bound μW μV hr_conv hsec_Cq hsec_fW
  -- ============================================================================
  -- assemble:  `∫⁻ ofReal(-(negMulLog r)) = ∫⁻ ofReal(φ r) ≤ ∫⁻ ofReal G ≤ 1·C < ⊤`.
  -- ============================================================================
  have hgoal_le : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (r x))) ∂volume)
      ≤ ∫⁻ z, ENNReal.ofReal (G z) ∂volume := by
    apply lintegral_mono; intro z
    show ENNReal.ofReal (-(Real.negMulLog (r z))) ≤ ENNReal.ofReal (G z)
    rw [hφ_eq (r z)]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  refine ne_top_of_le_ne_top ?_ hgoal_le
  have hfinal : (∫⁻ z, ENNReal.ofReal (G z) ∂volume) ≤ (μV Set.univ) * C :=
    calc ∫⁻ z, ENNReal.ofReal (G z) ∂volume
        ≤ ∫⁻ z, ENNReal.ofReal (∫ v, Cq (z - v) ∂μV) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [hjensen] with z hz
          exact ENNReal.ofReal_le_ofReal hz
      _ ≤ ∫⁻ z, ∫⁻ v, ENNReal.ofReal (Cq (z - v)) ∂μV ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [hsec_Cq] with z hz
          calc ENNReal.ofReal (∫ v, Cq (z - v) ∂μV)
              = ∫⁻ v, ENNReal.ofReal (Cq (z - v)) ∂μV := by
                rw [ofReal_integral_eq_lintegral_ofReal hz
                  (Filter.Eventually.of_forall (fun v ↦ hCq_nn _))]
            _ ≤ _ := le_refl _
      _ = (μV Set.univ) * C := by rw [hkernel_lint Cq hCq_meas hCq_nn, hC_def]
  refine ne_top_of_le_ne_top ?_ hfinal
  rw [measure_univ, one_mul]; exact hC_lt_top

end InformationTheory.Shannon
