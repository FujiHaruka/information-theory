import InformationTheory.Shannon.EntropyPower.Ext
import InformationTheory.Shannon.EPI.Unconditional.CondEntropyExt
import InformationTheory.Shannon.EPI.Unconditional.Monotone
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
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Core

/-!
# TruncationLimit — Mono part

正部 lintegral の Fatou lift / 有限エントロピー単調性 (per-fibre translate Gibbs) /
per-n 截断単調性。Core part (truncW / conv 密度 / per-fibre a.c. / cross-entropy) に依存。
umbrella: `InformationTheory.Shannon.EPI.Unconditional.TruncationLimit`。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **negMulLog-Fatou helper** — 正部 lintegral `A` の Fatou lift。
density の toReal a.e. 収束 `f_{μ_n} → f_μ` から `A_μ ≤ liminf A_{μ_n}` を Fatou で出す
(`A μ := ∫⁻ x, ofReal (negMulLog (rnDeriv μ vol x).toReal) ∂volume` = `differentialEntropyExt`
の a.c. 枝の正部、`EntropyPowerExt.lean:61`)。

`klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`、`@audit:ok`) と完全同型で、
`klFun`→`negMulLog` 差替のみ (両者 continuous)。骨格 = `lintegral_liminf_le` +
`ENNReal.continuous_ofReal` + `Tendsto.liminf_eq` + `lintegral_mono_ae`。

**proof-done (Phase 3、0 sorry)**: pointwise `F n x → G x` を `Real.continuous_negMulLog` +
`ENNReal.continuous_ofReal` 合成で出し、`Tendsto.liminf_eq.ge` で `G x ≤ liminf (F · x)`、
`lintegral_mono_ae` + Fatou `lintegral_liminf_le` で結論。

honesty 4-check (proof-done): (1) 非循環 — 結論 (正部 lintegral の liminf 下界) は仮説 `h_ae`
(density a.e. 収束) と非同型、body は genuine 全証明。(2) 非バンドル — `h_ae` は a.e. 収束 input
precondition、Fatou 不等式の核を encode せず。(3) 非退化 — `:True` slot なし。(4) sufficiency —
Fatou (`lintegral_liminf_le`、非負被積分関数列で `∫ liminf ≤ liminf ∫`) が正しい向き: `ofReal(negMulLog
...)` で負部を 0 clamp した正部 A に対し成立する向きで、収束列の極限 = liminf を使う
(`klDiv_le_liminf_of_ae_tendsto` body と同構造)。`klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`)
と **別物** (参照測度 γ 有限 vs volume 無限、klFun vs negMulLog) ゆえ集約漏れでない。
@audit:ok -/
theorem differentialEntropyExt_posPart_le_liminf_of_ae_tendsto
    (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ)
    (h_ae : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => ((μ_n n).rnDeriv volume x).toReal) atTop
        (𝓝 ((μ.rnDeriv volume x).toReal))) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
      ≤ Filter.liminf
          (fun n => ∫⁻ x, ENNReal.ofReal
            (Real.negMulLog (((μ_n n).rnDeriv volume x).toReal)) ∂volume) atTop := by
  classical
  -- Abbreviate the ℝ≥0∞ integrands.
  set F : ℕ → ℝ → ℝ≥0∞ :=
    fun n x => ENNReal.ofReal (Real.negMulLog (((μ_n n).rnDeriv volume x).toReal)) with hF
  set G : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) with hG
  -- Each `F n` is measurable.
  have hF_meas : ∀ n, Measurable (F n) := by
    intro n
    exact (Real.continuous_negMulLog.measurable.comp
      ((μ_n n).measurable_rnDeriv volume).ennreal_toReal).ennreal_ofReal
  -- Pointwise: `G x ≤ liminf (fun n => F n x)`, a.e.
  have hpt : ∀ᵐ x ∂(volume : Measure ℝ), G x ≤ Filter.liminf (fun n => F n x) atTop := by
    filter_upwards [h_ae] with x hx
    -- `F n x → G x` by continuity of `negMulLog` and `ENNReal.ofReal`.
    have htend : Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
      have hk : Tendsto (fun n => Real.negMulLog (((μ_n n).rnDeriv volume x).toReal)) atTop
          (𝓝 (Real.negMulLog ((μ.rnDeriv volume x).toReal))) :=
        (Real.continuous_negMulLog.tendsto _).comp hx
      exact (ENNReal.continuous_ofReal.tendsto _).comp hk
    exact htend.liminf_eq.ge
  -- Fatou + the pointwise lower bound.
  calc ∫⁻ x, G x ∂(volume : Measure ℝ)
      ≤ ∫⁻ x, Filter.liminf (fun n => F n x) atTop ∂volume := lintegral_mono_ae hpt
    _ ≤ Filter.liminf (fun n => ∫⁻ x, F n x ∂volume) atTop := lintegral_liminf_le hF_meas

/-- **finite-entropy 単調性 (truncation 不要、un-truncated)**: `W` a.c. ∧ `W ⊥ V` ∧ `h(W)` の負部
有限 (`Integrable (negMulLog ((Q.map W).rnDeriv vol ·).toReal)`、= 有限微分エントロピー) のとき
`h(W) ≤ h(W+V)`。per-fibre translate Gibbs で建て、`ν = W+V` の有限性で場合分け (有限枝 = 実数 Gibbs、
⊤ 枝 = `le_top`)。**truncation を要求しない**ので un-truncated `W` に直接適用できる
(`differentialEntropyExt_mono_add_truncW` の core を `Q : Measure Ω` 一般で抽出したもの)。

`differentialEntropyExt_mono_add_truncW` は本補題に `Q := truncW P W n` を渡し、preamble
(条件付けでの a.c. / 独立 / 有限エントロピー保存) を供給する系として書ける。core は truncation
を一切使わず、compact support が core に供給していた唯一の入力 = `Q.map W` の有限エントロピー
`hW_ent` を仮説として受ける。

**仮説は全て regularity (非 load-bearing)**: `hW`/`hV`/`hWV`/`hW_ac` は可測/独立/絶対連続、
`hW_ent` (= `Q.map W` の有限微分エントロピー) は ⊤ 枝の `⊤-⊤` 不定形回避用の有限性 precondition
(grant しても単調性は出ない = 非 load-bearing)。単調性の核は body の per-fibre translate Gibbs
(`differentialEntropy_le_cross_entropy` 経由) + Tonelli collapse で body が担い、仮説に encode しない。

proof-done (0 sorry / 0 @residual)。`#print axioms` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free、`differentialEntropyExt_mono_add_truncW` の core を抽出したものなので transitive も同等)。
@audit:ok -/
theorem differentialEntropyExt_mono_add_of_integrable
    (W V : Ω → ℝ) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V Q)
    (hW_ac : (Q.map W) ≪ volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((Q.map W).rnDeriv volume x).toReal) volume) :
    differentialEntropyExt (Q.map W)
      ≤ differentialEntropyExt (Q.map (fun ω => W ω + V ω)) := by
  -- **Local aliases matching the transplanted core's names.**
  have hW_ac_Q : (Q.map W) ≪ volume := hW_ac
  have hindep : IndepFun W V Q := hWV
  -- Probability-measure instances on the relevant marginals.
  haveI hWmap_prob : IsProbabilityMeasure (Q.map W) :=
    Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hVmap_prob : IsProbabilityMeasure (Q.map V) :=
    Measure.isProbabilityMeasure_map hV.aemeasurable
  -- The sum law equals the convolution of the W- and V-marginals (independence).
  have hsum_conv : Q.map (fun ω => W ω + V ω) = (Q.map W) ∗ (Q.map V) := by
    have := hindep.map_add_eq_map_conv_map hW hV
    simpa [Pi.add_apply] using this
  -- W + V is a.c. under `Q` (`hW_ac_Q` + independence).
  have hWV_ac_Q : (Q.map (fun ω => W ω + V ω)) ≪ volume :=
    map_add_absolutelyContinuous W V Q hW hV hindep hW_ac_Q
  -- Full differential-entropy integrability of `Q.map W` is exactly the hypothesis `hW_ent`.
  have hW_ent_Q : Integrable
      (fun x => Real.negMulLog ((Q.map W).rnDeriv volume x).toReal) volume := hW_ent
  -- **negative-part lintegral `B(W) < ⊤`** from the integrability `hW_ent`
  -- (`∫⁻ ofReal(-(negMulLog f)) ≤ ∫⁻ ‖negMulLog f‖ₑ < ⊤`).
  have hBn_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hW_ent.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_trans (neg_le_abs _) (le_refl _))
  -- ↓↓↓ **core, transplanted verbatim from `differentialEntropyExt_mono_add_truncW`** ↓↓↓
  -- abbreviations for the sum law `ν := Q.map (W+V) = (Q.map W) ∗ (Q.map V)` and its density.
  set ν : Measure ℝ := Q.map (fun ω => W ω + V ω) with hν_def
  set rfun : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal with hrfun_def
  -- **`B(ν) < ⊤`** (sum-marginal negative-part), via the single-component helper
  -- `negPart_negMulLog_conv_single_ne_top` averaging over the probability measure `Q.map V`
  -- (no a.c. on `V` needed).  `B(Q.map W) < ⊤` is `hBn_fin`.
  have hBn_fin' :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤ := hBn_fin
  have hν_conv : ν = (Q.map W) ∗ (Q.map V) := hsum_conv
  have hBnu_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (rfun x))) ∂volume) ≠ ⊤ := by
    have hconv_fin := negPart_negMulLog_conv_single_ne_top (Q.map W) (Q.map V) hW_ac_Q hBn_fin'
    rw [hrfun_def, hν_conv]; exact hconv_fin
  -- **Case split on whether the sum entropy integrand is integrable.**
  by_cases hent_sum : Integrable (fun x => Real.negMulLog (rfun x)) volume
  · -- **Case B (finite branch)**: descend to the workhorse `differentialEntropy` and prove the
    -- real inequality `h(Q.map W) ≤ h(ν)` via per-fibre translate Gibbs.
    have hν_ac : ν ≪ volume := hWV_ac_Q
    have hent_sum' : Integrable
        (fun x => Real.negMulLog ((ν.rnDeriv volume x).toReal)) volume := hent_sum
    rw [differentialEntropyExt_of_ac_integrable hν_ac hent_sum',
      differentialEntropyExt_of_ac_integrable hW_ac_Q hW_ent_Q]
    refine EReal.coe_le_coe_iff.mpr ?_
    -- **per-fibre translate Gibbs**.  Set `μWz z := (Q.map W).map (·+z)` (the per-fibre conditional
    -- law of `W+V` given `V=z`, by independence).  Each `μWz z ≪ ν` (a.e. z), so per-fibre Gibbs gives
    -- `h(μWz z) ≤ -∫ x, log(r x) ∂(μWz z)`, and translation invariance gives `h(μWz z) = h(Q.map W)`.
    -- Integrating over `μV` and collapsing the RHS by Tonelli (`r(x) = ∫ fW(x-z) ∂μV`) yields `h(ν)`.
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν_def]; exact Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
    set μV : Measure ℝ := Q.map V with hμV_def
    set fW : ℝ → ℝ := fun x => ((Q.map W).rnDeriv volume x).toReal with hfWb_def
    -- the per-fibre translated measure.
    set μWz : ℝ → Measure ℝ := fun z => (Q.map W).map (fun x => x + z) with hμWz_def
    -- (a) per-fibre a.c. `μWz z ≪ ν`  (a.e. z ∂μV).
    have hμWz_ac_ν : ∀ᵐ z ∂μV, μWz z ≪ ν := by
      have hper := condDistrib_ae_absolutelyContinuous_indep_add
        (μW := Q.map W) (μV := Q.map V) hW_ac_Q
      filter_upwards [hper] with z hz
      show (Q.map W).map (fun x => x + z) ≪ ν
      rw [hν_conv]; exact hz
    -- (b) per-fibre a.c. `μWz z ≪ volume`  (translation invariance).
    have hμWz_ac_vol : ∀ z, μWz z ≪ volume := by
      intro z
      show (Q.map W).map (fun x => x + z) ≪ volume
      have hshift : Measurable fun x : ℝ => x + z := by fun_prop
      have h_map_vol : (volume : Measure ℝ).map (fun x : ℝ => x + z) = volume :=
        MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) z
      have := hW_ac_Q.map hshift
      rwa [h_map_vol] at this
    haveI hμWz_prob : ∀ z, IsProbabilityMeasure (μWz z) := by
      intro z
      show IsProbabilityMeasure ((Q.map W).map (fun x => x + z))
      exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable fun x : ℝ => x + z).aemeasurable
    -- (c) per-fibre finite entropy.
    have hμWz_ent : ∀ z, Integrable
        (fun x => Real.negMulLog ((μWz z).rnDeriv volume x).toReal) volume := by
      intro z
      show Integrable (fun x => Real.negMulLog
        (((Q.map W).map (fun x => x + z)).rnDeriv volume x).toReal) volume
      exact integrable_negMulLog_rnDeriv_map_add_const (ν := Q.map W) z hW_ent_Q
    -- **Foundational identities for the Tonelli collapse.**
    set fWe : ℝ → ℝ≥0∞ := (Q.map W).rnDeriv volume with hfWeb_def
    have hfWe_meas : Measurable fWe := Measure.measurable_rnDeriv _ _
    have hfW_meas : Measurable fW := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hfW_nn : ∀ x, 0 ≤ fW x := fun _ => ENNReal.toReal_nonneg
    have hr_nn : ∀ x, 0 ≤ rfun x := fun _ => ENNReal.toReal_nonneg
    have hlog_meas : Measurable (fun x => Real.log (rfun x)) :=
      Real.measurable_log.comp ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
    -- `μWz z = vol.withDensity (fun x => fWe (x - z))`  (translate of an a.c. measure as withDensity).
    have hμWz_wd : ∀ z, μWz z = (volume : Measure ℝ).withDensity (fun x => fWe (x - z)) := by
      intro z
      show (Q.map W).map (fun x => x + z) = _
      conv_lhs => rw [show (Q.map W) = (volume : Measure ℝ).withDensity fWe from
        (Measure.withDensity_rnDeriv_eq (Q.map W) volume hW_ac_Q).symm]
      rw [map_add_const_withDensity fWe z]
    -- a.e.-finiteness of the translated density `x ↦ fWe (x - z)`  (Lebesgue translation invariance).
    have hfWe_translate_fin : ∀ z, ∀ᵐ x ∂volume, fWe (x - z) < ∞ := by
      intro z
      have h0 : ∀ᵐ x ∂volume, fWe x < ∞ := Measure.rnDeriv_lt_top (Q.map W) volume
      have hmp : MeasurePreserving (fun x : ℝ => x - z) volume volume :=
        ⟨by fun_prop, MeasureTheory.map_sub_right_eq_self (μ := (volume : Measure ℝ)) z⟩
      exact hmp.quasiMeasurePreserving.ae h0
    -- **inner integral identity**: `∫ x, g x ∂(μWz z) = ∫ x, fW (x - z) * g x ∂volume`.
    have hinner : ∀ (z : ℝ) (g : ℝ → ℝ),
        ∫ x, g x ∂(μWz z) = ∫ x, fW (x - z) * g x ∂volume := by
      intro z g
      rw [hμWz_wd z, integral_withDensity_eq_integral_toReal_smul
        (by fun_prop : Measurable fun x => fWe (x - z)) (hfWe_translate_fin z)]
      apply integral_congr_ae; filter_upwards with x
      show ((fWe (x - z)).toReal) • g x = fW (x - z) * g x
      rw [smul_eq_mul]
    -- **convergence density**: `rfun =ᵐ[vol] fun x => ∫ z, fW (x - z) ∂μV`.
    have hr_avg : rfun =ᵐ[volume] fun x => ∫ z, fW (x - z) ∂μV := by
      have hconv : ν = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, fWe (z - v) ∂μV) := by
        rw [hν_conv]; exact conv_eq_withDensity_translate_average (Q.map W) (Q.map V) hW_ac_Q
      have hrho_meas : Measurable (fun z => ∫⁻ v, fWe (z - v) ∂μV) :=
        (hfWe_meas.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
      have h_rn : ν.rnDeriv volume =ᵐ[volume] fun z => ∫⁻ v, fWe (z - v) ∂μV := by
        rw [hconv]; exact Measure.rnDeriv_withDensity volume hrho_meas
      have h_lt : ∀ᵐ z ∂volume, ν.rnDeriv volume z < ∞ := Measure.rnDeriv_lt_top ν volume
      filter_upwards [h_rn, h_lt] with x hx hx_lt
      show (ν.rnDeriv volume x).toReal = ∫ z, fW (x - z) ∂μV
      have hfWe_x_meas : Measurable (fun z => fWe (x - z)) := by fun_prop
      have hint_lt : (∫⁻ z, fWe (x - z) ∂μV) < ∞ := hx ▸ hx_lt
      have hae_lt : ∀ᵐ z ∂μV, fWe (x - z) < ∞ :=
        ae_lt_top' hfWe_x_meas.aemeasurable hint_lt.ne
      rw [hx]; exact (integral_toReal hfWe_x_meas.aemeasurable hae_lt).symm
    -- **global product integrability** of `K (z, x) = fW (x - z) * log (rfun x)` over `μV.prod vol`.
    -- The absolute kernel `fW (x-z) * |log (rfun x)|` integrates (Tonelli, nonneg) to
    -- `∫ x, rfun x * |log r| = ∫ |negMulLog r| < ∞` (`hent_sum`).
    have habs_eq : ∀ x, rfun x * |Real.log (rfun x)| = |Real.negMulLog (rfun x)| := by
      intro x
      rw [Real.negMulLog, neg_mul, abs_neg, abs_mul, abs_of_nonneg (hr_nn x)]
    -- `∫⁻ z, ofReal (fW (x-z)) ∂μV = ofReal (rfun x)`  (a.e. x): the ENNReal convolution density.
    have hsumdens : ν.rnDeriv volume =ᵐ[volume] fun z => ∫⁻ v, fWe (z - v) ∂μV := by
      have hconv : ν = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, fWe (z - v) ∂μV) := by
        rw [hν_conv]; exact conv_eq_withDensity_translate_average (Q.map W) (Q.map V) hW_ac_Q
      rw [hconv]
      exact Measure.rnDeriv_withDensity volume
        ((hfWe_meas.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right')
    have hofReal_fW : ∀ᵐ x ∂volume,
        (∫⁻ z, ENNReal.ofReal (fW (x - z)) ∂μV) = ENNReal.ofReal (rfun x) := by
      have h_lt : ∀ᵐ z ∂volume, ν.rnDeriv volume z < ∞ := Measure.rnDeriv_lt_top ν volume
      filter_upwards [hsumdens, h_lt] with x hx hx_lt
      have hae_fin : ∀ᵐ z ∂μV, fWe (x - z) < ∞ :=
        ae_lt_top' (by fun_prop : Measurable fun z => fWe (x - z)).aemeasurable (hx ▸ hx_lt).ne
      calc (∫⁻ z, ENNReal.ofReal (fW (x - z)) ∂μV)
          = ∫⁻ z, fWe (x - z) ∂μV := by
            apply lintegral_congr_ae; filter_upwards [hae_fin] with z hz
            show ENNReal.ofReal ((fWe (x - z)).toReal) = fWe (x - z)
            exact ENNReal.ofReal_toReal hz.ne
        _ = ENNReal.ofReal (rfun x) := by
            rw [hrfun_def]; simp only
            rw [ENNReal.ofReal_toReal (by rw [hx]; exact (hx ▸ hx_lt).ne), hx]
    have hglob_abs_lint : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (fW (p.2 - p.1) * |Real.log (rfun p.2)|)
        ∂(μV.prod volume) ≠ ⊤ := by
      have hker_meas : Measurable (fun p : ℝ × ℝ =>
          ENNReal.ofReal (fW (p.2 - p.1) * |Real.log (rfun p.2)|)) :=
        ((hfW_meas.comp (measurable_snd.sub measurable_fst)).mul
          (hlog_meas.comp measurable_snd).abs).ennreal_ofReal
      rw [lintegral_prod _ hker_meas.aemeasurable,
        lintegral_lintegral_swap hker_meas.aemeasurable]
      have hbody : (∫⁻ x, ∫⁻ z, ENNReal.ofReal (fW (x - z) * |Real.log (rfun x)|) ∂μV ∂volume)
          = ∫⁻ x, ENNReal.ofReal (rfun x * |Real.log (rfun x)|) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [hofReal_fW] with x hx
        calc (∫⁻ z, ENNReal.ofReal (fW (x - z) * |Real.log (rfun x)|) ∂μV)
            = ENNReal.ofReal (|Real.log (rfun x)|) * ∫⁻ z, ENNReal.ofReal (fW (x - z)) ∂μV := by
              rw [← lintegral_const_mul _
                ((by fun_prop : Measurable fun z => fW (x - z)).ennreal_ofReal)]
              apply lintegral_congr; intro z
              rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm (fW (x - z))]
          _ = ENNReal.ofReal (|Real.log (rfun x)|) * ENNReal.ofReal (rfun x) := by rw [hx]
          _ = ENNReal.ofReal (rfun x * |Real.log (rfun x)|) := by
              rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
      rw [hbody]
      -- `∫⁻ ofReal(rfun x * |log r|) = ∫⁻ ofReal(|negMulLog r|) = ∫⁻ ‖negMulLog r‖ₑ < ∞`.
      have hfin : (∫⁻ x, ‖Real.negMulLog (rfun x)‖ₑ ∂volume) ≠ ⊤ :=
        hent_sum.hasFiniteIntegral.ne
      refine ne_top_of_le_ne_top hfin (lintegral_mono (fun x => ?_))
      rw [habs_eq x, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    -- the kernel `K (z, x) = fW (x - z) * log (rfun x)` is product-integrable (abs-dominated).
    have hKmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => fW (p.2 - p.1) * Real.log (rfun p.2)) (μV.prod volume) :=
      ((hfW_meas.comp (measurable_snd.sub measurable_fst)).mul
        (hlog_meas.comp measurable_snd)).aestronglyMeasurable
    have hKint : Integrable
        (fun p : ℝ × ℝ => fW (p.2 - p.1) * Real.log (rfun p.2)) (μV.prod volume) := by
      refine ⟨hKmeas, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have henorm_eq : (∫⁻ p : ℝ × ℝ, ‖fW (p.2 - p.1) * Real.log (rfun p.2)‖ₑ ∂(μV.prod volume))
          = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (fW (p.2 - p.1) * |Real.log (rfun p.2)|)
            ∂(μV.prod volume) := by
        apply lintegral_congr; intro p
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfW_nn _)]
      rw [henorm_eq]
      exact lt_of_le_of_ne le_top hglob_abs_lint
    -- (d) per-fibre cross-integrability `Integrable (log r) (μWz z)`  (a.e. z), from the per-z
    -- section of the global product-integrable kernel `hKint`.
    have hcross_int : ∀ᵐ z ∂μV, Integrable
        (fun x => Real.log (rfun x)) (μWz z) := by
      filter_upwards [hKint.prod_right_ae] with z hz_sec
      -- `hz_sec : Integrable (fun x => fW (x - z) * log (rfun x)) volume`.
      rw [hμWz_wd z, integrable_withDensity_iff_integrable_smul'
        (by fun_prop : Measurable fun x => fWe (x - z)) (hfWe_translate_fin z)]
      refine hz_sec.congr ?_
      filter_upwards with x
      show fW (x - z) * Real.log (rfun x) = (fWe (x - z)).toReal • Real.log (rfun x)
      rw [smul_eq_mul]
    -- (e) per-fibre Gibbs:  `h(μWz z) ≤ -∫ x, log(r x) ∂(μWz z)`  (a.e. z).
    have hgibbs : ∀ᵐ z ∂μV,
        differentialEntropy (μWz z) ≤ - ∫ x, Real.log (rfun x) ∂(μWz z) := by
      filter_upwards [hμWz_ac_ν, hcross_int] with z hz_ac hz_cross
      exact EPIInfiniteVarianceTruncation.differentialEntropy_le_cross_entropy
        (hμWz_ac_vol z) hν_ac hz_ac (hμWz_ent z) hz_cross
    -- (f) translation invariance:  `h(μWz z) = h(Q.map W)`.
    have htrans_ent : ∀ z, differentialEntropy (μWz z) = differentialEntropy (Q.map W) := by
      intro z
      show differentialEntropy ((Q.map W).map (fun x => x + z)) = differentialEntropy (Q.map W)
      exact differentialEntropy_map_add_const hW_ac_Q z
    -- (g) the cross-entropy term collapses (after integration over μV) to `-h(ν)`.
    -- the μV-integrability of `z ↦ -∫ x, log(r x) ∂(μWz z)` (for `integral_mono_ae`).
    have hRHS_int : Integrable (fun z => - ∫ x, Real.log (rfun x) ∂(μWz z)) μV := by
      have hbase : Integrable
          (fun z => ∫ x, fW (x - z) * Real.log (rfun x) ∂volume) μV :=
        hKint.integral_prod_left
      refine (hbase.neg).congr ?_
      filter_upwards with z
      show -∫ x, fW (x - z) * Real.log (rfun x) ∂volume
        = -∫ x, Real.log (rfun x) ∂(μWz z)
      rw [hinner z (fun x => Real.log (rfun x))]
    -- (h) `∫ z, (-∫ x, log(r x) ∂(μWz z)) ∂μV = - ∫ x, r x · log(r x) ∂volume = h(ν)`.
    have hRHS_eq : (∫ z, (- ∫ x, Real.log (rfun x) ∂(μWz z)) ∂μV)
        = differentialEntropy ν := by
      -- rewrite each inner via `hinner`, pull out the sign, Fubini-swap, collapse the inner z-integral.
      have hstep1 : (∫ z, (- ∫ x, Real.log (rfun x) ∂(μWz z)) ∂μV)
          = - ∫ z, (∫ x, fW (x - z) * Real.log (rfun x) ∂volume) ∂μV := by
        rw [← integral_neg]
        apply integral_congr_ae; filter_upwards with z
        rw [hinner z (fun x => Real.log (rfun x))]
      -- Fubini swap `∫ z ∫ x = ∫ x ∫ z`  (kernel `hKint` over `μV.prod vol`).
      have hswap : (∫ z, (∫ x, fW (x - z) * Real.log (rfun x) ∂volume) ∂μV)
          = ∫ x, (∫ z, fW (x - z) * Real.log (rfun x) ∂μV) ∂volume :=
        integral_integral_swap (f := fun z x => fW (x - z) * Real.log (rfun x)) hKint
      -- inner `∫ z, fW(x-z)·log(r x) ∂μV = (∫ z, fW(x-z) ∂μV)·log(r x) = rfun x · log(rfun x)` a.e.
      have hcollapse : (∫ x, (∫ z, fW (x - z) * Real.log (rfun x) ∂μV) ∂volume)
          = ∫ x, rfun x * Real.log (rfun x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hr_avg] with x hx
        rw [integral_mul_const, ← hx]
      -- `differentialEntropy ν = ∫ negMulLog r = -∫ r·log r`.
      have hent_eq : differentialEntropy ν = - ∫ x, rfun x * Real.log (rfun x) ∂volume := by
        rw [differentialEntropy, ← integral_neg]
        apply integral_congr_ae; filter_upwards with x
        show Real.negMulLog ((ν.rnDeriv volume x).toReal) = -(rfun x * Real.log (rfun x))
        rw [Real.negMulLog]; ring
      rw [hstep1, hswap, hcollapse, hent_eq]
    -- assemble:  `h(Q.map W) = ∫ z, h(Q.map W) ∂μV ≤ ∫ z, (-∫ log r ∂μWz) ∂μV = h(ν)`.
    calc differentialEntropy (Q.map W)
        = ∫ _z, differentialEntropy (Q.map W) ∂μV := by
          rw [integral_const, probReal_univ, one_smul]
      _ ≤ ∫ z, (- ∫ x, Real.log (rfun x) ∂(μWz z)) ∂μV := by
          apply integral_mono_ae (integrable_const _) hRHS_int
          filter_upwards [hgibbs] with z hz
          calc differentialEntropy (Q.map W) = differentialEntropy (μWz z) := (htrans_ent z).symm
            _ ≤ _ := hz
      _ = differentialEntropy ν := hRHS_eq
  · -- **Case A (infinite branch)**: `¬ hent_sum` and `B(ν) < ⊤` ⟹ `A(ν) = ⊤` ⟹
    -- `differentialEntropyExt ν = ⊤`, then `h(Q.map W) ≤ ⊤` by `le_top`.
    set g : ℝ → ℝ := fun x => Real.negMulLog (rfun x) with hg_def
    have hg_meas : Measurable g :=
      Real.continuous_negMulLog.measurable.comp
        ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
    set Aint : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (g x) ∂volume with hA_def
    set Bint : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume with hB_def
    have hB_lt_top : Bint ≠ ⊤ := by rw [hB_def]; exact hBnu_fin
    have hA_top : Aint = ⊤ := by
      have hnotfin : ¬ HasFiniteIntegral g volume := fun hfin =>
        hent_sum ⟨hg_meas.aestronglyMeasurable, hfin⟩
      have henorm_top : (∫⁻ x, ‖g x‖ₑ ∂volume) = ⊤ := by
        by_contra h
        exact hnotfin (hasFiniteIntegral_iff_enorm.mpr (lt_of_le_of_ne le_top h))
      have hsplit : (∫⁻ x, ‖g x‖ₑ ∂volume) = Aint + Bint := by
        rw [hA_def, hB_def, ← lintegral_add_left
          (Measurable.ennreal_ofReal hg_meas) (fun x => ENNReal.ofReal (-(g x)))]
        apply lintegral_congr; intro x
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        rcases le_or_gt 0 (g x) with h | h
        · have hneg : ENNReal.ofReal (-(g x)) = 0 :=
            ENNReal.ofReal_of_nonpos (by linarith)
          rw [abs_of_nonneg h, hneg, add_zero]
        · have hpos : ENNReal.ofReal (g x) = 0 :=
            ENNReal.ofReal_of_nonpos h.le
          rw [abs_of_neg h, hpos, zero_add]
      rw [hsplit] at henorm_top
      by_contra hA
      exact (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hA, lt_of_le_of_ne le_top hB_lt_top⟩).ne
        henorm_top
    have hdiff_top : differentialEntropyExt ν = ⊤ := by
      rw [differentialEntropyExt_of_ac hWV_ac_Q]
      show ((Aint : EReal) - (Bint : EReal)) = ⊤
      rw [hA_def, hB_def, ← hg_def] at *
      rw [hA_top, EReal.coe_ennreal_top]
      exact EReal.top_sub (by
        rw [Ne, EReal.coe_ennreal_eq_top_iff]; exact hB_lt_top)
    rw [hdiff_top]; exact le_top

/-- **per-n 単調性** (proof-done, 0 sorry): 各 n で `h(W_n) ≤ h(W_n + V)`、`W_n := truncW P W n`
(= `P` を W-事象 `{|W| ≤ n}` で条件付けた compact-support 近似)。

**route (core を `differentialEntropyExt_mono_add_of_integrable` に抽出)**: 旧版は finite ② chain rule
`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite` を `X:=W+V, Z:=V` で適用していたが、
その 11 regularity 仮説のうち `hκ_dens_meas` (joint 密度可測) が Mathlib 不在の真 gap だった。
本版は **chain rule を完全に捨て**、fibre を抽象 condDistrib でなく **explicit な平行移動
`(Q.map W).map(·+z)`** として扱う per-fibre translate Gibbs に置き換える。

**2026-06-08 refactor**: per-fibre translate Gibbs core を **truncation 非依存の一般化補題
`differentialEntropyExt_mono_add_of_integrable`** (`Q : Measure Ω` 一般、`hW_ent` = `Q.map W` の有限
微分エントロピーを仮説に取る) に抽出した。本補題は `Q := truncW P W n` を渡し、preamble で truncation
固有の regularity (条件付けでの a.c. 保存 `hW_ac_Q` / 独立保存 `hindep` / compact-support による有限
エントロピー `hW_ent_Q`) を供給して、core 一般化補題を呼ぶ系として書ける。core が truncation から受けて
いた唯一の入力は `hW_ent_Q` (W-marginal の有限エントロピー) ただ一つで、その他 (Tonelli collapse / 平行
移動 identities / 畳み込み密度) は任意 a.c. 確率測度で動くため、un-truncated `W` への直接適用も可能。

**preamble の構成**: `Q := truncW P W n`、`hindep` (W ⊥ V は W-事象条件付けで保存) / `hW_ac_Q`
(cond の a.c. 保存) / `hW_ent_Q` (compact-support `Sn = {|W|≤n}` ⟹ 密度 `c⁻¹·1_Sn·fW` の正部 `A<⊤`
+ 負部 `B<⊤` = `hW_negPart_fin` から、両部有限 ⟹ integrable)。これらを揃えて
`differentialEntropyExt_mono_add_of_integrable W V Q hW hV hindep hW_ac_Q hW_ent_Q` で結論。

**仮説は全て regularity (非 load-bearing)**: `hW`/`hV`/`hWV`/`hW_ac` は可測/独立/絶対連続、
`hW_negPart_fin` (= `B(W) < ⊤`) は h(W) 負部有限性、`hn` (positive mass) は cond well-defined の scope。
単調性の核は一般化補題 body の per-fibre Gibbs + Tonelli が担い、仮説に encode しない。`#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free、要 olean refresh で確認)。
@audit:ok -/
theorem differentialEntropyExt_mono_add_truncW
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (n : ℕ) (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    differentialEntropyExt ((truncW P W n).map W)
      ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
  -- The truncated measure `Q := truncW P W n = P[| {|W| ≤ n}]` is a probability measure.
  set Q : Measure Ω := truncW P W n with hQ_def
  haveI hQ_prob : IsProbabilityMeasure Q := by
    rw [hQ_def, truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
  -- W stays a.c. under conditioning: `Q.map W ≪ P.map W ≪ volume`.
  have hW_ac_Q : (Q.map W) ≪ volume := by
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [hQ_def, truncW]
    exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- W ⊥ V is preserved under conditioning on a W-event `{|W| ≤ n}` (the event is a function of
  -- W only, so V is unaffected). Self-built from `indepFun_iff_measure_inter_preimage_eq_mul`:
  -- the conditioning event `E = W⁻¹' {r | |r| ≤ n}` absorbs into the W-preimage, and `hWV`
  -- factors the joint measure of W- and V-preimages.
  have hE_meas : MeasurableSet {ω : Ω | |W ω| ≤ (n : ℝ)} :=
    hW.abs measurableSet_Iic
  set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
  have hindep : IndepFun W V Q := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    -- `E ∩ W⁻¹' s = W⁻¹' (Icc⁻¹ ∩ s)` is itself a W-preimage of a measurable set.
    have hEW : E ∩ W ⁻¹' s = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := by
      ext ω; simp [hE_def, Set.mem_inter_iff, and_comm]
    have hIcc_meas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      (_root_.continuous_abs.measurable measurableSet_Iic)
    have hAW : MeasurableSet ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := hIcc_meas.inter hs
    -- Expand each `cond` term via `cond_apply hE_meas`.
    rw [hQ_def, truncW, cond_apply hE_meas, cond_apply hE_meas, cond_apply hE_meas]
    -- The joint preimage: `E ∩ (W⁻¹s ∩ V⁻¹t) = (E ∩ W⁻¹s) ∩ V⁻¹t = W⁻¹(..) ∩ V⁻¹t`.
    have hjoint : E ∩ (W ⁻¹' s ∩ V ⁻¹' t) = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t := by
      rw [← Set.inter_assoc, hEW]
    rw [hjoint, hEW]
    -- Factor `P` on the W- and V-preimages via the original independence `hWV`.
    have hfac1 : P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t)
        = P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s)) * P (V ⁻¹' t) :=
      hWV.measure_inter_preimage_eq_mul _ _ hAW ht
    -- For the V-term: `E ∩ V⁻¹t = W⁻¹(Icc) ∩ V⁻¹t`, again factored by `hWV`.
    have hEV : E ∩ V ⁻¹' t = W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} ∩ V ⁻¹' t := by
      ext ω; simp [hE_def]
    have hfac2 : P (E ∩ V ⁻¹' t) = P E * P (V ⁻¹' t) := by
      rw [hEV, hWV.measure_inter_preimage_eq_mul _ _ hIcc_meas ht, hE_def]; rfl
    rw [hfac1, hfac2]
    -- Arithmetic: `c·(a·v) = (c·a)·(c·(P E·v))` where `c = (P E)⁻¹`, since `c·P E = 1`.
    have hPE_ne : P E ≠ 0 := by rw [hE_def]; exact hn
    have hPE_ne_top : P E ≠ ∞ := measure_ne_top P E
    have hcancel : (P E)⁻¹ * (P E * P (V ⁻¹' t)) = P (V ⁻¹' t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hPE_ne hPE_ne_top, one_mul]
    rw [hcancel]
    ring
  -- **Set-up shared by the `≠ ⊥` / entropy blocks**: `Q.map W = cond (P.map W) Sn` (single-variable
  -- truncation), so its density is `c⁻¹ · 1_Sn · f_W` with `c = (P.map W) Sn = P E`.
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  -- `(truncW P W n).map W = cond (P.map W) Sn` (direct: conditioning on `W⁻¹' Sn` then pushing
  -- forward by `W` equals conditioning the law of `W` on `Sn`).
  have hE_eq : E = W ⁻¹' Sn := by ext ω; simp [hE_def, hSn_def]
  have hQW_eq : (Q.map W) = ProbabilityTheory.cond (P.map W) Sn := by
    refine Measure.ext (fun A hA => ?_)
    -- LHS: `(Q.map W) A = Q (W⁻¹A) = (P E)⁻¹ * P (E ∩ W⁻¹A)`.
    have hLHS : (Q.map W) A = (P E)⁻¹ * P (W ⁻¹' Sn ∩ W ⁻¹' A) := by
      rw [Measure.map_apply hW hA, hQ_def, truncW, ← hE_def,
        ProbabilityTheory.cond_apply hE_meas P, hE_eq]
    -- RHS: `cond (P.map W) Sn A = ((P.map W) Sn)⁻¹ * (P.map W)(Sn ∩ A)`.
    have hRHS : (ProbabilityTheory.cond (P.map W) Sn) A
        = (P E)⁻¹ * P (W ⁻¹' Sn ∩ W ⁻¹' A) := by
      rw [ProbabilityTheory.cond_apply hSn_meas (P.map W) A,
        Measure.map_apply hW hSn_meas, Measure.map_apply hW (hSn_meas.inter hA),
        Set.preimage_inter, hE_eq]
    rw [hLHS, hRHS]
  -- positive mass of `Sn` under `P.map W`.
  have hWmap_prob' : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hSn_pos : (P.map W) Sn ≠ 0 := by
    rw [Measure.map_apply hW hSn_meas]
    have : W ⁻¹' Sn = E := by ext ω; simp [hE_def, hSn_def]
    rw [this, hE_def]; exact hn
  -- **density formula for `Q.map W`** (cond density, reusable across the `≠⊥` / entropy blocks).
  set fW : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hfW_def
  set c : ℝ≥0∞ := (P.map W) Sn with hc_def
  have hc_top : c ≠ ∞ := measure_ne_top _ _
  set cbar : ℝ := (c⁻¹).toReal with hcbar_def
  have hcbar_nn : 0 ≤ cbar := ENNReal.toReal_nonneg
  have h_rn : (Q.map W).rnDeriv volume
      =ᵐ[volume] fun x => c⁻¹ * Sn.indicator ((P.map W).rnDeriv volume) x := by
    rw [hQW_eq]; exact rnDeriv_cond_eq (P.map W) hSn_meas hSn_pos
  -- abbreviation: `fn x := ((Q.map W).rnDeriv volume x).toReal` (the truncated density, real).
  set fn : ℝ → ℝ := fun x => ((Q.map W).rnDeriv volume x).toReal with hfn_def
  have hfn_meas : Measurable fn := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  -- `∫⁻ ofReal(fW) = 1` (probability density of `P.map W`).
  have hfW_meas : Measurable (fun x => ENNReal.ofReal (fW x)) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal
  have hfW_lint : (∫⁻ x, ENNReal.ofReal (fW x) ∂volume) = 1 := by
    have hae_eq : (fun x => ENNReal.ofReal (fW x)) =ᵐ[volume] (P.map W).rnDeriv volume := by
      filter_upwards [(P.map W).rnDeriv_ne_top volume] with x hx
      rw [hfW_def]; exact ENNReal.ofReal_toReal hx
    rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hW_ac, measure_univ]
  -- **negative-part lintegral `B(W_n) < ⊤`** (from `hW_negPart_fin = B(W) < ⊤`).
  have hBn_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (fn x))) ∂volume) ≠ ⊤ := by
    -- pointwise `=ᵐ`: `-(negMulLog fn) = 1_Sn · ((cbar log cbar)·fW + cbar·(-(negMulLog fW)))`.
    have h_int_eq : (fun x => ENNReal.ofReal (-(Real.negMulLog (fn x))))
        =ᵐ[volume] fun x => ENNReal.ofReal (Sn.indicator
          (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) := by
      filter_upwards [h_rn] with x hx
      rw [hfn_def]; simp only; rw [hx]
      by_cases hxs : x ∈ Sn
      · rw [Set.indicator_of_mem hxs (f := (P.map W).rnDeriv volume),
          Set.indicator_of_mem hxs
            (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))),
          ENNReal.toReal_mul]
        congr 1
        show -(Real.negMulLog (cbar * fW x)) = cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))
        rw [Real.negMulLog_mul cbar (fW x)]
        ring_nf
        rw [Real.negMulLog]
        ring
      · rw [Set.indicator_of_notMem hxs (f := (P.map W).rnDeriv volume),
          Set.indicator_of_notMem hxs
            (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x))))]
        simp [Real.negMulLog]
    rw [lintegral_congr_ae h_int_eq]
    -- Bound the indicator integrand by two finite-integral pieces.
    have hbound : ∀ x, ENNReal.ofReal (Sn.indicator
          (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x)
        ≤ ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)
          + ENNReal.ofReal cbar * ENNReal.ofReal (-(Real.negMulLog (fW x))) := by
      intro x
      by_cases hxs : x ∈ Sn
      · rw [Set.indicator_of_mem hxs]
        refine le_trans ENNReal.ofReal_add_le ?_
        refine add_le_add ?_ ?_
        · rw [← ENNReal.ofReal_mul (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) ?_)
          have hfW_nn : (0 : ℝ) ≤ fW x := ENNReal.toReal_nonneg
          rw [abs_mul, abs_of_nonneg hfW_nn]
        · rw [← ENNReal.ofReal_mul hcbar_nn]
      · rw [Set.indicator_of_notMem hxs]; simp
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
    have hg1_meas : Measurable
        (fun x => ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)) :=
      measurable_const.mul hfW_meas
    have hnegm_meas : Measurable (fun x => ENNReal.ofReal (-(Real.negMulLog (fW x)))) :=
      ((Real.continuous_negMulLog.measurable.comp
        ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).neg).ennreal_ofReal
    rw [lintegral_add_left hg1_meas]
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · rw [lintegral_const_mul _ hfW_meas, hfW_lint, mul_one]; exact ENNReal.ofReal_ne_top
    · rw [lintegral_const_mul _ hnegm_meas]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW_negPart_fin
  -- **positive-part lintegral `A(W_n) < ⊤`** (compact support: `negMulLog fn ≤ 1` on `Sn`,
  -- `fn = 0` off `Sn`, and `volume Sn < ⊤`).
  have hAn_fin :
      (∫⁻ x, ENNReal.ofReal (Real.negMulLog (fn x)) ∂volume) ≠ ⊤ := by
    -- `ofReal(negMulLog fn) ≤ 1_Sn` pointwise (a.e.), and `∫⁻ 1_Sn = volume Sn < ⊤`.
    have hbound : (fun x => ENNReal.ofReal (Real.negMulLog (fn x)))
        ≤ᵐ[volume] fun x => Sn.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      filter_upwards [h_rn] with x hx
      by_cases hxs : x ∈ Sn
      · rw [Set.indicator_of_mem hxs]
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_one.le
        calc Real.negMulLog (fn x) ≤ 1 - fn x := Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg
          _ ≤ 1 := by have : (0 : ℝ) ≤ fn x := ENNReal.toReal_nonneg; linarith
      · rw [Set.indicator_of_notMem hxs]
        -- off `Sn`, `fn x = 0`, so `negMulLog 0 = 0`, `ofReal 0 = 0`.
        have hfn0 : fn x = 0 := by
          rw [hfn_def]; simp only; rw [hx, Set.indicator_of_notMem hxs]; simp
        rw [hfn0]; simp [Real.negMulLog]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
    rw [lintegral_indicator hSn_meas, setLIntegral_const, one_mul]
    -- `volume Sn < ⊤` since `Sn ⊆ Icc (-n) n` is bounded.
    have hSn_sub : Sn ⊆ Set.Icc (-(n : ℝ)) (n : ℝ) := by
      intro r hr; rw [hSn_def, Set.mem_setOf_eq, abs_le] at hr; exact ⟨hr.1, hr.2⟩
    exact ne_top_of_le_ne_top (measure_Icc_lt_top.ne) (measure_mono hSn_sub)
  -- **full differential-entropy integrability of `Q.map W`** (both parts finite ⟹ integrable).
  have hW_ent_Q : Integrable (fun x => Real.negMulLog (fn x)) volume := by
    refine ⟨(Real.continuous_negMulLog.measurable.comp hfn_meas).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    -- `∫⁻ ofReal‖negMulLog fn‖ = ∫⁻ ofReal(negMulLog fn) + ∫⁻ ofReal(-(negMulLog fn)) = A + B < ∞`.
    have h_abs_eq : (fun x => ENNReal.ofReal ‖Real.negMulLog (fn x)‖)
        = fun x => ENNReal.ofReal (Real.negMulLog (fn x))
          + ENNReal.ofReal (-(Real.negMulLog (fn x))) := by
      funext x
      rw [Real.norm_eq_abs]
      rcases le_total 0 (Real.negMulLog (fn x)) with h | h
      · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -(Real.negMulLog (fn x)) ≤ 0),
          add_zero]
      · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
    have hposm : Measurable (fun x => ENNReal.ofReal (Real.negMulLog (fn x))) :=
      (Real.continuous_negMulLog.measurable.comp hfn_meas).ennreal_ofReal
    rw [h_abs_eq, lintegral_add_left hposm]
    exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hAn_fin, hBn_fin⟩)
  -- **core delegation**: the preamble established `hindep` (W ⊥ V under conditioning) / `hW_ac_Q`
  -- (truncated W-marginal a.c.) / `hW_ent_Q` (its finite differential entropy).  The per-fibre
  -- translate Gibbs core is now the truncation-free lemma
  -- `differentialEntropyExt_mono_add_of_integrable` applied to `Q := truncW P W n`.
  exact differentialEntropyExt_mono_add_of_integrable W V Q hW hV hindep hW_ac_Q hW_ent_Q

end InformationTheory.Shannon
