import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIUncondCondEntropyExt
import InformationTheory.Shannon.EPIUncondMonotone
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
# EPI 無条件化 W-Y2 — route β' (truncation + monotone-limit) skeleton

無限エントロピー a.c. 入力 (`h(W) = ⊤` の a.c.) で gateway 単調性の ⊤ 伝播
`differentialEntropyExt_top_of_indep_add` を **無条件** (整数 truncation 近似経由) で
genuine 着地させるための skeleton。route T (`EPIInfiniteVarianceTruncation` /
`EPIInfiniteVarianceCapstone`、sorryAx-free CLOSED) の機構を `W` 単独 truncation に
読み替えて再利用する。

ターゲットは無条件版② chain rule の等式 (finiteness-free 証明不能確定) でなく、
gateway 単調性の ⊤ 枝不等式 (`h(W) = ⊤ ⟹ h(W+V) = ⊤`)。LSC/liminf は `≤` しか出さないが、
⊤ 枝は `le_top` 一発で閉じるため極限と相性が良い。

route β' Phase 1 skeleton (本 file は signature 確定のみ、本体は Phase 2-4)。

SoT 計画: `docs/shannon/epi-uncond-truncation-lsc-plan.md`
(Parent: `docs/shannon/epi-unconditional-moonshot-plan.md` §S5 W-Y2)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **W 単独 truncation の構成** (route T `condTrunc` を W 単独に読み替え)。
`truncW P W n := P[| {ω | |W ω| ≤ n}]` (`W` の値が `[-n, n]` に入る事象での条件付け)。
各 `truncW P W n` は compact support (有界) → 有限分散・有限エントロピーを満たし、a.c.
(`cond_absolutelyContinuous` 保存) を保つ。route T の joint `truncSet X Y n` と違い W 単独。

独立 honesty audit 2026-06-08 (skeleton Phase 1): `ProbabilityTheory.cond` を直接呼ぶ
genuine def、退化定義悪用なし (cond は well-defined、mass≠0 scope は consumer の `hn`)。
sorry なし・@residual なし。@audit:ok -/
noncomputable def truncW (P : Measure Ω) (W : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P {ω | |W ω| ≤ (n : ℝ)}

/-- **cond density formula** (route T `rnDeriv_cond_eq` を W 単独 truncation 用に再掲、heavy
import 回避のため local 再証明): 確率測度 `μ : Measure ℝ` を可測集合 `s` (positive mass) で
条件付けた測度の Radon-Nikodym 微分は `(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`。
`cond μ s = (μ s)⁻¹ • μ.restrict s` の scalar mul + restrict の rnDeriv (`rnDeriv_smul_left_of_ne_top`
+ `rnDeriv_restrict`、共に Mathlib) で組立。route T と完全同型 (集約漏れでなく import cycle/cost 回避)。
独立 honesty audit 2026-06-08: Mathlib 2 補題の機械的合成、循環/bundling なし。@audit:ok -/
private theorem rnDeriv_cond_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) :
    (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] fun x => (μ s)⁻¹ * s.indicator (μ.rnDeriv volume) x := by
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
truncW sum law. (`hn` は consumer の `cond` well-defined scope を揃えるための regularity precondition で
API 対称用に保持。`P E = 0` でも `cond P E = 0 ≤ anything` ゆえ本 `≤` 方向の proof body では未使用。)

独立 honesty audit 2026-06-08 (route (d'') gateway atom): genuine, Mathlib 機械合成 (cond 展開 +
restrict ≤ self + map 単調 + smul 可換)、結論は測度不等式 (regularity)、循環/bundling なし。@audit:ok -/
private theorem map_truncW_add_le_smul_map_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (n : ℕ)
    (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    (truncW P W n).map (fun ω => W ω + V ω)
      ≤ (P {ω | |W ω| ≤ (n : ℝ)})⁻¹ • P.map (fun ω => W ω + V ω) := by
  set g : Ω → ℝ := fun ω => W ω + V ω with hg_def
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

独立 honesty audit 2026-06-08 (route (d'') gateway atom): genuine, 先行 `≤` lemma の機械的帰結、
結論は絶対連続性 (regularity)、循環/bundling なし。@audit:ok -/
private theorem map_truncW_add_absolutelyContinuous_map_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (n : ℕ)
    (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    (truncW P W n).map (fun ω => W ω + V ω) ≪ P.map (fun ω => W ω + V ω) := by
  exact Measure.absolutelyContinuous_of_le_smul
    (map_truncW_add_le_smul_map_add W V P hW hV n hn)

/-! ### route (d'') atom 2 — finiteness-free ℝ≥0∞ cross-entropy (Gibbs)

route (d'') の load-bearing piece。⊤ を跨ぐ Gibbs 不等式 `h(μ) ≤ crossEnt(μ,ν)` を、in-tree の
ℝ-valued `differentialEntropy_le_cross_entropy` (`EPIInfiniteVarianceTruncation.lean:997`、
`integral_sub` で有限 cross-integral + μ 自身の有限微分エントロピーを必須にし ⊤ で破綻) でなく、
**有限性を要求しない ℝ≥0∞ lintegral 形** で建てる。

cross-entropy の正部・負部 (ℝ≥0∞):
* `crossPos μ ν := ∫⁻ x, ofReal (-log fν x) ∂μ` (= `∫ (-log fν)⁺ dμ`、ofReal が負部を 0 clamp)
* `crossNeg μ ν := ∫⁻ x, ofReal (log fν x) ∂μ`  (= `∫ (log fν)⁺ dμ`)

ただし `fν x := (ν.rnDeriv volume x).toReal`。`crossEnt(μ,ν) = -∫ log fν ∂μ = crossPos - crossNeg`
(ℝ で書くと subtraction、ℝ≥0∞ では ⊤-⊤ 回避のため移項形で扱う)。 -/

/-- **cross-entropy 正部** (ℝ≥0∞): `∫⁻ x, ofReal (-log ((ν.rnDeriv volume x).toReal)) ∂μ`。
`ν` の対数密度の **負値部** を `μ` で積分 (ofReal が負部 = `log fν < 0` のとき 0 clamp ⟹
正の寄与のみ拾う)。`A(μ) = crossPos μ μ` (self-identity helper `crossPos_self`)。 -/
noncomputable def crossPos (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂μ

/-- **cross-entropy 負部** (ℝ≥0∞): `∫⁻ x, ofReal (log ((ν.rnDeriv volume x).toReal)) ∂μ`。
`ν` の対数密度の **正値部** を `μ` で積分。`B(μ) = crossNeg μ μ` (self-identity helper `crossNeg_self`)。 -/
noncomputable def crossNeg (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂μ

/-- **self-identity (正部)**: `ν` を自分自身に対する cross-entropy 正部が `differentialEntropyExt`
a.c. 枝の正部 `A(ν)` (`EntropyPowerExt.lean:61`) に一致。
`crossPos ν ν = ∫⁻ ofReal(-log fν) ∂ν = ∫⁻ (ν.rnDeriv vol)·ofReal(-log fν) ∂vol`
(change-of-measure `lintegral_rnDeriv_mul`) `= ∫⁻ ofReal(negMulLog fν) ∂vol = A(ν)`
(a.e. `ν.rnDeriv vol = ofReal fν` + `ofReal fν · ofReal(-log fν) = ofReal(fν·(-log fν)) = ofReal(negMulLog fν)`)。

route (d'') の atom 1 (測度 domination) を `A(ν)` に橋渡しする鍵。proof-done (0 sorry)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。@audit:ok -/
private theorem crossPos_self (ν : Measure ℝ) [SigmaFinite ν] (hν : ν ≪ volume) :
    crossPos ν ν
      = ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume := by
  rw [crossPos]
  -- change of measure: `∫⁻ f ∂ν = ∫⁻ (ν.rnDeriv vol)·f ∂vol`.
  rw [← lintegral_rnDeriv_mul hν
    (f := fun x => ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)))
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

/-- **self-identity (負部)**: `ν` を自分自身に対する cross-entropy 負部が `differentialEntropyExt`
a.c. 枝の負部 `B(ν)` (`EntropyPowerExt.lean:62`) に一致。`crossPos_self` と同型 (符号反転)。
proof-done (0 sorry)。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。@audit:ok -/
private theorem crossNeg_self (ν : Measure ℝ) [SigmaFinite ν] (hν : ν ≪ volume) :
    crossNeg ν ν
      = ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume := by
  rw [crossNeg]
  -- change of measure: `∫⁻ f ∂ν = ∫⁻ (ν.rnDeriv vol)·f ∂vol`.
  rw [← lintegral_rnDeriv_mul hν
    (f := fun x => ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)))
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

/-- **整数性 helper**: `∫⁻ ofReal(f) < ⊤` ∧ `∫⁻ ofReal(-f) < ⊤` ∧ `AEStronglyMeasurable f`
から `Integrable f m`。`HasFiniteIntegral f = ∫⁻ ‖f‖ₑ` を `‖f‖ₑ = ofReal(f) + ofReal(-f)`
(正部・負部分解) に展開し、両 lintegral 有限性 + `lintegral_add` で組む。 -/
private theorem integrable_of_lintegral_ofReal_pos_neg_ne_top {m : Measure ℝ} {f : ℝ → ℝ}
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

/-- **⊤ を跨ぐ ℝ≥0∞ Gibbs (rearranged、finite-entropy 枝)**: `μ ≪ ν ≪ volume` (ともに
probability) で `h(μ) ≤ crossEnt(μ,ν)` を **⊤-⊤ を回避した移項 ℝ≥0∞ 形**:
`A(μ) + crossNeg μ ν ≤ crossPos μ ν + B(μ)`
(`A(μ) := ∫⁻ ofReal(negMulLog fμ) ∂vol`, `B(μ) := ∫⁻ ofReal(-(negMulLog fμ)) ∂vol`)。
**`μ` が有限微分エントロピー (`hμ_ent`) + cross-entropy μ-可積分 (`h_cross_int`) を持つ枝専用**
(両者で 4 lintegral 全有限 → ℝ-valued Gibbs に降ろせる)。A(μ)=⊤ の枝は consumer-form
`ennreal_gibbs_rearranged` が別途扱う。

**証明**: in-tree `differentialEntropy_le_cross_entropy` (`EPIInfiniteVarianceTruncation.lean:997`、
ℝ-valued Gibbs) を適用、`integral_eq_lintegral_pos_part_sub_lintegral_neg_part` で両辺を正部・負部
lintegral 差に同定 → ℝ で移項 → 全有限ゆえ ℝ≥0∞ に持ち上げ。

`hμ_ac`/`hν_ac`/`hμν` は絶対連続性、`hμ_ent`/`h_cross_int` は有限性 regularity precondition
(grant しても Gibbs 不等式は出ない → 非 load-bearing)。`#print axioms` = sorryAx-free。@audit:ok -/
private theorem ennreal_gibbs_rearranged_of_finite_ent {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_ac : μ ≪ volume) (hν_ac : ν ≪ volume) (hμν : μ ≪ ν)
    (hμ_ent : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume)
    (h_cross_int : Integrable (fun x => Real.log ((ν.rnDeriv volume x).toReal)) μ) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
        + crossNeg μ ν
      ≤ crossPos μ ν
        + ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume := by
  -- abbreviations for the four lintegrals (all finite under the regularity preconditions).
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume with hA
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB
  -- finiteness of all four from the integrability preconditions
  -- (`∫⁻ ofReal f ≤ ∫⁻ ‖f‖ₑ = hasFiniteIntegral`).
  have hbound : ∀ (f : ℝ → ℝ) (m : Measure ℝ), Integrable f m →
      (∫⁻ x, ENNReal.ofReal (f x) ∂m) ≠ ⊤ := by
    intro f m hf
    refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
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

/-- **⊤ を跨ぐ ℝ≥0∞ Gibbs (rearranged、consumer form)**: `μ ≪ ν ≪ volume` (ともに probability) で
`A(μ) + crossNeg μ ν ≤ crossPos μ ν + B(μ)`。route (d'') atom 2 の最終消費形。
`A(μ) := ∫⁻ ofReal(negMulLog fμ) ∂vol`, `B(μ) := ∫⁻ ofReal(-(negMulLog fμ)) ∂vol`。

**`A(μ) = ⊤` (h(μ)=+∞) を許す版**: assembly では `μ = ν_n` (截断和の法) が `h(ν_n) = ⊤` になりうる
(V が無限エントロピーのとき bounded-W + V が ⊤)。その枝で `A(W+V) = ⊤` を引き出すのが route (d'')
の核心。`crossPos μ ν` も ⊤ を許す。一方 `B(μ)` (= μ 自身の負部、`hμ_negPart_fin`) と
`crossNeg μ ν` (= 負部 cross-entropy、atom 1 domination で `(P E)⁻¹·B(ν) < ⊤`) は finite に固定。

**証明 (A(μ) で場合分け)**:
- **A(μ) < ⊤**: μ 有限微分エントロピー (A<⊤ ∧ B<⊤ で `negMulLog∘fμ` 可積分) →
  `crossPos μ ν` で更に場合分け: ⊤ なら RHS=⊤ で `le_top`、finite なら cross-entropy μ-可積分
  (crossPos<⊤ ∧ crossNeg<⊤ で `log∘fν` 可積分) → finite-entropy 版 `_of_finite_ent` に委譲。
- **A(μ) = ⊤**: LHS = ⊤、`B(μ)<⊤` ゆえ RHS=⊤ には `crossPos μ ν = ⊤` が必要。これは
  `A(μ)=⊤ ∧ B(μ)<⊤` (= h(μ)=+∞) から `crossPos μ ν = ⊤` を出す **⊤-case Gibbs**。
  ℝ-valued Gibbs (`differentialEntropy_le_cross_entropy`) は `hμ_ent` (= A<⊤) を必須にし、
  A=⊤ では `differentialEntropy μ` が Bochner 慣行で `0` に退化するため使えない。pointwise/
  subadditivity ルートも `∫⁻ ofReal(-log r) ∂μ` が同時に ⊤ になりうるため失敗 (構造的)。
  genuine な ℝ≥0∞ klFun 非負分解 (ofReal 非加法性を跨ぐ) が要る → Phase 4 closure 残課題。

`hμ_ac`/`hν_ac`/`hμν` は絶対連続性、`hμ_negPart_fin` (= B(μ)<⊤) / `hCN_fin` (= crossNeg μ ν<⊤)
は有限性 regularity precondition (結論核を encode せず、非 load-bearing: B(μ)<⊤ + crossNeg<⊤ を
grant しても A=⊤⟹crossPos=⊤ の Gibbs 核は出ない)。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
private theorem ennreal_gibbs_rearranged {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_ac : μ ≪ volume) (hν_ac : ν ≪ volume) (hμν : μ ≪ ν)
    (hμ_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤)
    (hCN_fin : crossNeg μ ν ≠ ⊤) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
        + crossNeg μ ν
      ≤ crossPos μ ν
        + ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume := by
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume with hA
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB
  by_cases hA_top : A = ⊤
  · -- A(μ) = ⊤ branch. LHS = `⊤ + crossNeg = ⊤`; with `B < ⊤` the goal needs `crossPos μ ν = ⊤`.
    -- 残課題 = genuine ⊤-case Gibbs `A=⊤ ∧ B<⊤ ∧ crossNeg<⊤ ⟹ crossPos μ ν = ⊤`
    -- (= h(μ)=+∞ ⟹ cross-entropy=+∞)。
    --
    -- 反証済の elementary route (CLAUDE.md「反証義務」):
    -- (1) ℝ-valued Gibbs `differentialEntropy_le_cross_entropy`: `hμ_ent` (= A<⊤) 必須。A=⊤ では
    --     `differentialEntropy μ = ∫ negMulLog fμ` が Bochner 慣行 (非可積分→0) で退化 = 使用不能。
    -- (2) pointwise ofReal subadditivity (`-log fμ = -log fν + -log r`、r=μ.rnDeriv ν):
    --     `A ≤ crossPos + ∫⁻ ofReal(-log r) ∂μ` を出すが、これは Gibbs の **逆向き**
    --     (`∫⁻ ofReal(-log r) ∂μ` = llr 負部 ≤ crossNeg + A で B に bound されない)。
    -- (3) combine-then-pointwise: `ofReal(-log fμ)+ofReal(log fν) ≤ ofReal(-log fν)+ofReal(log fμ)`
    --     は pointwise FALSE (ofReal 符号 clamp、反例 `log fμ=-5,log fν=3`)。
    -- 真の Gibbs は klFun 凸性/非負 (`klDiv_eq_lintegral_klFun_of_ac` + `klFun≥0`) を積分した
    -- 後にしか効かず、ofReal 非加法性を跨ぐ ℝ≥0∞ klFun 分解 (or 密度 truncation + 有限 Gibbs の
    -- monotone-limit、いずれも 50-100 行規模) が要る。proof-pivot-advisor への escalate 推奨
    -- (本 atom は route (d'') の load-bearing piece、詰まり方は klFun-分解 vs truncation-limit の
    -- 設計判断に直結)。
    -- @residual(plan:epi-uncond-truncation-lsc-plan)
    sorry
  · -- A(μ) < ⊤ branch: derive finite differential entropy of μ, delegate to `_of_finite_ent`.
    have hμ_ent : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume := by
      refine integrable_of_lintegral_ofReal_pos_neg_ne_top
        ((Real.continuous_negMulLog.measurable.comp
          (μ.measurable_rnDeriv volume).ennreal_toReal).aestronglyMeasurable) ?_ ?_
      · exact hA_top
      · exact hμ_negPart_fin
    by_cases hCP_top : crossPos μ ν = ⊤
    · rw [hCP_top, top_add]; exact le_top
    · -- crossPos μ ν < ⊤: derive cross-entropy integrability, delegate.
      have h_cross_int :
          Integrable (fun x => Real.log ((ν.rnDeriv volume x).toReal)) μ := by
        refine integrable_of_lintegral_ofReal_pos_neg_ne_top
          ((Real.measurable_log.comp
            (ν.measurable_rnDeriv volume).ennreal_toReal).aestronglyMeasurable) ?_ ?_
        · rw [crossNeg] at hCN_fin; exact hCN_fin
        · rw [crossPos] at hCP_top; exact hCP_top
      exact ennreal_gibbs_rearranged_of_finite_ent hμ_ac hν_ac hμν hμ_ent h_cross_int

/-- **per-fibre entropy integrability の translation 不変性**: `ν ≪ volume` で
`negMulLog (rnDeriv ν)` が可積分なら、平行移動 `ν.map (· + y)` でも可積分。Lebesgue 平行移動不変
(`map_add_right_eq_self`) + measure-preserving 合成 (`MeasurePreserving.integrable_comp_emb`) +
`MeasurableEmbedding.rnDeriv_map` で shift 後の rnDeriv を shift 前に同定。
独立 honesty audit 2026-06-08: Mathlib 機械的合成、循環/bundling なし。@audit:ok -/
private theorem integrable_negMulLog_rnDeriv_map_add_const
    {ν : Measure ℝ} [SigmaFinite ν] (y : ℝ)
    (hν_ent : Integrable (fun x => Real.negMulLog ((ν.rnDeriv volume x).toReal)) volume) :
    Integrable
      (fun x => Real.negMulLog (((ν.map (fun x => x + y)).rnDeriv volume x).toReal)) volume := by
  have hf : MeasurableEmbedding (fun x : ℝ => x + y) := measurableEmbedding_addRight y
  have h_map_vol : (volume : Measure ℝ).map (fun x => x + y) = volume :=
    MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) y
  -- `(· + y)` is measure-preserving on Lebesgue.
  have hmp : MeasurePreserving (fun x : ℝ => x + y) volume volume :=
    ⟨hf.measurable, h_map_vol⟩
  -- rnDeriv after the shift, evaluated at `x + y`, equals rnDeriv before the shift.
  have h_rn := hf.rnDeriv_map ν (volume : Measure ℝ)
  rw [h_map_vol] at h_rn
  -- It suffices to prove integrability of the composition `g ∘ (· + y)` and then transfer.
  have hcomp_int : Integrable
      (fun x => Real.negMulLog ((((ν.map (fun x => x + y)).rnDeriv volume) (x + y)).toReal))
      volume := by
    refine hν_ent.congr ?_
    filter_upwards [h_rn] with x hx
    rw [hx]
  -- transfer along the measure-preserving embedding `(· + y)`.
  exact (hmp.integrable_comp_emb hf).mp hcomp_int

/-- **convolution density as translate-average** (only the LEFT factor a.c.): for `μW ≪ volume`
the sum law `μW ∗ μV` is `volume.withDensity (z ↦ ∫⁻ v, f_W (z - v) ∂μV)` where `f_W = μW.rnDeriv vol`.
Unlike the route-T `convDensityAdd` machinery (`EPIConvDensity`, which requires **both** components
a.c.), this only needs `μW` a.c.; `μV` is a general (probability) measure. `lintegral_conv` (Tonelli)
+ `withDensity_rnDeriv_eq` (recover `μW = vol.withDensity f_W`) + translation invariance.

独立 honesty audit 2026-06-08 (sum-marginal crux supply): genuine, Mathlib 機械合成 (Tonelli +
平行移動不変)、結論は a.e. 測度等式 (regularity)、循環/bundling なし。@audit:ok -/
private theorem conv_eq_withDensity_translate_average
    (μW μV : Measure ℝ) [SFinite μW] [SFinite μV] (hμW : μW ≪ volume) :
    μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, μW.rnDeriv volume (z - v) ∂μV) := by
  set g : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hg_def
  have hg_meas : Measurable g := Measure.measurable_rnDeriv _ _
  have hμW_wd : μW = (volume : Measure ℝ).withDensity g :=
    (Measure.withDensity_rnDeriv_eq μW volume hμW).symm
  refine Measure.ext fun A hA => ?_
  have hind : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  have hinner_meas : Measurable (fun x => ∫⁻ v, A.indicator 1 (x + v) ∂μV) :=
    (hind.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'
  have hL : (μW ∗ μV) A = ∫⁻ x, (∫⁻ v, A.indicator 1 (x + v) ∂μV) ∂μW := by
    rw [← lintegral_indicator_one hA, Measure.lintegral_conv hind]
  have hR : ((volume : Measure ℝ).withDensity (fun z => ∫⁻ v, g (z - v) ∂μV)) A
      = ∫⁻ z, A.indicator 1 z * (∫⁻ v, g (z - v) ∂μV) ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    apply lintegral_congr; intro z
    by_cases hz : z ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hL, hR, hμW_wd,
    lintegral_withDensity_eq_lintegral_mul₀ hg_meas.aemeasurable hinner_meas.aemeasurable]
  calc ∫⁻ x, (g * fun x => ∫⁻ v, A.indicator 1 (x + v) ∂μV) x ∂volume
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
          (μ := (volume : Measure ℝ)) (fun z => g (z - v) * A.indicator 1 z) v]
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
独立 honesty audit 2026-06-08: genuine, ext + 平行移動不変、循環/bundling なし。@audit:ok -/
private theorem map_add_const_withDensity (f : ℝ → ℝ≥0∞) (z : ℝ) :
    ((volume : Measure ℝ).withDensity f).map (fun x => x + z)
      = (volume : Measure ℝ).withDensity (fun x => f (x - z)) := by
  have hmap : Measurable (fun x : ℝ => x + z) := measurable_id.add_const z
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hmap hA, withDensity_apply _ (hmap hA), withDensity_apply _ hA,
    ← lintegral_indicator (hmap hA), ← lintegral_indicator hA]
  rw [← lintegral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun x => A.indicator (fun y => f (y - z)) x) z]
  apply lintegral_congr; intro x
  by_cases hx : x + z ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by simpa using hx), add_sub_cancel_right]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa using hx)]

/-- **per-fibre a.c. (continuous disintegration, sum structure)**: for `W ⊥ V` under `Q` with
`Q.map W ≪ volume`, the affine-shift fibre `(Q.map W).map (·+z)` (= the per-fibre conditional law
of `W+V` given `V=z`, via `affineShiftKernel`) is a.c. w.r.t. the sum marginal `(Q.map W) ∗ (Q.map V)`
for a.e. `z ∂(Q.map V)`. This is the **continuous** version of the general disintegration fact
`condDistrib z ≪ μ.map X` (Mathlib's general/non-discrete version is absent; the in-tree
`Bridge.condDistrib_ae_absolutelyContinuous_map` is `[Countable X]`-only, unusable for `X = ℝ`).

機構: 和密度 `r(x) = ∫⁻ v, f_W(x-v) ∂μ_V` (= `conv_eq_withDensity_translate_average`)、translate 密度
`f_W(·-z)`。Fubini で `(μ_V × vol)({(z,x) : r(x)=0 ∧ 0<f_W(x-z)}) = 0` (各 x で `r(x)=0 ⟹ f_W(x-v)=0`
μ_V-a.e.)、swap で a.e. z に `{r=0} ⊆ {f_W(·-z)=0}` vol-a.e. を出し、withDensity 間 a.c. に変換。

独立 honesty audit 2026-06-08 (sum-marginal crux supply, 4-check): (1) 非循環 — 結論 (a.e. per-fibre
a.c.) は仮説 (indep + a.c. regularity) と非同型。(2) 非バンドル — `hindep`/`hμW_ac` は regularity
precondition、a.c. の核を encode せず。(3) 非退化 — `:True` slot なし。(4) sufficiency — Fubini +
support 包含で genuine、Z=X 退化 (Dirac fibre) は **sum 構造で除外** (translate of a.c. は a.c.、
Dirac でない)。

**独立 auditor 確認 (fresh subagent, 2026-06-08, 実装者 self-report と独立、4-check 再検証 PASS)**:
sorryAx-free 機械裏取り済 (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。
under-hypothesized でない (核心検証): `hμW_ac` を落とすと反例で偽 (μW=δ_a, μV=Unif[0,1] ⟹
δ_{a+z} ⋘ Unif[a,a+1]) = 仮説必要 = honest。退化境界: μV=δ_0 で trivial (δ_0 で μW≪μW)、Dirac fibre
病理 (一般 disintegration `condDistrib z ≪ μ.map X` は Z=X で偽) は **fibre が translate-of-a.c. =
それ自身 a.c. ＋ marginal が convolution = 全 translate を mixing** ゆえ排除 (sum 構造が本質、generic
condDistrib でない)。in-tree `Bridge.condDistrib_ae_absolutelyContinuous_map` は per-singleton vanishing
proof = 離散 alphabet 限定 (`X=ℝ` 構造的に不可) を確認 ⇒ 本 continuous 自前 build は集約漏れでなく
genuine distinct asset。@audit:ok -/
private theorem condDistrib_ae_absolutelyContinuous_indep_add
    {μW μV : Measure ℝ} [SFinite μW] [SFinite μV] [IsProbabilityMeasure μV] (hμW_ac : μW ≪ volume) :
    ∀ᵐ z ∂μV, (μW.map (fun x => x + z)) ≪ (μW ∗ μV) := by
  have hconv : μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, μW.rnDeriv volume (z - v) ∂μV) :=
    conv_eq_withDensity_translate_average μW μV hμW_ac
  have htrans : ∀ z : ℝ, μW.map (fun x => x + z)
      = (volume : Measure ℝ).withDensity (fun x => μW.rnDeriv volume (x - z)) := by
    intro z
    conv_lhs => rw [show μW = (volume : Measure ℝ).withDensity (μW.rnDeriv volume) from
      (Measure.withDensity_rnDeriv_eq μW volume hμW_ac).symm]
    rw [map_add_const_withDensity (μW.rnDeriv volume) z]
  set f : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hf_def
  have hf_meas : Measurable f := Measure.measurable_rnDeriv _ _
  set r : ℝ → ℝ≥0∞ := fun z => ∫⁻ v, f (z - v) ∂μV with hr_def
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
      exact measure_mono_null (fun v hv => pos_iff_ne_zero.mp hv.2) hfzero
    · have : {v | r x = 0 ∧ 0 < f (x - v)} = ∅ := by ext v; simp [hrx]
      rw [this]; simp
  have hkey : ∫⁻ z, (volume : Measure ℝ) (Prod.mk z ⁻¹' S) ∂μV = 0 := by
    rw [← Measure.prod_apply hSmeas, Measure.prod_apply_symm hSmeas]
    simp_rw [show ∀ x : ℝ, (fun v => (v, x)) ⁻¹' S = {v | r x = 0 ∧ 0 < f (x - v)} from fun _ => rfl,
      hslice_x, lintegral_zero]
  have hae_slice : ∀ᵐ z ∂μV, (volume : Measure ℝ) (Prod.mk z ⁻¹' S) = 0 :=
    (lintegral_eq_zero_iff (measurable_measure_prodMk_left hSmeas)).mp hkey
  filter_upwards [hae_slice] with z hz
  rw [htrans z, hconv]
  have hfz_meas : Measurable (fun x : ℝ => f (x - z)) := hf_meas.comp (measurable_id.sub_const z)
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  rw [withDensity_apply _ hA] at hA0 ⊢
  rw [setLIntegral_eq_zero_iff hA hr_meas] at hA0
  rw [setLIntegral_eq_zero_iff hA hfz_meas]
  have hnull2 : ∀ᵐ x ∂volume, ¬ (r x = 0 ∧ 0 < f (x - z)) := by
    rw [ae_iff]; convert (hz : (volume : Measure ℝ) (Prod.mk z ⁻¹' S) = 0) using 2; ext x; simp [hS_def]
  filter_upwards [hA0, hnull2] with x hx0 hxsub hxA
  by_contra hne
  exact hxsub ⟨hx0 hxA, pos_iff_ne_zero.mpr hne⟩

/-- **single-component negative-part finiteness of the sum law** — `B(μW ∗ μV) < ⊤` from
`B(μW) < ⊤`. The single-component generalization of route-T
`integrable_negPart_negMulLog_map_condTrunc_sum` (`EPIInfiniteVarianceTruncation.lean:600`),
which averages over the X-marginal `pn·vol` (requires both components a.c.) and bounds the
Y-marginal negative part. Here the averaging is over the **general probability measure** `μV`
(no a.c. on `μV` needed, so it works even when `V` is non-a.c.), bounding the **W-marginal**
negative part `B(μW)`.

機構 (route-T:600 を下敷きに、averaging measure を `pn·vol → μV` に差し替え):
- `r := ((μW ∗ μV).rnDeriv vol).toReal`, `fW := (μW.rnDeriv vol).toReal`, `φ t := t·log t`.
  目標 `∫⁻ ofReal(-(negMulLog r)) = ∫⁻ ofReal(φ r) ≤ ∫⁻ ofReal(max (φ r) 0)`。
- 収束密度: `r =ᵐ[vol] fun z => ∫ v, fW(z-v) ∂μV` (`conv_eq_withDensity_translate_average` の
  `Measure.rnDeriv_withDensity` + `integral_toReal`)。`μV` 確率測度ゆえ平均。
- per-z Jensen: `φ(r z) ≤ ∫ v, max (φ (fW(z-v))) 0 ∂μV` (`Real.convexOn_mul_log.map_integral_le`,
  `μ := μV` 確率測度)。
- Tonelli + 平行移動不変: `∫⁻ z, ofReal(max (φ (r z)) 0) ≤ ∫⁻ z ∫⁻ v ofReal(max(φ(fW(z-v)))0) ∂μV
  = ∫⁻ v ∫⁻ z ofReal(Cq(z-v)) ∂vol ∂μV = (μV univ)·C = 1·C = C = B(μW) < ⊤`.

proof-done (0 sorry)。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。
非循環/非バンドル/非退化: 結論 (和周辺負部 lintegral 有限性) は仮説 (`hμW` a.c. + `B(μW)<⊤`) と
非同型、両仮説は regularity precondition、`:True`/退化なし。

**独立 honesty audit 2026-06-08 (fresh subagent, self-applied @audit:ok を独立確認 → ok)**:
under-hypothesized でないことを反例試行で確認済 (3 仮説いずれも load-bearing for soundness、欠落で偽):
- `[IsProbabilityMeasure μV]` 欠落 → Jensen `φ(∫f dμV) ≤ ∫φ(f) dμV` が確率測度必須ゆえ崩壊、bound
  `μV(univ)·B(μW)` も発散。確率性は regularity precondition で genuine 必要・present。
- `hμW` (a.c.) 欠落 → 反例 μW=δ₀ (rnDeriv=0 a.e. で `B(δ₀)=0≠⊤` を vacuous に満たすが `δ₀∗μV=μV`、
  μV を `B=⊤` の a.c. 確率測度に取ると結論偽)。body は `conv_eq_withDensity_translate_average`
  (`:109`) で a.c. を genuine 消費。
- `hμW_negPart_fin` (B(μW)<⊤) 欠落 → 反例 μW a.c. で密度 spike により `B(μW)=⊤`、bound 右辺 ⊤ で
  結論不成立。
退化境界: μV=δ₀ で `μW∗δ₀=μW`、結論=仮説で trivial だが non-vacuous (live statement)。
false-statement でない: 「凸性 + μV 確率での Jensen → Tonelli + 平行移動不変で和の負部 ≤ 片成分負部」
は数学的に正しい (`Real.convexOn_mul_log.map_integral_le` line 414 で genuine 適用)。`#print axioms`
(transient + `lake env lean`) = `[propext, Classical.choice, Quot.sound]`、sorryAx 非依存を機械再確認。
@audit:ok -/
private theorem negPart_negMulLog_conv_single_ne_top
    (μW μV : Measure ℝ) [IsFiniteMeasure μW] [IsProbabilityMeasure μV] (hμW : μW ≪ volume)
    (hμW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μW.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((μW ∗ μV).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := by
  -- densities and `φ t = t log t = -(negMulLog t)`.
  set fW : ℝ → ℝ := fun x => (μW.rnDeriv volume x).toReal with hfW_def
  set r : ℝ → ℝ := fun x => ((μW ∗ μV).rnDeriv volume x).toReal with hr_def
  set φ : ℝ → ℝ := fun t => t * Real.log t with hφ_def
  have hφ_eq : ∀ t, -(Real.negMulLog t) = φ t := by
    intro t; show -(-t * Real.log t) = t * Real.log t; ring
  -- basic measurability / nonnegativity.
  have hfW_meas : Measurable fW := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hfW_nn : ∀ x, 0 ≤ fW x := fun _ => ENNReal.toReal_nonneg
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hr_nn : ∀ x, 0 ≤ r x := fun _ => ENNReal.toReal_nonneg
  have hφ_meas : Measurable φ := measurable_id.mul (Real.measurable_log.comp measurable_id)
  -- `Cq w = (φ (fW w))⁺`.  `C = ∫⁻ ofReal Cq = ∫⁻ ofReal (-(negMulLog fW)) = hμW_negPart_fin`.
  set Cq : ℝ → ℝ := fun w => max (φ (fW w)) 0 with hCq_def
  have hCq_nn : ∀ w, 0 ≤ Cq w := fun _ => le_max_right _ _
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
      = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, fWe (z - v) ∂μV) :=
    conv_eq_withDensity_translate_average μW μV hμW
  have hrho_meas : Measurable (fun z => ∫⁻ v, fWe (z - v) ∂μV) :=
    (hfWe_meas.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  -- `r =ᵐ[vol] fun z => ∫ v, fW (z-v) ∂μV`  (toReal of the convolution density, μV is a prob measure).
  have hr_conv : r =ᵐ[volume] fun z => ∫ v, fW (z - v) ∂μV := by
    have h_rn : (μW ∗ μV).rnDeriv volume =ᵐ[volume] fun z => ∫⁻ v, fWe (z - v) ∂μV := by
      rw [hconv]; exact Measure.rnDeriv_withDensity volume hrho_meas
    have h_lt : ∀ᵐ z ∂volume, (μW ∗ μV).rnDeriv volume z < ∞ :=
      Measure.rnDeriv_lt_top (μW ∗ μV) volume
    filter_upwards [h_rn, h_lt] with z hz hz_lt
    show ((μW ∗ μV).rnDeriv volume z).toReal = ∫ v, fW (z - v) ∂μV
    -- `∫⁻ v, fWe(z-v) ∂μV < ∞` ⟹ `fWe(z-v) < ∞` μV-a.e. (finite integral ⟹ a.e. finite).
    have hfWe_z_meas : Measurable (fun v => fWe (z - v)) := by fun_prop
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
        = ∫⁻ w, ENNReal.ofReal (g w) ∂volume := fun v =>
      lintegral_sub_right_eq_self (fun w => ENNReal.ofReal (g w)) v
    simp_rw [hinner]
    rw [lintegral_const, mul_comm]
  -- product-measure integrability of `K (z, v) = fW (z - v)` (needed for the per-z section
  -- integrability of `v ↦ Cq (z - v)`).
  have hkernel_int : ∀ g : ℝ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
      (∫⁻ w, ENNReal.ofReal (g w) ∂volume) ≠ ⊤ →
      Integrable (fun p : ℝ × ℝ => g (p.1 - p.2)) (volume.prod μV) := by
    intro g hg hg_nn hg_fin
    have hgp_meas : Measurable (fun p : ℝ × ℝ => g (p.1 - p.2)) :=
      hg.comp (measurable_fst.sub measurable_snd)
    refine ⟨hgp_meas.aestronglyMeasurable, ?_⟩
    have hnn : ∀ᵐ p : ℝ × ℝ ∂(volume.prod μV), 0 ≤ g (p.1 - p.2) :=
      Filter.Eventually.of_forall (fun p => hg_nn _)
    rw [hasFiniteIntegral_iff_ofReal hnn,
      lintegral_prod _ hgp_meas.ennreal_ofReal.aemeasurable,
      hkernel_lint g hg hg_nn, measure_univ, one_mul]
    exact lt_of_le_of_ne le_top hg_fin
  -- per-`z` section integrability: `v ↦ Cq (z - v)` integrable w.r.t. `μV`  (a.e. `z`).
  have hsec_Cq : ∀ᵐ z ∂volume, Integrable (fun v => Cq (z - v)) μV := by
    have := (hkernel_int Cq hCq_meas hCq_nn (by rw [← hC_def]; exact hC_lt_top)).prod_right_ae
    exact this
  -- per-`z` section integrability of `v ↦ fW (z - v)` (the Jensen integrand `f`).
  have hsec_fW : ∀ᵐ z ∂volume, Integrable (fun v => fW (z - v)) μV := by
    have := (hkernel_int fW hfW_meas hfW_nn (by
      -- `∫⁻ ofReal fW = μW univ = 1`  (probability density of `μW`).
      have hae_eq : (fun x => ENNReal.ofReal (fW x)) =ᵐ[volume] μW.rnDeriv volume := by
        filter_upwards [μW.rnDeriv_ne_top volume] with x hx
        rw [hfW_def]; exact ENNReal.ofReal_toReal hx
      rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hμW]
      exact measure_ne_top _ _)).prod_right_ae
    exact this
  -- ============================================================================
  -- per-`z` Jensen bound:  `max (φ (r z)) 0 ≤ ∫ v, Cq (z - v) ∂μV`  (a.e. `z`).
  -- ============================================================================
  set G : ℝ → ℝ := fun z => max (φ (r z)) 0 with hG_def
  have hG_nn : ∀ z, 0 ≤ G z := fun _ => le_max_right _ _
  have hjensen : ∀ᵐ z ∂volume, G z ≤ ∫ v, Cq (z - v) ∂μV := by
    filter_upwards [hr_conv, hsec_Cq, hsec_fW] with z hz hzCq hzfW
    -- abbreviation `f v = fW (z - v)`.
    set f : ℝ → ℝ := fun v => fW (z - v) with hf_def
    have hf_nn : ∀ v, 0 ≤ f v := fun _ => hfW_nn _
    -- `max (φ (f v)) 0 = Cq (z - v)` and `(φ∘f)⁻ = Cm (z - v)`.
    have hCqf_int : Integrable (fun v => max (φ (f v)) 0) μV := hzCq
    set Cm : ℝ → ℝ := fun v => max (-(φ (f v))) 0 with hCm_def
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
    have hφf_eq : (fun v => φ (f v)) = fun v => max (φ (f v)) 0 - Cm v := by
      funext v
      show φ (f v) = max (φ (f v)) 0 - max (-(φ (f v))) 0
      rcases le_or_gt 0 (φ (f v)) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -(φ (f v)) ≤ 0)]; ring
      · rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(φ (f v)))]; ring
    have hf_int : Integrable f μV := hzfW
    have hφf_int : Integrable (fun v => φ (f v)) μV := by
      rw [hφf_eq]; exact hCqf_int.sub hCm_int
    -- Jensen:  `φ (∫ f ∂μV) ≤ ∫ φ∘f ∂μV`.
    have hjz : φ (∫ v, f v ∂μV) ≤ ∫ v, φ (f v) ∂μV := by
      have := Real.convexOn_mul_log.map_integral_le
        (μ := μV) (f := f) (g := φ)
        Real.continuous_mul_log.continuousOn
        isClosed_Ici
        (Filter.Eventually.of_forall (fun v => hf_nn v))
        hf_int hφf_int
      simpa only [hφ_def] using this
    -- `r z = ∫ v, f v ∂μV`  (the convolution-density identity `hz`).
    have hrz_eq : r z = ∫ v, f v ∂μV := hz
    have hstep1 : φ (r z) ≤ ∫ v, φ (f v) ∂μV := by rw [hrz_eq]; exact hjz
    have hstep2 : (∫ v, φ (f v) ∂μV) ≤ ∫ v, max (φ (f v)) 0 ∂μV :=
      integral_mono hφf_int hCqf_int (fun v => le_max_left _ _)
    have hstep3 : (∫ v, max (φ (f v)) 0 ∂μV) = ∫ v, Cq (z - v) ∂μV := rfl
    have hCq_int_z : (0 : ℝ) ≤ ∫ v, Cq (z - v) ∂μV :=
      integral_nonneg (fun v => hCq_nn _)
    rw [hG_def]
    exact max_le (by rw [← hstep3]; exact le_trans hstep1 hstep2) hCq_int_z
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
                  (Filter.Eventually.of_forall (fun v => hCq_nn _))]
            _ ≤ _ := le_refl _
      _ = (μV Set.univ) * C := by rw [hkernel_lint Cq hCq_meas hCq_nn, hC_def]
  refine ne_top_of_le_ne_top ?_ hfinal
  rw [measure_univ, one_mul]; exact hC_lt_top

/-- **negMulLog-Fatou helper** — 正部 lintegral `A` の Fatou lift。
density の toReal a.e. 収束 `f_{μ_n} → f_μ` から `A_μ ≤ liminf A_{μ_n}` を Fatou で出す
(`A μ := ∫⁻ x, ofReal (negMulLog (rnDeriv μ vol x).toReal) ∂volume` = `differentialEntropyExt`
の a.c. 枝の正部、`EntropyPowerExt.lean:61`)。

`klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`、`@audit:ok`) と完全同型で、
`klFun`→`negMulLog` 差替のみ (両者 continuous)。骨格 = `lintegral_liminf_le` +
`ENNReal.continuous_ofReal` + `Tendsto.liminf_eq` + `lintegral_mono_ae`。Phase 0 scratch
(`/tmp/route_beta_phase0.lean` `A_le_liminf_of_ae_tendsto`) で骨格実証済 (0 sorry)、本 file
では Phase 3 で埋める skeleton として sorry。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(正部 lintegral の liminf 下界) は仮説 `h_ae` (density a.e. 収束) と非同型。(2) 非バンドル —
`h_ae` は a.e. 収束 input precondition、Fatou 不等式の核を encode せず。(3) 非退化 — `:True`
slot なし。(4) sufficiency — Fatou (`lintegral_liminf_le`、非負被積分関数列で `∫ liminf ≤
liminf ∫`) が正しい向き: `ofReal(negMulLog ...)` で負部を 0 clamp した正部 A に対し成立する
向きで、収束列の極限 = liminf を使う (`klDiv_le_liminf_of_ae_tendsto` body と同構造)。
classification: `klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`) と **別物**
(参照測度 γ 有限 vs volume 無限、klFun vs negMulLog) ゆえ集約漏れでない。`plan:` 妥当
(Mathlib 1本不在の壁でなく既存同型骨格の差替で closeable、対応 plan 実在)。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_posPart_le_liminf_of_ae_tendsto
    (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ)
    (h_ae : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => ((μ_n n).rnDeriv volume x).toReal) atTop
        (𝓝 ((μ.rnDeriv volume x).toReal))) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
      ≤ Filter.liminf
          (fun n => ∫⁻ x, ENNReal.ofReal
            (Real.negMulLog (((μ_n n).rnDeriv volume x).toReal)) ∂volume) atTop := by
  sorry

/-- **per-n 単調性** (proof-done, 0 sorry): 各 n で `h(W_n) ≤ h(W_n + V)`、`W_n := truncW P W n`
(= `P` を W-事象 `{|W| ≤ n}` で条件付けた compact-support 近似)。

**route (chain rule 不使用)**: 旧版は finite ② chain rule
`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite` を `X:=W+V, Z:=V` で適用していたが、
その 11 regularity 仮説のうち `hκ_dens_meas` (joint 密度可測) が Mathlib 不在の真 gap だった。
本版は **chain rule を完全に捨て**、fibre を抽象 condDistrib でなく **explicit な平行移動
`(Q.map W).map(·+z)`** として扱う per-fibre translate Gibbs に置き換え、`hκ_dens_meas`/`hκ_KL`/
`hκ_cross_int` を全廃する。

記号: `Q := truncW P W n`、`ν := Q.map(W+V) = (Q.map W) ∗ (Q.map V)` (独立 ⟹ 畳み込み)、
`rfun := (ν.rnDeriv vol).toReal` (和周辺密度)、`fW := (Q.map W).rnDeriv vol .toReal`。

**証明の骨格 (3 段)**:
1. **B(ν) < ⊤** (= 和周辺の負部 lintegral 有限性): single-component helper
   `negPart_negMulLog_conv_single_ne_top` を `μW := Q.map W`, `μV := Q.map V` で適用。`B(Q.map W) < ⊤`
   (= `hBn_fin`、`hW_negPart_fin` を truncated 密度分解 + `negMulLog_mul` で供給) が入力。averaging は
   確率測度 `Q.map V` 上ゆえ `V` の a.c. 不要 (route-T single-component 一般化)。
2. **場合分け** `by_cases hent_sum : Integrable (negMulLog ∘ rfun) volume`:
   - **Case A (無限枝, `¬ hent_sum`)**: `B(ν) < ⊤` と `¬ hent_sum` から正部 `A(ν) = ⊤`、よって
     `differentialEntropyExt ν = ⊤`、`h(W_n) ≤ ⊤` を `le_top` で閉じる (route T capstone Case 2 と同型)。
   - **Case B (有限枝, `hent_sum`)**: 両辺を workhorse `differentialEntropy` に降ろし、実不等式
     `h(Q.map W) ≤ h(ν)` を **per-fibre translate Gibbs** で建てる: 各 fibre `μWz z := (Q.map W).map(·+z)`
     に Gibbs 出口 `differentialEntropy_le_cross_entropy` (`μWz z ≪ ν` は連続 disintegration a.c.
     `condDistrib_ae_absolutelyContinuous_indep_add` で供給) → 平行移動不変
     `differentialEntropy_map_add_const` で LHS を定数化 → `μV` 上で積分 → cross-entropy 項を Tonelli
     (`r(x) = ∫ fW(x-z) ∂μV` = 収束密度恒等式) で collapse して `-h(ν)` に同定。

**仮説は全て regularity (非 load-bearing)**: `hW`/`hV`/`hWV`/`hW_ac` は可測/独立/絶対連続、
`hW_negPart_fin` (= `B(W) < ⊤`) は h(W) 負部有限性、`hn` (positive mass) は cond well-defined の scope。
単調性の核は body の per-fibre Gibbs + Tonelli が担い、仮説に encode しない。`#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free、要 olean refresh で確認)。

**独立 honesty audit 2026-06-08 (fresh subagent, proof-done 主張検証 → ok)**: proof-done 確定。
(1) 非循環 — 結論 `h(W_n) ≤ h(W_n+V)` は 7 仮説のいずれとも非同型、body は genuine 全証明 (`:= h`
でない)。(2) 非バンドル — `hW`/`hV`/`hWV`/`hW_ac` は可測/独立/絶対連続、`hW_negPart_fin` (=B(W)<⊤)
は ⊤ 枝の `⊤-⊤` 不定形回避用の有限性 precondition (B(W)<⊤ を grant しても単調性は出ない = core-
reconstruction FAIL = 非 load-bearing)、`hn` は cond well-defined scope。単調性の核 = Case B の
per-fibre translate Gibbs (`differentialEntropy_le_cross_entropy` 経由) + Tonelli collapse で body
が担う。(3) 非退化 — Case A の `le_top` は `differentialEntropyExt ν = A−B = ⊤−(有限) = ⊤` を A(ν)=⊤
(¬hent_sum で `‖g‖ₑ = A+B` 分解、B<⊤ は `negPart_negMulLog_conv_single_ne_top` で genuine 供給) から
建ててからの genuine EReal ⊤ 利用 (route T capstone Case 2 と同型、vacuous/exfalso でない)。(4)
sufficiency — 結論は 7 仮説から follow、依存 private helper 6 本 + 外部 Gibbs `differentialEntropy_le_
cross_entropy` (`@audit:ok`) 全て sorry-free。**機械裏取り**: `#print axioms` (transient + `lake env lean`、
olean refresh 後) = `[propext, Classical.choice, Quot.sound]`、sorryAx **非依存** を確認 (Phase 3/4
skeleton sorry 3 件は本定理の依存 path 外、axiom 出力 clean で transitive 0 sorry)。@audit:ok -/
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
  -- W + V is a.c. under `Q` (`hW_ac_Q` + independence).
  have hWV_ac_Q : (Q.map (fun ω => W ω + V ω)) ≪ volume :=
    map_add_absolutelyContinuous W V Q hW hV hindep hW_ac_Q
  -- Probability-measure instances on the relevant marginals.
  haveI hWmap_prob : IsProbabilityMeasure (Q.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hVmap_prob : IsProbabilityMeasure (Q.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  -- The sum law equals the convolution of the W- and V-marginals (independence).
  have hsum_conv : Q.map (fun ω => W ω + V ω) = (Q.map W) ∗ (Q.map V) := by
    have := hindep.map_add_eq_map_conv_map hW hV
    simpa [Pi.add_apply] using this
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
  -- `h(W_n) ≠ ⊥` (compact-support ⟹ finite differential entropy ⟹ `= (real : EReal) ≠ ⊥`).
  have hW_ne_bot : differentialEntropyExt (Q.map W) ≠ ⊥ := by
    rw [differentialEntropyExt_of_ac_integrable hW_ac_Q hW_ent_Q]
    exact EReal.coe_ne_bot _
  -- abbreviations for the sum law `ν := Q.map (W+V) = (Q.map W) ∗ (Q.map V)` and its density.
  set ν : Measure ℝ := Q.map (fun ω => W ω + V ω) with hν_def
  set rfun : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal with hrfun_def
  -- **`B(ν) < ⊤`** (sum-marginal negative-part), via the single-component helper
  -- `negPart_negMulLog_conv_single_ne_top` averaging over the probability measure `Q.map V`
  -- (no a.c. on `V` needed).  `B(Q.map W) < ⊤` is `hBn_fin` (= `hW_negPart_fin` truncated).
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

/-- **`h(W_n) → h(W)` の極限**: truncation 緩和で entropy 単調増加 → 極限。`h(W) = ⊤` のときは
`h(W_n) ↑ ⊤` の単調発散 (有界増加列の ⊤ への発散) で、weak-convergence portmanteau を経由しない。
route T が `tendsto_measure_iUnion_atTop` (`EPIInfiniteVarianceTruncation.lean:110`) ベースの
極限を実証済。

route β' Phase 3 で埋める。極限が density a.e. 収束 (`differentialEntropyExt_posPart_le_liminf_of_ae_tendsto`
適用可) or 単調収束のみで閉じ、weak-conv 定義を使わないことを担保する。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(極限 `h(W_n) → h(W)`) は仮説 `hW`/`hW_ac` と非同型。(2) 非バンドル — 両仮説は可測/絶対連続の
regularity precondition、極限の核を encode せず。(3) 非退化 — `:True` slot なし。(4) sufficiency
— truncation 緩和列の entropy 単調増加 → 極限 (`h(W)=⊤` で `h(W_n)↑⊤`) は正しい (route T が
`tendsto_measure_iUnion_atTop` で同型極限を実証)。`plan:` 妥当。
**独立 auditor 確認 (fresh subagent、2026-06-08)**: 4-check PASS、honest_residual。`plan:` slug 実在。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_truncW_tendsto
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) :
    Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (differentialEntropyExt (P.map W))) := by
  sorry

/-- **gateway ⊤ 枝 (無条件)**: `h(W) = ⊤ ⟹ h(W+V) = ⊤`、無条件版② (i-a) を bypass。
per-n 単調性 `h(W_n) ≤ h(W_n + V)` (`differentialEntropyExt_mono_add_truncW`) と `h(W_n) ↑ ⊤`
(`differentialEntropyExt_truncW_tendsto`) を組み、`h(W_n + V) ≥ h(W_n) → ⊤` で `h(W+V) = ⊤`。
route T capstone Case 2 (`EPIInfiniteVarianceCapstone.lean:343`、`entropyPowerExt = ⊤` を
`le_top`) と同型の「⊤ 枝は EReal ⊤ 表現で trivial に閉じる」を再利用する。

**⊤ 枝のみ無条件、有限枝は別 lemma** (finite ② / coe 枝)。`_unconditional` 命名は本 ⊤ 枝が真に
無条件 (regularity precondition `hW`/`hV`/`hWV`/`hW_ac` のみ、無条件版② sorry を継承しない) なため
honest。`hW_top` (h(W)=⊤) は場合分け precondition で load-bearing でない。

route β' Phase 4 で埋める。

独立 honesty audit 2026-06-08 (skeleton, 4-check + name-laundering PASS → honest_residual):
**`_unconditional` 命名 = NOT name-laundering**。signature は既存 `differentialEntropyExt_top_of_indep_add`
(`EPIUncondMonotone.lean:153`、(i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` の transitive
sorry を継承) と **完全同一の仮説群** (`hW`/`hV`/`hWV`/`hW_ac`/`hW_top`、結論も同一)。新規 load-bearing
hypothesis を threading していない — `_unconditional` は「(i-a) sorry を継承しない別 route (truncation
近似) で同結論を建てる」という proof-route の主張で、「仮説が無い」主張ではない (CORE doctrine の
name_laundering は「open load-bearing hyp or 完成偽装 sorry-body」、本件は body sorry が `@residual`
で正直にマーク済 = 偽装でない)。**`hW_top` load-bearing 判定**: `h(W)=⊤` は ⊤ 枝の場合分け
precondition、結論の核 (= h(W+V)=⊤) を encode せず。hard core = 単調性 `h(W)≤h(W+V)` (#3 が供給)、
`hW_top` + 単調性 → `h(W+V)≥⊤` → `=⊤` (`le_top`)。`le_top` は退化定義悪用でなく EReal ⊤ 表現の
genuine 利用 (route T capstone Case 2 と同型)。(4) sufficiency — `h(W)=⊤` + 単調性で `h(W+V)=⊤` は
正しい含意 (反例なし: 単調性が無条件で成立する以上 ⊤ 入力は ⊤ 出力)。`plan:` 妥当。

**独立 auditor 確認 (fresh subagent、2026-06-08)**: `_unconditional` 命名 = **NOT name-laundering**。
CORE doctrine の name_laundering は「open load-bearing hyp を残したまま / 完成偽装 sorry-body で _full
等を名乗る」だが、本件は (a) load-bearing hyp なし (`hW`/`hV`/`hWV`/`hW_ac` は regularity、`hW_top` は
場合分け precondition で結論核 = h(W+V)=⊤ を encode せず)、(b) body sorry は `@residual(plan:...)` で
正直にマーク済 = 偽装でない。命名は「(i-a) sorry を継承しない別 route で同結論を建てる」proof-route の
主張で正当。⚠ 本 ⊤ 枝 closure (body) は #3 の単調性 (4 sorry 残) + #2/#3 極限に transitive 依存ゆえ
**現状 #4 自体が未着手 sorry**、proof-done でない (honest_residual)。honest sorry、4-check + name-laundering
PASS。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  sorry

end InformationTheory.Shannon
