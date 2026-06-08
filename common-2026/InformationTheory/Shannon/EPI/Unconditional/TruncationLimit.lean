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
(ℝ で書くと subtraction、ℝ≥0∞ では ⊤-⊤ 回避のため移項形で扱う)。

**atom 2 全体 proof-done (sorryAx-free)**: `crossPos_self`/`crossNeg_self` (self-identity) +
`ennreal_gibbs_rearranged` (consumer form、`A(μ)=⊤` 許容) が `#print axioms` で
`[propext, Classical.choice, Quot.sound]`。⊤-case Gibbs は **負部 `∫⁻ ofReal(-log r) ∂μ ≤ 1`**
(普遍定数 1-有界 = klFun≥0 の content、`-r log r ≤ 1`) で genuine 着地。 -/

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
(grant しても Gibbs 不等式は出ない → 非 load-bearing)。出口補題 `differentialEntropy_le_cross_entropy`
(ℝ-Gibbs、本体に KL≥0 = `toReal_klDiv_of_measure_eq` の genuine 核) を pos/neg 分解で lift。
独立 honesty audit 2026-06-08 PASS: regularity precondition のみ、核は出口補題本体。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械再確認)。@audit:ok -/
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

**証明 (A(μ) で場合分け、proof-done)**:
- **A(μ) < ⊤**: μ 有限微分エントロピー (A<⊤ ∧ B<⊤ で `negMulLog∘fμ` 可積分) →
  `crossPos μ ν` で更に場合分け: ⊤ なら RHS=⊤ で `le_top`、finite なら cross-entropy μ-可積分
  (crossPos<⊤ ∧ crossNeg<⊤ で `log∘fν` 可積分) → finite-entropy 版 `_of_finite_ent` に委譲。
- **A(μ) = ⊤**: `A(μ)=⊤ ⟹ crossPos μ ν = ⊤` (⊤-case Gibbs、finiteness precondition 不要) を出し、
  RHS=`crossPos+B(μ)=⊤` で `le_top`。核は **負部の普遍定数 1-有界** (= klFun≥0 の content):
  1. pointwise subadditivity (μ-a.e.、`-log fμ = -log fν + -log r`, `r := dμ/dν`):
     `ofReal(-log fμ) ≤ ofReal(-log fν) + ofReal(-log r)` (`ENNReal.ofReal_add_le`)。積分して
     `A(μ) = crossPos μ μ ≤ crossPos μ ν + ∫⁻ ofReal(-log r) ∂μ` (`crossPos_self` で `crossPos μ μ = A(μ)`)。
  2. `∫⁻ ofReal(-log r) ∂μ ≤ 1`: change-of-measure `lintegral_rnDeriv_mul` で ν へ移し
     `∫⁻ ofReal(r·(-log r)) ∂ν`、各 fibre で `-r log r ≤ 1 - r ≤ 1` (`Real.log_le_sub_one_of_pos`
     を `1/r` に適用)、`∫⁻ 1 ∂ν = ν univ = 1`。
  3. `A(μ)=⊤ ≤ crossPos μ ν + 1`、`1 ≠ ⊤` ゆえ `crossPos μ ν = ⊤`。
  (当初 #2 ルートを「負部が `crossNeg+A` で wrong-direction」と誤判定したが、負部 = dμ/dν の log で
  cross 項でなく、`-r log r ≤ 1` の普遍定数で抑えられる = klFun≥0 が効く。orchestrator escalate で訂正。)

`hμ_ac`/`hν_ac`/`hμν` は絶対連続性、`hμ_negPart_fin` (= B(μ)<⊤) / `hCN_fin` (= crossNeg μ ν<⊤)
は有限性 regularity precondition (A<⊤ 枝で finite-entropy 版へ委譲する際の integrability 供給に使用、
A=⊤ 枝では未使用 = 結論核を encode せず非 load-bearing。downstream assembly が同じ finiteness を持つ)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。
独立 honesty audit 2026-06-08 PASS (4-check 全通過): core-reconstruction = 2 finiteness hyp を grant しても
Gibbs (KL≥0) は出ない (非 load-bearing、Gibbs 核は A<⊤ 枝の出口補題 `differentialEntropy_le_cross_entropy`
本体 + A=⊤ 枝の `-r log r ≤ 1` 普遍定数で genuine 供給)。sufficiency = `A=⊤ ⟹ crossPos=⊤` を body が
genuine に証明 (退化/vacuous でない、refutation: 「A=⊤ かつ crossPos<⊤」なら偽だが body がこの枝を排除)。
循環/`:= h`/`:True` slot なし。`#print axioms` 機械再確認 sorryAx-free。@audit:ok -/
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
  · -- A(μ) = ⊤ branch. LHS = `⊤ + crossNeg = ⊤`; goal needs `crossPos μ ν = ⊤`, then RHS = ⊤.
    -- ⊤-case Gibbs: `A(μ) = ⊤ ⟹ crossPos μ ν = ⊤` via pointwise subadditivity
    -- (`-log fμ = -log fν + -log r`, `r := dμ/dν`) + **negative part 1-bounded** (`-r log r ≤ 1`,
    -- = klFun ≥ 0 content). This needs no finiteness precondition.
    have hCP_top : crossPos μ ν = ⊤ := by
      -- The `dμ/dν` density as a real and the `μ`-a.e. chain `log fμ = log r + log fν`.
      set r : ℝ → ℝ := fun x => (μ.rnDeriv ν x).toReal with hr_def
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
          (f := fun x => ENNReal.ofReal (-Real.log (r x)))
          ((Real.measurable_log.comp (μ.measurable_rnDeriv ν).ennreal_toReal).neg
            |>.ennreal_ofReal.aemeasurable)]
        calc (∫⁻ x, μ.rnDeriv ν x * ENNReal.ofReal (-Real.log (r x)) ∂ν)
            ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂ν := by
              refine lintegral_mono_ae ?_
              filter_upwards [μ.rnDeriv_lt_top ν] with x hx
              -- `μ.rnDeriv ν x = ofReal (r x)`, then `ofReal(r)·ofReal(-log r) = ofReal(-r log r) ≤ 1`.
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

**独立 honesty audit 2026-06-08 (fresh subagent, `@residual` 除去の正当性検証 → ok)**: 旧 sorry+
`@residual` 除去は正当。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free
機械確認、transitive sorry 無し)。4-check PASS: `h_ae` は a.e. 収束 input precondition で Fatou
不等式の核 (`lintegral_liminf_le`) を encode せず (非 load-bearing)、Fatou の向きは正部 (負部 0-clamp)
被積分関数列で正しい。@audit:ok -/
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

**独立 honesty audit 2026-06-08 (fresh subagent, proof-done + `hW_ent` 非 load-bearing 主張検証 → ok)**:
4-check PASS。(1) 非循環 — 結論 `h(Q.map W) ≤ h(Q.map (W+V))` は 5 仮説いずれとも非同型、body は
~280 行の genuine 全証明 (`:= h` でない)。(2) 非バンドル — core-reconstruction test: `hW_ent` (W-marginal
有限微分エントロピー) を grant しても単調不等式は出ない (h(W) の有限性のみ、h(W) と h(W+V) の関係を
encode しない) = FAIL = 非 load-bearing。単調性の核 = Case B の per-fibre translate Gibbs (外部
`differentialEntropy_le_cross_entropy`、`@audit:ok`、klDiv≥0 由来の genuine 出口補題) + Tonelli collapse
で body が担う。`hW_ent` は Case B descent (`differentialEntropyExt_of_ac_integrable` の integrability)
+ Case A の `B(ν)<⊤` 供給 (`negPart_negMulLog_conv_single_ne_top` 経由) に消費される finiteness
precondition。(3) 非退化 — Case A の `le_top` は `differentialEntropyExt ν = A−B = ⊤−(有限) = ⊤` を
A(ν)=⊤ (`‖g‖ₑ=A+B=⊤` ∧ B<⊤ の genuine 分解) から建ててからの `EReal.top_sub` (vacuous/exfalso/`0=value`
でない)。(4) sufficiency — 「W a.c. ∧ W⊥V ∧ h(W) 有限 ⟹ h(W)≤h(W+V)」は独立ノイズ加算でエントロピー
増大の古典定理で真。反証試行: `hW_ac` 欠落 → W=Dirac で per-fibre translate `μWz z` が ν に非 a.c. ⟹
Gibbs 崩壊 (`condDistrib_ae_absolutelyContinuous_indep_add` が a.c. genuine 消費) = a.c. は必要 precondition
present。**機械裏取り**: `#print axioms differentialEntropyExt_mono_add_of_integrable` (transient +
`lake env lean`) = `[propext, Classical.choice, Quot.sound]`、sorryAx **非依存**。(i-a) chain rule
`differentialEntropyExt_indep_add_eq_add_klDiv` (sorryAx 保持) を **非継承** (axiom 出力に sorryAx
非出現で genuine 迂回を確認、body も chain rule 不使用 = per-fibre translate Gibbs に置換済)。@audit:ok -/
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

/-- **(2a) helper — truncated W-marginal density a.e. 収束**: `((truncW P W n).map W).rnDeriv vol x).toReal`
は n→∞ で `((P.map W).rnDeriv vol x).toReal` に volume-a.e. 収束。`(truncW P W n).map W = cond (P.map W) Sn`
(`Sn n := {r | |r| ≤ n}`) + `rnDeriv_cond_eq` で `fn_n x = c_n⁻¹ · 1_{Sn n}(x) · fW_enn x` (a.e.)、
`c_n = (P.map W) Sn → 1` (`tendsto_measure_iUnion_atTop`、`⋃ Sn = univ`) + 固定 x で十分大 n で `x ∈ Sn n`。
weak-conv 不使用 (各点極限)。`hW_ac` は a.c. (cond 保存)、regularity precondition。

**独立 honesty audit 2026-06-08 (fresh subagent → ok)**: (B) `hW_ac` は body 未参照 (unused
warning line 1463) = over-hypothesized だが honesty-safe (a.c. 無しでも各点 a.e. 密度収束は cond
公式 + 質量収束で閉じる = より弱い前提で済む、退化定義悪用でなく単なる冗長)。除去可能 (非必須)、
caller 一様性のため残置。(E) weak-conv portmanteau (`tendsto_iff_forall_integral_tendsto` 等) 不使用、
`rnDeriv_cond_eq` + `tendsto_measure_iUnion_atTop` + indicator 各点極限で閉じる (L-Uncond-Y-roi 不発動)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem truncW_map_density_tendsto_ae
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => (((truncW P W n).map W).rnDeriv volume x).toReal) atTop
        (𝓝 (((P.map W).rnDeriv volume x).toReal)) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  -- truncation set in the W-marginal and its mass.
  set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : ∀ n, MeasurableSet (Sn n) := fun n =>
    measurableSet_le measurable_norm measurable_const
  have hSn_mono : Monotone Sn := by
    intro n m hnm r hr
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact le_trans hr this
  have hSn_union : ⋃ n, Sn n = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro r
    obtain ⟨k, hk⟩ := exists_nat_ge |r|
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  set c : ℕ → ℝ≥0∞ := fun n => (P.map W) (Sn n) with hc_def
  -- `c n → 1` (union is everything).
  have hc_lim : Tendsto c atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := P.map W) hSn_mono
    rw [hSn_union, measure_univ] at h
    exact h
  -- `(truncW P W n).map W = cond (P.map W) (Sn n)` for every `n` (direct measure equality).
  have hmap_eq : ∀ n, ((truncW P W n).map W) = ProbabilityTheory.cond (P.map W) (Sn n) := by
    intro n
    set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_meas : MeasurableSet E := hW.abs measurableSet_Iic
    have hE_eq : E = W ⁻¹' (Sn n) := by ext ω; simp [hE_def, hSn_def]
    refine Measure.ext (fun A hA => ?_)
    have hLHS : ((truncW P W n).map W) A = ((P.map W) (Sn n))⁻¹ * (P.map W) (Sn n ∩ A) := by
      rw [Measure.map_apply hW hA, truncW, ProbabilityTheory.cond_apply hE_meas P, hE_eq,
        Measure.map_apply hW (hSn_meas n), Measure.map_apply hW ((hSn_meas n).inter hA),
        Set.preimage_inter]
    have hRHS : (ProbabilityTheory.cond (P.map W) (Sn n)) A
        = ((P.map W) (Sn n))⁻¹ * (P.map W) (Sn n ∩ A) := by
      rw [ProbabilityTheory.cond_apply (hSn_meas n) (P.map W) A]
    rw [hLHS, hRHS]
  -- real-valued mass and its inverse converge to 1.
  set cr : ℕ → ℝ := fun n => (c n).toReal with hcr_def
  have hcr_lim : Tendsto cr atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hc_lim
    simpa [hcr_def, Function.comp] using this
  -- eventually `c n ≠ 0`.
  have hc_ne : ∀ᶠ n in atTop, c n ≠ 0 := by
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hc_lim.eventually_mem h_nhds
  -- the inverse mass (real) converges to 1.
  have hcbar_lim : Tendsto (fun n => ((c n)⁻¹).toReal) atTop (𝓝 1) := by
    have heq : (fun n => (cr n)⁻¹) =ᶠ[atTop] fun n => ((c n)⁻¹).toReal := by
      filter_upwards [hc_ne] with n hn
      rw [hcr_def]; simp only; rw [ENNReal.toReal_inv]
    refine Tendsto.congr' heq ?_
    have : Tendsto (fun n => (cr n)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
      (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcr_lim
    simpa using this
  -- on the tail (`c n ≠ 0`), the cond density formula:
  -- `fn_n =ᵐ (c n)⁻¹ · 1_{Sn n} · μW.rnDeriv vol`.
  have h_rn : ∀ n, c n ≠ 0 → ((truncW P W n).map W).rnDeriv volume
      =ᵐ[volume] fun x => (c n)⁻¹ * (Sn n).indicator ((P.map W).rnDeriv volume) x := by
    intro n hcn
    have hrn := rnDeriv_cond_eq (P.map W) (hSn_meas n) hcn
    rw [hmap_eq n]; exact hrn
  -- assemble: an a.e. set of `x` where (i) all tail density formulas hold and (ii) `μW.rnDeriv x < ⊤`.
  -- Then `fn_n x → fW x`.
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hc_ne
  -- the a.e. set: tail density formulas hold simultaneously (countable conjunction) + finite density.
  have h_all : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, N₀ ≤ n →
      ((truncW P W n).map W).rnDeriv volume x
        = (c n)⁻¹ * (Sn n).indicator ((P.map W).rnDeriv volume) x := by
    rw [ae_all_iff]; intro n
    by_cases hn : N₀ ≤ n
    · filter_upwards [h_rn n (hN₀ n hn)] with x hx _; exact hx
    · filter_upwards with x h; exact absurd h hn
  filter_upwards [h_all, (P.map W).rnDeriv_lt_top volume] with x hx hx_fin
  -- abbreviations.
  set fWe : ℝ≥0∞ := (P.map W).rnDeriv volume x with hfWe_def
  have hfWe_ne : fWe ≠ ⊤ := hx_fin.ne
  -- `x ∈ Sn n` eventually (when `|x| ≤ n`).
  obtain ⟨Nx, hNx⟩ := exists_nat_ge |x|
  -- the tail formula simplifies (on `n ≥ max N₀ Nx`) to `(c n)⁻¹.toReal * fWe.toReal`.
  have hev : ∀ᶠ n in atTop, (((truncW P W n).map W).rnDeriv volume x).toReal
      = ((c n)⁻¹).toReal * fWe.toReal := by
    filter_upwards [Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop Nx] with n hnN₀ hnNx
    have hxSn : x ∈ Sn n := le_trans hNx (by exact_mod_cast hnNx)
    rw [hx n hnN₀, Set.indicator_of_mem hxSn, ENNReal.toReal_mul, ← hfWe_def]
  -- the product `(c n)⁻¹.toReal * fWe.toReal → 1 * fWe.toReal = fWe.toReal`.
  refine Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
  have hprod : Tendsto (fun n => ((c n)⁻¹).toReal * fWe.toReal) atTop (𝓝 (1 * fWe.toReal)) :=
    hcbar_lim.mul tendsto_const_nhds
  simpa using hprod

/-- **(2b) helper — `h(μ) = ⊤ ⟹ A(μ) = ⊤`** (正部 lintegral 発散の抽出)。
`differentialEntropyExt μ = (A:EReal) − (B:EReal) = ⊤` (a.c. 枝) から、`A ≠ ⊤` だと EReal 引き算が
`⊤` になり得ない (`B = ⊤`: `fin − ⊤ = ⊥`、`B ≠ ⊤`: `fin − fin = fin`) ので `A = ⊤`。`B(μ) < ⊤` 不要
(`h = ⊤` だけで `A = ⊤` が follow、より強い形)。

**独立 honesty audit 2026-06-08 (fresh subagent → ok)**: genuine (新規 helper)。`htop : h(μ)=⊤`
から `A=⊤` を EReal 減算規約 (`sub_top`/`top_sub`) の場合分けで抽出、循環/bundling/退化なし。
本 helper の対称形が #1 の `hW_negPart_fin` redundancy (= `h=⊤ ⟹ B≠⊤`) を裏付ける。`#print axioms`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem posPart_lintegral_eq_top_of_diffEntExt_top {μ : Measure ℝ} (hac : μ ≪ volume)
    (htop : differentialEntropyExt μ = ⊤) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume) = ⊤ := by
  rw [differentialEntropyExt_of_ac hac] at htop
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `htop : (A : EReal) - (B : EReal) = ⊤`.  Suppose `A ≠ ⊤`; derive a contradiction.
  by_contra hA
  -- `A` finite ⟹ `(A : EReal) = ((A.toReal : ℝ) : EReal)`, a real coe.
  have hAcoe : (A : EReal) = ((A.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hA).symm
  rcases eq_or_ne B (⊤ : ℝ≥0∞) with hBtop | hBfin
  · -- `B = ⊤`: `(A:EReal) - ⊤ = ⊥ ≠ ⊤`.
    rw [hBtop, EReal.coe_ennreal_top, EReal.sub_top] at htop
    exact absurd htop (by simp)
  · -- `B ≠ ⊤`: difference of two finite reals is finite (`≠ ⊤`).
    have hBcoe : (B : EReal) = ((B.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hBfin).symm
    rw [hAcoe, hBcoe, ← EReal.coe_sub] at htop
    exact (EReal.coe_ne_top _ htop)

/-- **Step 0 helper — `h(μ) = ⊤ ⟹ B(μ) ≠ ⊤`** (負部 lintegral 有限性の抽出、`posPart_…` の対称形)。
`differentialEntropyExt μ = (A:EReal) − (B:EReal) = ⊤` (a.c. 枝) から、`B = ⊤` だと EReal 引き算が
`(A:EReal) − ⊤ = ⊥ ≠ ⊤` (`EReal.sub_top`、`(A:ℝ≥0∞) ≠ ⊥`) ゆえ矛盾、よって `B ≠ ⊤`。これにより
assembly の Step 0 で `hW_top` から `B(P.map W) ≠ ⊤` を導出でき、signature に `hW_negPart_fin` を
足さずに済む (= 無条件性の鍵)。

genuine (新規 helper)。`htop : h(μ)=⊤` から `B ≠ ⊤` を EReal 減算規約の場合分けで抽出、
循環/bundling/退化なし。@residual なし。

**独立 honesty audit 2026-06-08 (fresh subagent, route closure 監査, commit 803e489 → ok)**:
`posPart_…` の genuine 対称形。`hac` は regularity precondition、結論 `B≠⊤` は body の EReal `sub_top`
場合分け (`B=⊤⟹(A:EReal)−⊤=⊥≠⊤=htop` 矛盾) で `htop` から抽出 = 仮説に核を encode せず (非循環・
非バンドル・非退化)。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 独立
機械確認)。@audit:ok -/
theorem negPart_lintegral_ne_top_of_diffEntExt_top {μ : Measure ℝ} (hac : μ ≪ volume)
    (htop : differentialEntropyExt μ = ⊤) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤ := by
  rw [differentialEntropyExt_of_ac hac] at htop
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `htop : (A : EReal) - (B : EReal) = ⊤`.  If `B = ⊤`, then `(A:EReal) - ⊤ = ⊥ ≠ ⊤`.
  intro hBtop
  rw [hBtop, EReal.coe_ennreal_top, EReal.sub_top] at htop
  exact absurd htop (by simp)

/-- **(2c) helper — truncated W-marginal の負部 lintegral の明示上界**: `c_n ≠ 0` のとき
`B(W_n) ≤ ofReal|cbar_n · log cbar_n| + ofReal(cbar_n) · B(W)`、`cbar_n := ((P.map W)(Sn n))⁻¹.toReal`、
`Sn n := {r | |r| ≤ n}`。truncated 密度 `fn = cbar_n · 1_{Sn n} · fW` の `negMulLog_mul` 分解 +
`∫⁻ ofReal(fW) = 1` (確率密度正規化) で得る。`cbar_n → 1` ゆえ B(W_n) を最終的に固定有限値で抑えるための
per-n bound。

**独立 honesty audit 2026-06-08 (fresh subagent → ok)**: genuine (新規 helper)。`hcn` (positive
mass) は cond well-defined の scope = regularity、`hW`/`hW_ac` も regularity。結論 = per-n B 上界の
explicit 式で、仮説に核を encode せず (`negMulLog_mul` 分解 + 確率密度正規化が body で担う)。`#print
axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。NB: docstring 旧版が言及
していた `hW_negPart_fin` は本 helper の signature に**無い** (caller #1 / 単調性側の仮説)。@audit:ok -/
theorem truncW_map_negPart_lintegral_le
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) (n : ℕ)
    (hcn : (P.map W) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
        ∂volume)
      ≤ ENNReal.ofReal (|(((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal
          * Real.log ((((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal)|)
        + ENNReal.ofReal ((((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal)
          * (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
              ∂volume) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  set fW : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hfW_def
  set c : ℝ≥0∞ := (P.map W) Sn with hc_def
  set cbar : ℝ := (c⁻¹).toReal with hcbar_def
  have hcbar_nn : 0 ≤ cbar := ENNReal.toReal_nonneg
  -- `(truncW P W n).map W = cond (P.map W) Sn` and its density.
  have hmap_eq : ((truncW P W n).map W) = ProbabilityTheory.cond (P.map W) Sn := by
    set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_meas : MeasurableSet E := hW.abs measurableSet_Iic
    have hE_eq : E = W ⁻¹' Sn := by ext ω; simp [hE_def, hSn_def]
    refine Measure.ext (fun A hA => ?_)
    have hLHS : ((truncW P W n).map W) A = ((P.map W) Sn)⁻¹ * (P.map W) (Sn ∩ A) := by
      rw [Measure.map_apply hW hA, truncW, ProbabilityTheory.cond_apply hE_meas P, hE_eq,
        Measure.map_apply hW hSn_meas, Measure.map_apply hW (hSn_meas.inter hA),
        Set.preimage_inter]
    have hRHS : (ProbabilityTheory.cond (P.map W) Sn) A = ((P.map W) Sn)⁻¹ * (P.map W) (Sn ∩ A) := by
      rw [ProbabilityTheory.cond_apply hSn_meas (P.map W) A]
    rw [hLHS, hRHS]
  set fn : ℝ → ℝ := fun x => (((truncW P W n).map W).rnDeriv volume x).toReal with hfn_def
  have h_rn : ((truncW P W n).map W).rnDeriv volume
      =ᵐ[volume] fun x => c⁻¹ * Sn.indicator ((P.map W).rnDeriv volume) x := by
    rw [hmap_eq]; exact rnDeriv_cond_eq (P.map W) hSn_meas hcn
  have hfW_meas : Measurable (fun x => ENNReal.ofReal (fW x)) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal
  have hfW_lint : (∫⁻ x, ENNReal.ofReal (fW x) ∂volume) = 1 := by
    have hae_eq : (fun x => ENNReal.ofReal (fW x)) =ᵐ[volume] (P.map W).rnDeriv volume := by
      filter_upwards [(P.map W).rnDeriv_ne_top volume] with x hx
      rw [hfW_def]; exact ENNReal.ofReal_toReal hx
    rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hW_ac, measure_univ]
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
      show -(Real.negMulLog (cbar * fW x))
        = cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))
      rw [Real.negMulLog_mul cbar (fW x)]
      ring_nf
      rw [Real.negMulLog]
      ring
    · rw [Set.indicator_of_notMem hxs (f := (P.map W).rnDeriv volume),
        Set.indicator_of_notMem hxs
          (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x))))]
      simp [Real.negMulLog]
  rw [hfn_def] at *
  rw [show (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
      ∂volume)
    = ∫⁻ x, ENNReal.ofReal (Sn.indicator
        (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) ∂volume from
    lintegral_congr_ae h_int_eq]
  -- Bound the indicator integrand by two finite-integral pieces (`≤`, then evaluate).
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
  have hnegm_meas : Measurable (fun x => ENNReal.ofReal (-(Real.negMulLog (fW x)))) :=
    ((Real.continuous_negMulLog.measurable.comp
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).neg).ennreal_ofReal
  have hg1_meas : Measurable
      (fun x => ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)) :=
    measurable_const.mul hfW_meas
  calc (∫⁻ x, ENNReal.ofReal (Sn.indicator
          (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) ∂volume)
      ≤ ∫⁻ x, (ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)
          + ENNReal.ofReal cbar * ENNReal.ofReal (-(Real.negMulLog (fW x)))) ∂volume :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (|cbar * Real.log cbar|) + ENNReal.ofReal cbar
          * (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (fW x))) ∂volume) := by
        rw [lintegral_add_left hg1_meas, lintegral_const_mul _ hfW_meas, hfW_lint, mul_one,
          lintegral_const_mul _ hnegm_meas]

/-- **W-marginal の ⊤-divergence** (route (d'') 専用、⊤ ケースに縮小): `h(W) = ⊤` のとき
`h(W_n) → ⊤`、`W_n := truncW P W n` (= `P` を W-事象 `{|W| ≤ n}` で条件付けた compact-support 近似)。

**スコープ縮小 (判断ログ6)**: 旧版は任意 `h(W)` の full `Tendsto … (𝓝 (h(W)))` だったが、
これは有限ケースで reverse-Fatou (`≥` 方向) を要し over-scoped。route (d'') が実際に必要とするのは
⊤ ケースのみ (gateway ⊤ 枝の closure で per-n 単調性との squeeze に使う発散) なので、結論を
`𝓝 (⊤ : EReal)` に固定し finite ケースを切り落とす。LSC/Fatou は `≤` しか出さないが、⊤ への発散は
`liminf = ⊤` から `Tendsto … ⊤` が一発で出るため (`eventually_lt_of_lt_liminf` + `ENNReal.tendsto_nhds_top`)
極限と相性が良い。

**証明の骨格 (3 段、weak-conv 不使用)**:
1. **density a.e. 収束** `fn_n → fW` a.e.(volume): `(truncW P W n).map W = cond (P.map W) Sn`
   (`Sn n := {r | |r| ≤ n}`、`hQW_eq` 同型) → `rnDeriv_cond_eq` で `fn_n x = c_n⁻¹.toReal · 1_{Sn n}(x) · fW x`、
   `c_n = (P.map W) Sn`。n→∞: `c_n → 1` (`tendsto_measure_iUnion_atTop`、`⋃ Sn = univ`) ゆえ
   `c_n⁻¹.toReal → 1`、各固定 x で十分大 n で `x ∈ Sn n` ゆえ `1_{Sn n}(x) → 1`、積 → `fW x`。各点極限で弱収束でない。
2. **`A(P.map W) = ⊤`**: `h(P.map W) = A − B = ⊤` (EReal) から `A = ⊤` (EReal の `(A:EReal) − (B:EReal) = ⊤`
   は `A ≠ ⊤` だと不可能、場合分けで `A(P.map W) = ⊤`)。`B(P.map W) < ⊤` 不要 (helper はより強い形)。
3. **合成**: Fatou helper `differentialEntropyExt_posPart_le_liminf_of_ae_tendsto` (1 を h_ae に渡す) で
   `A(P.map W) ≤ liminf A(Q_n.map W)` → `A(P.map W)=⊤` ⟹ `liminf A(Q_n.map W) = ⊤` (`top_le_iff`) ⟹
   `A(Q_n.map W) → ⊤` (ℝ≥0∞ liminf=⊤ ⟹ tendsto ⊤)。+ `B(Q_n.map W)` 有界 (`hBn_fin` 分解、`cbar→1`
   ゆえ eventually 一様有界) ⟹ `h(Q_n.map W) = A−B → ⊤` (EReal、A→⊤ かつ B 有界)。

仮説は全て regularity (非 load-bearing): `hW`/`hW_ac` は可測/絶対連続、`hW_negPart_fin` (= `B(W) < ⊤`)
は h(W) 負部有限性 (2 の `⊤−⊤` 不定形回避 + 3 の B 有界化に必要)、`hW_top` は ⊤-divergence の前提
(結論の発散先 ⊤ を grant する precondition であって発散の核を encode しない)。

**proof-done (Phase 3、0 sorry)**: 上記 3 段を helper `truncW_map_density_tendsto_ae` (1) /
`posPart_lintegral_eq_top_of_diffEntExt_top` (2) / `differentialEntropyExt_posPart_le_liminf_of_ae_tendsto`
(Fatou) / `truncW_map_negPart_lintegral_le` (B 有界化) で組立、最終 EReal Tendsto は
`EReal.tendsto_nhds_top_iff_real` で `∀ M, eventually M < A_n − B_n`。weak-convergence portmanteau
(`tendsto_iff_forall_integral_tendsto` 等) は使わず density a.e. 収束 (finitary) のみで閉じる
(L-Uncond-Y-roi 不発動)。

**独立 honesty audit 2026-06-08 (fresh subagent, proof-done 主張検証 → ok)**: A〜E 全 PASS。
(A) **`hW_negPart_fin` = regularity (非 load-bearing) かつ redundant**: B(W)<⊤ を grant しても
結論 `h(W_n)→⊤` は出ない (核は body の Fatou + posPart-⊤ lift、core-reconstruction FAIL) = 非
load-bearing。body では `C:=1+2·Bμ` 有限化 + #5 の per-n B-bound で genuine 消費 = regularity
precondition として生きている。**さらに redundant**: `hW_top : h(P.map W)=⊤` が EReal 減算規約
(`EReal.sub_top : x-⊤=⊥`、`EReal.top_sub : ⊤-x=⊤ (x≠⊤)`、機械確認) 上 B(W)<⊤ を含意する
(`A-B=⊤` ⟹ A=⊤ ∧ B≠⊤、#4 と対称の抽出)。除去可能 (非必須、別タスク)。honesty 上は無害。
(B) line ~1463 unused `hW_ac` は #3 (density helper) のもの、本定理の `hW_ac` は genuine 消費。
(C) rescope (full Tendsto → ⊤ 専用) honesty-safe: 結論を弱める方向、唯一の consumer = Phase 4
⊤ 枝 (`_top_of_indep_add_unconditional`) が `𝓝 ⊤` のみ要求、偽の含意隠蔽なし。(D) `#print axioms`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。(E) weak-conv portmanteau 不使用
(density a.e. 収束 finitary のみ、L-Uncond-Y-roi 不発動)。@audit:ok -/
theorem differentialEntropyExt_truncW_tendsto_top
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume)
    (hW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (⊤ : EReal)) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  -- Abbreviations for the positive / negative parts of `Q_n.map W := (truncW P W n).map W`.
  set μW : Measure ℝ := P.map W with hμW_def
  set A : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
      ∂volume with hB_def
  -- each truncated W-marginal is a.c. (`cond` preserves a.c.).
  have hQac : ∀ n, ((truncW P W n).map W) ≪ volume := by
    intro n
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [truncW]; exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- **Step (2b): `A(μW) = ⊤`** (positive-part divergence from `h(μW) = ⊤`, `B(μW) < ⊤`).
  have hA_top : (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μW.rnDeriv volume x).toReal)) ∂volume) = ⊤ :=
    posPart_lintegral_eq_top_of_diffEntExt_top hW_ac hW_top
  -- **Step (2a)+(2c): Fatou ⟹ `liminf A = ⊤`**.
  have hfatou := differentialEntropyExt_posPart_le_liminf_of_ae_tendsto μW
    (fun n => (truncW P W n).map W)
    (truncW_map_density_tendsto_ae W P hW hW_ac)
  -- `⊤ = A(μW) ≤ liminf A` ⟹ `liminf A = ⊤`.
  have hliminf_top : Filter.liminf A atTop = ⊤ := by
    rw [hA_def]
    rw [hA_top] at hfatou
    exact top_le_iff.mp hfatou
  -- `A n → ⊤` in ℝ≥0∞ (liminf = ⊤ ⟹ tendsto ⊤).
  have hA_tendsto : Tendsto A atTop (𝓝 (⊤ : ℝ≥0∞)) := by
    apply ENNReal.tendsto_nhds_top
    intro k
    have hk_lt : (k : ℝ≥0∞) < Filter.liminf A atTop := by rw [hliminf_top]; exact ENNReal.coe_lt_top
    exact Filter.eventually_lt_of_lt_liminf hk_lt
  -- **`B n` eventually bounded by a fixed finite constant `C`.**
  -- `C := 1 + 2 * B(μW)` (finite since `B(μW) = hW_negPart_fin < ⊤`).
  set Bμ : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μW.rnDeriv volume x).toReal))) ∂volume with hBμ_def
  set C : ℝ≥0∞ := 1 + 2 * Bμ with hC_def
  have hC_fin : C ≠ ⊤ := by
    rw [hC_def]
    refine ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) hW_negPart_fin⟩
  have hB_bound : ∀ᶠ n in atTop, B n ≤ C := by
    -- mass of the truncation set and its inverse (real) both → 1.
    set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
    have hSn_mono : Monotone Sn := by
      intro p q hpq r hr
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      exact le_trans hr this
    have hSn_union : ⋃ k, Sn k = Set.univ := by
      rw [Set.eq_univ_iff_forall]; intro r
      obtain ⟨k, hk⟩ := exists_nat_ge |r|
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    set cc : ℕ → ℝ≥0∞ := fun n => μW (Sn n) with hcc_def
    have hcc_lim : Tendsto cc atTop (𝓝 1) := by
      have h := tendsto_measure_iUnion_atTop (μ := μW) hSn_mono
      rw [hSn_union, measure_univ] at h
      exact h
    have hcc_ne : ∀ᶠ n in atTop, cc n ≠ 0 := by
      have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
      exact hcc_lim.eventually_mem h_nhds
    -- inverse-mass (real) `cbar n := (cc n)⁻¹.toReal → 1`.
    have hcbar_lim : Tendsto (fun n => ((cc n)⁻¹).toReal) atTop (𝓝 1) := by
      have hcr_lim : Tendsto (fun n => (cc n).toReal) atTop (𝓝 1) := by
        have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hcc_lim
        simpa [Function.comp] using this
      have heq : (fun n => ((cc n).toReal)⁻¹) =ᶠ[atTop] fun n => ((cc n)⁻¹).toReal := by
        filter_upwards [hcc_ne] with n hn; rw [ENNReal.toReal_inv]
      refine Tendsto.congr' heq ?_
      have : Tendsto (fun n => ((cc n).toReal)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
        (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcr_lim
      simpa using this
    -- eventually `cbar n ≤ 2` and `|cbar n · log (cbar n)| ≤ 1`.
    have hcbar_le : ∀ᶠ n in atTop, ((cc n)⁻¹).toReal ≤ 2 :=
      hcbar_lim.eventually_le_const (by norm_num : (1 : ℝ) < 2)
    have hlog_le : ∀ᶠ n in atTop,
        |((cc n)⁻¹).toReal * Real.log (((cc n)⁻¹).toReal)| ≤ 1 := by
      -- `t ↦ |t · log t|` is continuous and `→ 0` at `1` (`log 1 = 0`); so eventually `≤ 1`.
      have hcont : Tendsto (fun n => |((cc n)⁻¹).toReal * Real.log (((cc n)⁻¹).toReal)|)
          atTop (𝓝 |(1 : ℝ) * Real.log 1|) := by
        apply Tendsto.abs
        exact (hcbar_lim.mul ((Real.continuousAt_log (by norm_num)).tendsto.comp hcbar_lim))
      rw [Real.log_one, mul_zero, abs_zero] at hcont
      exact hcont.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hcc_ne, hcbar_le, hlog_le] with n hcn hcbar2 hlog1
    -- combine the per-`n` bound with the two eventual estimates.
    have hbnd := truncW_map_negPart_lintegral_le W P hW hW_ac n hcn
    calc B n
        ≤ ENNReal.ofReal (|((μW (Sn n))⁻¹).toReal * Real.log (((μW (Sn n))⁻¹).toReal)|)
            + ENNReal.ofReal (((μW (Sn n))⁻¹).toReal) * Bμ := hbnd
      _ ≤ 1 + 2 * Bμ := by
          refine add_le_add ?_ ?_
          · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlog1
          · refine mul_le_mul' ?_ (le_refl Bμ)
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
            exact ENNReal.ofReal_le_ofReal hcbar2
      _ = C := by rw [hC_def]
  -- **Final EReal Tendsto** via `tendsto_nhds_top_iff_real`.
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  -- coe `A n → ⊤` to EReal.
  have hAE_tendsto : Tendsto (fun n => ((A n : EReal))) atTop (𝓝 (⊤ : EReal)) := by
    have : Tendsto (fun n => ((A n : ℝ≥0∞) : EReal)) atTop (𝓝 ((⊤ : ℝ≥0∞) : EReal)) :=
      (continuous_coe_ennreal_ereal.tendsto _).comp hA_tendsto
    rwa [EReal.coe_ennreal_top] at this
  -- eventually `(M + C.toReal : EReal) < A n`.
  have hev_A : ∀ᶠ n in atTop, ((M + C.toReal : ℝ) : EReal) < (A n : EReal) := by
    rw [EReal.tendsto_nhds_top_iff_real] at hAE_tendsto
    exact hAE_tendsto (M + C.toReal)
  -- combine with the `B`-bound and a.c. expansion of `differentialEntropyExt`.
  filter_upwards [hev_A, hB_bound] with n hAn hBn
  -- expand `differentialEntropyExt (Q_n.map W) = (A n : EReal) - (B n : EReal)`.
  rw [differentialEntropyExt_of_ac (hQac n)]
  show ((M : ℝ) : EReal) < (A n : EReal) - (B n : EReal)
  -- `(B n : EReal) ≤ (C.toReal : EReal)`.
  have hBn_fin : B n ≠ ⊤ := ne_top_of_le_ne_top hC_fin hBn
  have hBn_le : (B n : EReal) ≤ ((C.toReal : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal hBn_fin]
    exact_mod_cast (ENNReal.toReal_le_toReal hBn_fin hC_fin).mpr hBn
  -- `M < A n - B n` ⟸ `M + B n < A n` ⟸ `M + C.toReal < A n` and `B n ≤ C.toReal`.
  rw [EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ennreal_ne_bot _))
    (Or.inr (EReal.coe_ne_bot _))]
  calc ((M : ℝ) : EReal) + (B n : EReal)
      ≤ ((M : ℝ) : EReal) + ((C.toReal : ℝ) : EReal) := add_le_add (le_refl _) hBn_le
    _ = ((M + C.toReal : ℝ) : EReal) := by rw [← EReal.coe_add]
    _ < (A n : EReal) := hAn

/-- **Step-0 helper for the ⊤-branch assembly — `B(ν_n) ≠ ⊤`** (negative part of the truncated sum
law). `ν_n := (truncW P W n).map (W+V)`. Decomposes `ν_n = (Q_n.map W) ∗ (Q_n.map V)` (independence
preserved under conditioning on the `W`-event `{|W| ≤ n}`), bounds `B(Q_n.map W) ≠ ⊤` via the per-n
explicit bound `truncW_map_negPart_lintegral_le` (finite since `B(W) < ⊤` and `c_n ≠ 0`), then lifts
to the sum law via the single-component finiteness `negPart_negMulLog_conv_single_ne_top`.

genuine (新規 helper)。`hW`/`hV`/`hWV`/`hW_ac`/`hBW`/`hn` は全て regularity precondition
(結論 = 截断和周辺負部の有限性 を encode せず)。@residual なし。

**独立 honesty audit 2026-06-08 (fresh subagent, route closure 監査, commit 803e489 → ok)**:
非循環・非バンドル・非退化 全 PASS。6 仮説は可測/独立/絶対連続/`B(W)<⊤`/positive-mass = 全 regularity
precondition (grant しても結論 `B(ν_n)≠⊤` は出ない、core = body の独立保存 conditioning + per-n explicit
bound `truncW_map_negPart_lintegral_le` + single-component lift `negPart_negMulLog_conv_single_ne_top`)。
sufficiency — `hBW` (=B(W)<⊤) + cond の per-n bound で genuine に follow。`#print axioms` (in-file
transient + `lake env lean`) = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 独立機械確認)。
@audit:ok -/
private theorem negPart_lintegral_map_truncW_add_ne_top
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hBW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (n : ℕ) (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map (fun ω => W ω + V ω)).rnDeriv
        volume x).toReal))) ∂volume) ≠ ⊤ := by
  classical
  set Q : Measure Ω := truncW P W n with hQ_def
  haveI hQ_prob : IsProbabilityMeasure Q := by
    rw [hQ_def, truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
  haveI hQW_prob : IsProbabilityMeasure (Q.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hQV_prob : IsProbabilityMeasure (Q.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  -- W stays a.c. under conditioning.
  have hW_ac_Q : (Q.map W) ≪ volume := by
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [hQ_def, truncW]
    exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- W ⊥ V under `Q` (conditioning on a `W`-event preserves independence).
  have hE_meas : MeasurableSet {ω : Ω | |W ω| ≤ (n : ℝ)} := hW.abs measurableSet_Iic
  set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
  have hindep : IndepFun W V Q := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have hEW : E ∩ W ⁻¹' s = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := by
      ext ω; simp [hE_def, Set.mem_inter_iff, and_comm]
    have hIcc_meas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      (_root_.continuous_abs.measurable measurableSet_Iic)
    have hAW : MeasurableSet ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := hIcc_meas.inter hs
    rw [hQ_def, truncW, cond_apply hE_meas, cond_apply hE_meas, cond_apply hE_meas]
    have hjoint : E ∩ (W ⁻¹' s ∩ V ⁻¹' t) = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t := by
      rw [← Set.inter_assoc, hEW]
    rw [hjoint, hEW]
    have hfac1 : P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t)
        = P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s)) * P (V ⁻¹' t) :=
      hWV.measure_inter_preimage_eq_mul _ _ hAW ht
    have hEV : E ∩ V ⁻¹' t = W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} ∩ V ⁻¹' t := by
      ext ω; simp [hE_def]
    have hfac2 : P (E ∩ V ⁻¹' t) = P E * P (V ⁻¹' t) := by
      rw [hEV, hWV.measure_inter_preimage_eq_mul _ _ hIcc_meas ht, hE_def]; rfl
    rw [hfac1, hfac2]
    have hPE_ne : P E ≠ 0 := by rw [hE_def]; exact hn
    have hPE_ne_top : P E ≠ ∞ := measure_ne_top P E
    have hcancel : (P E)⁻¹ * (P E * P (V ⁻¹' t)) = P (V ⁻¹' t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hPE_ne hPE_ne_top, one_mul]
    rw [hcancel]; ring
  -- the sum law equals the convolution of the marginals.
  have hsum_conv : Q.map (fun ω => W ω + V ω) = (Q.map W) ∗ (Q.map V) := by
    have := hindep.map_add_eq_map_conv_map hW hV
    simpa [Pi.add_apply] using this
  -- `B(Q.map W) ≠ ⊤` via the explicit per-n bound (finite under `B(W) < ⊤` and `c_n ≠ 0`).
  have hcn' : (P.map W) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0 := by
    have hmeas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      _root_.continuous_abs.measurable measurableSet_Iic
    rw [Measure.map_apply hW hmeas]
    have : W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} = {ω | |W ω| ≤ (n : ℝ)} := by ext ω; simp
    rw [this]; exact hn
  have hBQW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := by
    have hbnd := truncW_map_negPart_lintegral_le W P hW hW_ac n hcn'
    rw [← hQ_def] at hbnd
    refine ne_top_of_le_ne_top ?_ hbnd
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBW⟩
  -- lift to the sum law.
  rw [hsum_conv]
  exact negPart_negMulLog_conv_single_ne_top (Q.map W) (Q.map V) hW_ac_Q hBQW

/-- **gateway ⊤ 枝 (無条件)**: `h(W) = ⊤ ⟹ h(W+V) = ⊤`、無条件版② (i-a) を bypass。
per-n 単調性 `h(W_n) ≤ h(W_n + V)` (`differentialEntropyExt_mono_add_truncW`) と `h(W_n) → ⊤`
(`differentialEntropyExt_truncW_tendsto_top`、⊤ ケース専用に縮小済) を組み、
`h(W_n + V) ≥ h(W_n) → ⊤` で `h(W+V) = ⊤`。
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

**route (d'') assembly proof-done (Phase 4、0 sorry、2026-06-08)**: body は以下を組む。
Step 0 — regularity: `ν = (P.map W) ∗ (P.map V)` (`IndepFun.map_add_eq_map_conv_map`)、
`B(P.map W) ≠ ⊤` (新 helper `negPart_lintegral_ne_top_of_diffEntExt_top` で `hW_top` から導出 =
signature に `hW_negPart_fin` を足さない鍵)、`ν ≪ volume` (conv の a.c. left-factor)、`B(ν) ≠ ⊤`
(`negPart_negMulLog_conv_single_ne_top` un-truncated 適用)。Step 1 — `h(ν_n) → ⊤`: Phase 3
`differentialEntropyExt_truncW_tendsto_top` (`h(Q_n.map W) → ⊤`) + per-n 単調性
`differentialEntropyExt_mono_add_truncW` の squeeze (EReal `tendsto_nhds_top_iff_real`)。
Steps 2–4 — `A(ν) = ⊤` by_contra: per-n Gibbs `ennreal_gibbs_rearranged` で
`h(ν_n) ≤ (crossPos ν_n ν : EReal)`、atom 1 測度 domination (`ν_n ≤ c_n⁻¹ • ν`) で
`crossPos ν_n ν ≤ c_n⁻¹ · A(ν) ≤ 2·A(ν)` (eventually `c_n⁻¹ ≤ 2`)、`A(ν) ≠ ⊤` 仮定下で
`h(ν_n) ≤ (2·A(ν) : EReal)` (有限) が `h(ν_n) → ⊤` と矛盾。`A(ν) = ⊤` + `B(ν) ≠ ⊤` →
`h(ν) = ⊤ − fin = ⊤` (`EReal.top_sub_coe`)。

`#print axioms differentialEntropyExt_top_of_indep_add_unconditional`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認、olean refresh 後)。**核心: (i-a)
`differentialEntropyExt_indep_add_eq_add_klDiv` の sorryAx を継承しない** (truncation 近似で無条件版② を
bypass、axiom 出力に sorryAx 不在で機械裏取り)。

honesty: (a) load-bearing hyp なし (`hW`/`hV`/`hWV`/`hW_ac` は regularity、`hW_top` は ⊤ 枝の場合分け
precondition で結論核 = h(W+V)=⊤ を encode せず)、(b) `_unconditional` 命名 = NOT name-laundering
(open load-bearing hyp も完成偽装 sorry-body も無し、proof-done 達成済)。(4) sufficiency — `h(W)=⊤`
+ 無条件単調性で `h(W+V)=⊤` は正しい含意 (反例なし)。

**独立 honesty audit 2026-06-08 (fresh subagent, route 完了 closure 監査, commit 803e489 → ok)**:
4-check 全 PASS。(1) 非循環 — 結論 `h(P.map(W+V))=⊤` は 5 仮説のいずれとも非同型、body は
genuine 全証明 (`:= h` でない)。(2) 非バンドル (core-reconstruction) — `hW`/`hV`/`hWV`/`hW_ac` は
可測/独立/絶対連続、`hW_top` (h(W)=⊤) は ⊤ 枝 case-split precondition。5 仮説を全 grant しても
結論 (= h(W+V)=⊤) の核は出ない: 核 = 無条件単調性 `h(W_n)≤h(W_n+V)` (#3 `differentialEntropyExt_
mono_add_truncW`, `@audit:ok`) + `h(W_n)→⊤` (Phase 3, `@audit:ok`) で body が担う = 非 load-bearing。
(3) 非退化 — 結論の `h(ν)=⊤` は `A(ν)=⊤` (by_contra + per-n Gibbs + 測度 domination で genuine 確立)
+ `B(ν)≠⊤` から `⊤−fin=⊤` (`EReal.top_sub_coe`) で建てる genuine EReal ⊤ 利用、vacuous/exfalso でない。
(4) **sufficiency (反例試行) — 含意 TRUE、反例構成不能**: 退化境界 3 通り試行 — V Dirac (W+V=W+c シフト,
h 不変→⊤)、V 独立 a.c. (h(W+V)≥h(W)=⊤)、V atom/特異 (a.c. W との conv は a.c.、⊤-entropy シフト
混合は⊤ 維持)。いずれも `h(W+V)=⊤` が生き、`h(W+V)≠⊤` 反例なし。核は無条件単調性 (任意独立 V で成立,
V a.c. 不要) = 「独立ノイズ加算は微分エントロピーを減らさない」、`h(W)=⊤⟹h(W+V)=⊤` は genuine 含意。
under-hypothesized でない。**name-laundering 最終判定 = NOT laundering**: signature は既存
`differentialEntropyExt_top_of_indep_add` (EPIUncondMonotone.lean:153) と完全同一仮説群・同一結論、
新規 hyp なし。`_unconditional` は「(i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` の sorryAx を
継承しない別 route (truncation 近似)」という proof-route 主張で正当 (open load-bearing hyp も偽装
sorry-body も無し)。**機械裏取り (olean refresh 後)**: `#print axioms differentialEntropyExt_top_of_
indep_add_unconditional` = `[propext, Classical.choice, Quot.sound]` (sorryAx **非依存**)、対して
`#print axioms differentialEntropyExt_indep_add_eq_add_klDiv` (i-a) = `sorryAx` 保持。**非継承を独立
再確認**: 同 commit で両 module を `lake build` リフレッシュ後 fresh `lake env lean` で確認、stale-olean
artifact でなく truncation route が genuine に無条件版② chain rule を迂回。@audit:ok -/
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  classical
  -- ν := P.map(W+V),  ν_n := (truncW P W n).map(W+V),  c_n := P{|W| ≤ n}.
  set ν : Measure ℝ := P.map (fun ω => W ω + V ω) with hν_def
  haveI hμW_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hμV_prob : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  haveI hν_prob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
  -- **Step 0 — regularity.**
  -- ν = (P.map W) ∗ (P.map V) (independence).
  have hconv : ν = (P.map W) ∗ (P.map V) := by
    rw [hν_def]; exact hWV.map_add_eq_map_conv_map hW hV
  -- B(P.map W) ≠ ⊤ from h(W) = ⊤  (Step-0 helper, avoids adding a hypothesis to the signature).
  have hBW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := negPart_lintegral_ne_top_of_diffEntExt_top hW_ac hW_top
  -- ν ≪ volume (convolution with an a.c. left factor is a.c.).
  have hν_ac : ν ≪ volume := by
    rw [hconv, conv_eq_withDensity_translate_average (P.map W) (P.map V) hW_ac]
    exact withDensity_absolutelyContinuous _ _
  -- B(ν) ≠ ⊤ (single-component negative-part finiteness of the sum law).
  have hBν : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume)
      ≠ ⊤ := by
    rw [hconv]
    exact negPart_negMulLog_conv_single_ne_top (P.map W) (P.map V) hW_ac hBW
  -- **Step 1 — `h(ν_n) → ⊤`** (squeeze: per-n monotone below a tendsto-⊤ sequence).
  -- Phase 3: `h(Q_n.map W) → ⊤`.
  have hW_tendsto : Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (⊤ : EReal)) :=
    differentialEntropyExt_truncW_tendsto_top W P hW hW_ac hBW hW_top
  -- eventually positive mass `c_n ≠ 0`.
  have hcn_ev : ∀ᶠ n : ℕ in atTop, P {ω | |W ω| ≤ (n : ℝ)} ≠ 0 := by
    set E : ℕ → Set Ω := fun n => {ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_mono : Monotone E := by
      intro p q hpq ω hω
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      exact le_trans hω this
    have hE_union : ⋃ k, E k = Set.univ := by
      rw [Set.eq_univ_iff_forall]; intro ω
      obtain ⟨k, hk⟩ := exists_nat_ge |W ω|
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 1) := by
      have h := tendsto_measure_iUnion_atTop (μ := P) hE_mono
      rw [hE_union, measure_univ] at h
      exact h
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hlim.eventually_mem h_nhds
  -- per-n monotone (eventually): `h(Q_n.map W) ≤ h(ν_n)`.
  have hmono_ev : ∀ᶠ n in atTop,
      differentialEntropyExt ((truncW P W n).map W)
        ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
    filter_upwards [hcn_ev] with n hn
    exact differentialEntropyExt_mono_add_truncW W V P hW hV hWV hW_ac hBW n hn
  -- squeeze to get `h(ν_n) → ⊤`.
  have hνn_tendsto : Tendsto (fun n => differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)))
      atTop (𝓝 (⊤ : EReal)) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    rw [EReal.tendsto_nhds_top_iff_real] at hW_tendsto
    filter_upwards [hW_tendsto M, hmono_ev] with n hMn hmn
    exact lt_of_lt_of_le hMn hmn
  -- **Steps 2–4 — `A(ν) = ⊤`** (by_contra + per-n Gibbs + measure domination).
  set Aν : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume
    with hAν_def
  have hAν_top : Aν = ⊤ := by
    by_contra hAν_ne
    -- eventually `c_n⁻¹ ≤ 2`.
    have hcinv_ev : ∀ᶠ n : ℕ in atTop, ((P {ω | |W ω| ≤ (n : ℝ)})⁻¹).toReal ≤ 2 := by
      set E : ℕ → Set Ω := fun n => {ω | |W ω| ≤ (n : ℝ)} with hE_def
      have hE_mono : Monotone E := by
        intro p q hpq ω hω
        have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
        exact le_trans hω this
      have hE_union : ⋃ k, E k = Set.univ := by
        rw [Set.eq_univ_iff_forall]; intro ω
        obtain ⟨k, hk⟩ := exists_nat_ge |W ω|
        exact Set.mem_iUnion.2 ⟨k, hk⟩
      have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 1) := by
        have h := tendsto_measure_iUnion_atTop (μ := P) hE_mono
        rw [hE_union, measure_univ] at h
        exact h
      -- `(P (E n))⁻¹.toReal → 1`.
      have hcinv_lim : Tendsto (fun n => ((P (E n))⁻¹).toReal) atTop (𝓝 1) := by
        have hr_lim : Tendsto (fun n => (P (E n)).toReal) atTop (𝓝 1) := by
          have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hlim
          simpa [Function.comp] using this
        have heq : (fun n => ((P (E n)).toReal)⁻¹) =ᶠ[atTop] fun n => ((P (E n))⁻¹).toReal := by
          filter_upwards [hcn_ev] with n hn; rw [ENNReal.toReal_inv]
        refine Tendsto.congr' heq ?_
        have : Tendsto (fun n => ((P (E n)).toReal)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
          (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr_lim
        simpa using this
      exact hcinv_lim.eventually_le_const (by norm_num : (1 : ℝ) < 2)
    -- the finite EReal upper bound `(2 * Aν : EReal)`.
    -- eventually `h(ν_n) ≤ (2 * Aν : EReal)`.
    have hub : ∀ᶠ n in atTop,
        differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω))
          ≤ ((2 * Aν : ℝ≥0∞) : EReal) := by
      filter_upwards [hcn_ev, hcinv_ev] with n hn hcinv
      set νn : Measure ℝ := (truncW P W n).map (fun ω => W ω + V ω) with hνn_def
      set cinv : ℝ≥0∞ := (P {ω | |W ω| ≤ (n : ℝ)})⁻¹ with hcinv_def
      -- mass `c_n ∈ (0, 1]` so `cinv ∈ [1, ⊤)`.
      have hcn_ne_top : (P {ω | |W ω| ≤ (n : ℝ)}) ≠ ⊤ := measure_ne_top _ _
      have hcinv_top : cinv ≠ ⊤ := by
        rw [hcinv_def]; exact ENNReal.inv_ne_top.mpr hn
      have hcinv_le_two : cinv ≤ (2 : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hcinv_top, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
        exact ENNReal.ofReal_le_ofReal hcinv
      -- measure domination `ν_n ≤ cinv • ν` (atom 1).
      have hdom : νn ≤ cinv • ν := by
        rw [hνn_def, hcinv_def, hν_def]
        exact map_truncW_add_le_smul_map_add W V P hW hV n hn
      -- `ν_n ≪ ν ≪ volume`.
      have hνn_ν : νn ≪ ν := by
        rw [hνn_def, hν_def]
        exact map_truncW_add_absolutelyContinuous_map_add W V P hW hV n hn
      have hνn_ac : νn ≪ volume := hνn_ν.trans hν_ac
      haveI hQ_prob : IsProbabilityMeasure (truncW P W n) := by
        rw [truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
      haveI hνn_prob : IsProbabilityMeasure νn := by
        rw [hνn_def]
        exact Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
      -- `B(ν_n) ≠ ⊤`.
      have hBνn : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((νn.rnDeriv volume x).toReal)))
          ∂volume) ≠ ⊤ := by
        rw [hνn_def]
        exact negPart_lintegral_map_truncW_add_ne_top W V P hW hV hWV hW_ac hBW n hn
      -- `crossNeg ν_n ν ≤ cinv * crossNeg ν ν = cinv * B(ν)`, hence `≠ ⊤`.
      have hCNνn_dom : crossNeg νn ν ≤ cinv * crossNeg ν ν := by
        rw [crossNeg, crossNeg]
        calc (∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂νn)
            ≤ ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂(cinv • ν) :=
              lintegral_mono' hdom (le_refl _)
          _ = cinv * ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂ν := by
              rw [lintegral_smul_measure]; rfl
      have hCNν_eq : crossNeg ν ν
          = ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume :=
        crossNeg_self ν hν_ac
      have hCNνn_fin : crossNeg νn ν ≠ ⊤ := by
        refine ne_top_of_le_ne_top ?_ hCNνn_dom
        exact ENNReal.mul_ne_top hcinv_top (by rw [hCNν_eq]; exact hBν)
      -- Gibbs (consumer form): `A(ν_n) + crossNeg ≤ crossPos + B(ν_n)`.
      have hgibbs := ennreal_gibbs_rearranged hνn_ac hν_ac hνn_ν hBνn hCNνn_fin
      -- `A(ν_n) ≤ crossPos ν_n ν + B(ν_n)`  (drop the nonneg `crossNeg`).
      have hA_le : (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((νn.rnDeriv volume x).toReal)) ∂volume)
          ≤ crossPos νn ν
            + ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((νn.rnDeriv volume x).toReal))) ∂volume :=
        le_trans (le_add_right (le_refl _)) hgibbs
      -- `h(ν_n) = (A(ν_n):EReal) - (B(ν_n):EReal) ≤ (crossPos ν_n ν : EReal)`.
      have hh_le : differentialEntropyExt νn ≤ ((crossPos νn ν : ℝ≥0∞) : EReal) := by
        rw [differentialEntropyExt_of_ac hνn_ac]
        rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ennreal_ne_bot _))
          (Or.inl ((EReal.coe_ennreal_eq_top_iff).not.mpr hBνn))]
        rw [← EReal.coe_ennreal_add]
        exact_mod_cast hA_le
      -- domination of the positive cross-entropy: `crossPos ν_n ν ≤ cinv * Aν ≤ 2 * Aν`.
      have hCPνn_dom : crossPos νn ν ≤ (2 : ℝ≥0∞) * Aν := by
        have hstep : crossPos νn ν ≤ cinv * crossPos ν ν := by
          rw [crossPos, crossPos]
          calc (∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂νn)
              ≤ ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂(cinv • ν) :=
                lintegral_mono' hdom (le_refl _)
            _ = cinv * ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂ν := by
                rw [lintegral_smul_measure]; rfl
        have hCPν_eq : crossPos ν ν = Aν := by
          rw [hAν_def]; exact crossPos_self ν hν_ac
        calc crossPos νn ν ≤ cinv * crossPos ν ν := hstep
          _ = cinv * Aν := by rw [hCPν_eq]
          _ ≤ (2 : ℝ≥0∞) * Aν := by exact mul_le_mul' hcinv_le_two (le_refl _)
      -- chain: `h(ν_n) ≤ (crossPos ν_n ν : EReal) ≤ (2 * Aν : EReal)`.
      calc differentialEntropyExt νn ≤ ((crossPos νn ν : ℝ≥0∞) : EReal) := hh_le
        _ ≤ ((2 * Aν : ℝ≥0∞) : EReal) := by exact_mod_cast hCPνn_dom
    -- contradiction with `h(ν_n) → ⊤`.
    rw [EReal.tendsto_nhds_top_iff_real] at hνn_tendsto
    have h2Aν_fin : (2 * Aν) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hAν_ne
    -- pick `M` larger than `(2 * Aν).toReal` and derive `(M:EReal) < h(ν_n) ≤ (2*Aν:EReal) ≤ (M:EReal)`.
    have hcontra := hνn_tendsto ((2 * Aν).toReal)
    obtain ⟨n, hMn, hubn⟩ := (hcontra.and hub).exists
    have : ((2 * Aν : ℝ≥0∞) : EReal) = (((2 * Aν).toReal : ℝ) : EReal) :=
      (EReal.coe_ennreal_toReal h2Aν_fin).symm
    rw [this] at hubn
    exact absurd (lt_of_lt_of_le hMn hubn) (by simp)
  -- **conclude `h(ν) = ⊤`** : `h(ν) = (Aν:EReal) - (B(ν):EReal) = ⊤ - fin = ⊤`.
  rw [differentialEntropyExt_of_ac hν_ac, ← hAν_def, hAν_top, EReal.coe_ennreal_top,
    ← EReal.coe_ennreal_toReal hBν, EReal.top_sub_coe]

/-! ## 無条件 gateway 単調性 (方針 Y、(i-a) 非依存)

⊥ 枝 (`bot_le`)、有限枝 (`differentialEntropyExt_mono_add_of_integrable`、per-fibre Gibbs)、
⊤ 枝 (`differentialEntropyExt_top_of_indep_add_unconditional`、route β') の 3 部品を組んで
gateway 単調性を無条件で建てる。有限枝は finiteness → integrability の bridge
(`differentialEntropyExt_integrable_of_finite`) を経由する。 -/

/-- **有限微分エントロピー → `negMulLog∘density` 可積分** (`differentialEntropyExt_of_ac_integrable`
の converse)。a.c. + `h(μ) ≠ ⊤` + `h(μ) ≠ ⊥` から、`negMulLog (density)` が `volume` 上可積分。

`differentialEntropyExt_of_ac hac` で `h = (A:EReal) − (B:EReal)` (A/B = 正部・負部 lintegral)。
- `A ≠ ⊤`: A=⊤ なら `(⊤:EReal) − B = ⊤` (B<⊤) で `h=⊤`、`hne_top` に矛盾。
- `B ≠ ⊤`: B=⊤ なら `A − ⊤ = ⊥` (A<⊤) で `h=⊥`、`hne_bot` に矛盾。
- `A<⊤ ∧ B<⊤ ⟹ Integrable`: aestronglyMeasurable + HasFiniteIntegral
  (`∫⁻ ‖negMulLog f‖ₑ = A + B < ⊤`)。

honesty: `hne_top`/`hne_bot` は有限性 regularity precondition (結論 = Integrable を encode せず)。

**独立 honesty audit 2026-06-08 (fresh subagent, commit 64cb872 → ok)**: 4-check 全 PASS。
(1) 非循環 — 結論 `Integrable (negMulLog∘density)` は 3 仮説のいずれとも非同型、body は EReal
分岐 (`hsplit` の `A−B` 展開 + `EReal.sub_top`/`top_sub` で A≠⊤/B≠⊤) → `integrable_of_lintegral_
ofReal_pos_neg_ne_top` で genuine 組立 (`:= h` でない)。(2) 非バンドル — `hac` 絶対連続性、
`hne_top`/`hne_bot` 有限性 regularity precondition、3 仮説 grant しても Integrable は body の
EReal 推論を要し核を encode せず。(3) 非退化 — Integrable は実命題、vacuous/exfalso なし。
(4) **sufficiency (反例試行) — 両仮説 genuine に必要**: `hne_bot` 落とすと A<⊤∧B=⊤ (h=fin−⊤=⊥,
hne_top 成立だが非可積分) が反例、`hne_top` 落とすと A=⊤∧B<⊤ (h=⊤−fin=⊤, hne_bot 成立だが
非可積分) が反例。under-hypothesized でない。`#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free 機械確認、(i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` 非継承)。@audit:ok -/
theorem differentialEntropyExt_integrable_of_finite {μ : Measure ℝ} (hac : μ ≪ volume)
    (hne_top : differentialEntropyExt μ ≠ ⊤) (hne_bot : differentialEntropyExt μ ≠ ⊥) :
    Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume := by
  -- positive- and negative-part lintegrals of the density's `negMulLog`.
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `h(μ) = (A : EReal) - (B : EReal)`.
  have hsplit : differentialEntropyExt μ = (A : EReal) - (B : EReal) := by
    rw [differentialEntropyExt_of_ac hac]
  -- **`A ≠ ⊤`**: otherwise `⊤ - B` is `⊤` (B≠⊤) or `⊥` (B=⊤), both excluded.
  have hA_ne_top : A ≠ ⊤ := by
    intro hAtop
    by_cases hBtop : (B : EReal) = ⊤
    · -- `⊤ - ⊤ = ⊥` contradicts `hne_bot`.
      apply hne_bot
      rw [hsplit, hAtop, EReal.coe_ennreal_top, hBtop, EReal.sub_top]
    · -- `⊤ - (coe) = ⊤` contradicts `hne_top`.
      apply hne_top
      rw [hsplit, hAtop, EReal.coe_ennreal_top, EReal.top_sub hBtop]
  -- **`B ≠ ⊤`**: with `A < ⊤`, `(A : EReal) - ⊤ = ⊥` contradicts `hne_bot`.
  have hB_ne_top : B ≠ ⊤ := by
    intro hBtop
    apply hne_bot
    rw [hsplit, hBtop, EReal.coe_ennreal_top, EReal.sub_top]
  -- assemble integrability from the two finite lintegrals + measurability.
  refine integrable_of_lintegral_ofReal_pos_neg_ne_top ?_ hA_ne_top hB_ne_top
  exact (Real.continuous_negMulLog.measurable.comp
    (μ.measurable_rnDeriv volume).ennreal_toReal).aestronglyMeasurable

/-- **無条件 gateway 単調性** (方針 Y、(i-a) 非依存): `W a.c. ∧ W ⊥ V ⟹ h(W) ≤ h(W+V)`。
⊥ 枝 = `bot_le`、有限枝 = `differentialEntropyExt_mono_add_of_integrable` (per-fibre Gibbs)、
⊤ 枝 = `differentialEntropyExt_top_of_indep_add_unconditional` (route β')。

旧 `EPIUncondMonotone.differentialEntropyExt_mono_add` の無条件 proof-done 版 (旧版は無条件版②
`differentialEntropyExt_indep_add_eq_add_klDiv` (i-a) に transitive 依存)。本版は (i-a) を継承しない。

**独立 honesty audit 2026-06-08 (fresh subagent, commit 64cb872 → ok)**: 4-check 全 PASS。
(1) 非循環 — 結論 `h(W)≤h(W+V)` は 4 仮説のいずれとも非同型、body は genuine 3 枝場合分け。
(2) 非バンドル — `hW`/`hV`/`hWV`/`hW_ac` は可測/独立/絶対連続 regularity、核 (単調性) は body の
3 枝 (⊥=`bot_le` / ⊤=route β' `@audit:ok` / 有限=per-fibre Gibbs `@audit:ok` + bridge) が担う。
(3) 非退化 — ⊤ 枝の `⊤≤⊤` は route β' `differentialEntropyExt_top_of_indep_add_unconditional`
(genuine, `@audit:ok`) で `h(W+V)=⊤` を確立してから閉じる、退化定義悪用でない。
(4) **sufficiency (反例試行) — 含意 TRUE**: 「独立ノイズ加算は微分エントロピーを減らさない」の genuine
EPI 単調性、`hW_ac`/`hWV` は genuine に必要。under-hypothesized でない。**name-laundering check —
NOT laundering**: `_unconditional` = (i-a) sorryAx 非継承の proof-route 主張で正当、open load-bearing
hyp も偽装 sorry-body も無し。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free
機械確認、axiom 出力に (i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` 不在で非継承を独立裏取り)。@audit:ok -/
theorem differentialEntropyExt_mono_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (fun ω => W ω + V ω)) := by
  -- **⊥ branch**: `h(W) = ⊥ ≤ anything`.
  rcases eq_bot_or_bot_lt (differentialEntropyExt (P.map W)) with hbot | hpos
  · rw [hbot]; exact bot_le
  · have hne_bot : differentialEntropyExt (P.map W) ≠ ⊥ := hpos.ne'
    by_cases htop : differentialEntropyExt (P.map W) = ⊤
    · -- **⊤ branch**: route β' gives `h(W+V) = ⊤`, so `⊤ ≤ ⊤`.
      rw [htop, differentialEntropyExt_top_of_indep_add_unconditional W V P hW hV hWV hW_ac htop]
    · -- **finite branch**: bridge finiteness → integrability, then per-fibre Gibbs.
      exact differentialEntropyExt_mono_add_of_integrable W V P hW hV hWV hW_ac
        (differentialEntropyExt_integrable_of_finite hW_ac htop hne_bot)

/-- **無条件 gateway atom** (方針 Y): `W a.c. ∧ W ⊥ V ⟹ N(W+V) ≥ N(W)`。
`differentialEntropyExt_mono_add_unconditional` を `EReal.exp_monotone` で `entropyPowerExt`
(= `EReal.exp (2 · differentialEntropyExt)`) に lift。proof-done (i-a 非依存)。

**独立 honesty audit 2026-06-08 (fresh subagent, commit 64cb872 → ok)**: `mono_add_unconditional`
(@audit:ok) の genuine な `EReal.exp_monotone` lift (`mul_le_mul_of_nonneg_left ... (2≥0)` 経由)、
循環/bundling なし。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認、
(i-a) 非継承)。@audit:ok -/
theorem entropyPowerExt_mono_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    entropyPowerExt (P.map (fun ω => W ω + V ω)) ≥ entropyPowerExt (P.map W) := by
  unfold entropyPowerExt
  apply EReal.exp_monotone
  exact mul_le_mul_of_nonneg_left
    (differentialEntropyExt_mono_add_unconditional W V P hW hV hWV hW_ac) (by norm_num)

end InformationTheory.Shannon
