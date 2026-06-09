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
# TruncationLimit — Core part

route β' (truncation + monotone-limit) の foundational layer。truncW 構成 / cond 密度公式 /
measure domination / cross-entropy (crossPos/crossNeg) と finiteness-free ℝ≥0∞ Gibbs /
convolution 密度 / per-fibre a.c. / 和周辺負部有限性。下流 part (Mono / Limit) が import する。
umbrella: `InformationTheory.Shannon.EPI.Unconditional.TruncationLimit`。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **W 単独 truncation の構成** (route T `condTrunc` を W 単独に読み替え)。
`truncW P W n := P[| {ω | |W ω| ≤ n}]` (`W` の値が `[-n, n]` に入る事象での条件付け)。
各 `truncW P W n` は compact support (有界) → 有限分散・有限エントロピーを満たし、a.c.
(`cond_absolutelyContinuous` 保存) を保つ。route T の joint `truncSet X Y n` と違い W 単独。
@audit:ok -/
noncomputable def truncW (P : Measure Ω) (W : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P {ω | |W ω| ≤ (n : ℝ)}

/-- **cond density formula** (route T `rnDeriv_cond_eq` を W 単独 truncation 用に再掲、heavy
import 回避のため local 再証明): 確率測度 `μ : Measure ℝ` を可測集合 `s` (positive mass) で
条件付けた測度の Radon-Nikodym 微分は `(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`。
`cond μ s = (μ s)⁻¹ • μ.restrict s` の scalar mul + restrict の rnDeriv (`rnDeriv_smul_left_of_ne_top`
+ `rnDeriv_restrict`、共に Mathlib) で組立。route T と完全同型 (集約漏れでなく import cycle/cost 回避)。
@audit:ok -/
theorem rnDeriv_cond_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ}
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
@audit:ok -/
theorem map_truncW_add_le_smul_map_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (n : ℕ)
    (_hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
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
@audit:ok -/
theorem map_truncW_add_absolutelyContinuous_map_add
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
theorem crossPos_self (ν : Measure ℝ) [SigmaFinite ν] (hν : ν ≪ volume) :
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
theorem crossNeg_self (ν : Measure ℝ) [SigmaFinite ν] (hν : ν ≪ volume) :
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
@audit:ok -/
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
@audit:ok -/
theorem integrable_negMulLog_rnDeriv_map_add_const
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
@audit:ok -/
theorem conv_eq_withDensity_translate_average
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
@audit:ok -/
theorem map_add_const_withDensity (f : ℝ → ℝ≥0∞) (z : ℝ) :
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
@audit:ok -/
theorem condDistrib_ae_absolutelyContinuous_indep_add
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
theorem negPart_negMulLog_conv_single_ne_top
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

end InformationTheory.Shannon
