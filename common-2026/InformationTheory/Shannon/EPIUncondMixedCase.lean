import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic

/-!
# EPI 無条件化 — 特異・混合 case (S3)

`docs/shannon/epi-singular-mixed-case-plan.md` の Phase 1–5。S1 完成済の
`entropyPowerExt : Measure ℝ → ℝ≥0∞` (非分岐、退化トラップ除去済) 上で、3-case
分岐のうち **case 2 (X a.c. ∧ Y 特異)** + **case 3 (両特異)** の EPI を genuine 化する。

* Phase 1 `entropyPowerExt_singular_add_ge` (両特異): RHS = 0 + 0、`zero_le` で型自明。
* Phase 2 `map_add_absolutelyContinuous` (X a.c. ∧ X ⊥ Y ⟹ X+Y a.c.): 純 Mathlib (conv)。
* Phase 3 `differentialEntropy_add_ge_of_indep` (Real 中核 `h(X) ≤ h(X+Y)`):
  `condDifferentialEntropy_indep_add_eq` (c=1) + `condDifferentialEntropy_le` 合成。
  8 integrability は **honest regularity precondition** (W=X+Y の a.c. 密度 + fibre
  regularity)、`*Hypothesis` predicate に bundle しない。NOT load-bearing。
* Phase 4 `entropyPowerExt_mixed_add_ge` (+ 対称版): S1 `_of_ac`/`_singular` で ℝ≥0∞ lift。
* Phase 5 `entropyPowerExt_add_ge_dispatch_skeleton`: 4 分岐 by_cases。case 2/3 は上記補題、
  両 a.c. (case 1) は本 plan scope 外の hard core (`epi-stam-to-conclusion-plan` 待ち) で park。

case 3 の RHS = 0 は **genuine** (特異測度のエントロピーパワーは真に 0)、退化定義悪用ではない。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Phase 1 — case 3 (両特異)**: X, Y とも特異なら
`N(X+Y) ≥ N(X) + N(Y) = 0 + 0 = 0`。LHS ≥ 0 は ℝ≥0∞ で型自明 (`zero_le`)。
X+Y が a.c. か特異かを判定せずに閉じる (RHS=0 ゆえ LHS の値に依らず成立)。

退化定義悪用ではない: 特異測度のエントロピーパワーは真に 0 であり RHS=0 は正しい値。
独立 honesty audit 2026-06-05: `entropyPowerExt_singular` (genuine, sorryAx-free) + sanity gate
(`entropyPowerExt_dirac`/`_gaussianReal`) により退化定義悪用でなく、RHS=0 は正しい値と確認。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem entropyPowerExt_singular_add_ge
    (X Y : Ω → ℝ) (P : Measure Ω)
    (hX_sing : ¬ P.map X ≪ volume) (hY_sing : ¬ P.map Y ≪ volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  rw [entropyPowerExt_singular hX_sing, entropyPowerExt_singular hY_sing, add_zero]
  exact zero_le'

/-- **Phase 2 — convolution-a.c.**: `X a.c. ∧ X ⊥ Y ⟹ X+Y a.c.`。
`IndepFun.map_add_eq_map_conv_map` で `μ.map(X+Y) = μ.map X ∗ μ.map Y`、`conv_comm` で
a.c. 因子を右に回し (`conv_absolutelyContinuous` は a.c. 因子を右に要求する非対称形)、
`conv_absolutelyContinuous` で a.c. 伝播。純 Mathlib。
独立 honesty audit 2026-06-05: 仮説は全 regularity precondition (measurability/IndepFun/a.c.)、
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。@audit:ok -/
theorem map_add_absolutelyContinuous
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : P.map X ≪ volume) :
    P.map (fun ω => X ω + Y ω) ≪ volume := by
  rw [show (fun ω => X ω + Y ω) = X + Y from rfl,
    hXY.map_add_eq_map_conv_map hX hY, Measure.conv_comm]
  exact Measure.conv_absolutelyContinuous hX_ac

/-- **Phase 3 — case 2 Real 中核** `h(X) ≤ h(X+Y)`。
`condDifferentialEntropy_indep_add_eq` (c=1, Z:=Y) で `h(X+Y | Y) = h(X)`、
`condDifferentialEntropy_le` (X:=X+Y, Z:=Y) で `h(X+Y|Y) ≤ h(X+Y)`。合成して結論。

8 integrability 前提 (`h_ac`/`h_int`/`hκ_v`/`hκ_logp_int`/`hκ_cross_int`/`h_fibreEnt_int`/
`h_cross_int`/`h_logq_int`) は **honest regularity precondition** — W=X+Y の a.c. 密度 +
fibre regularity であって、結論の核心を encode していない (**NOT load-bearing**)。
`differentialEntropy_indep_gaussian_add_ge` の signature が雛形 (`√s·Z` を `Y` に置換)。
独立 honesty audit 2026-06-05: 8 integrability は `condDifferentialEntropy_le` / `_indep_add_eq`
(両 genuine `@audit:ok`) の precondition と同型 threading で load-bearing でない。core は genuine な
依存補題側にあり、結論 `h(X)≤h(X+Y)` を仮説に encode していない。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem differentialEntropy_add_ge_of_indep
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume)
    (hW_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume)
    (h_ac : (P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P
        ≪ (P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω)))
    (h_int : Integrable
      (llr ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P)
        ((P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω))))
      ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P))
    (hκ_v : ∀ᵐ z ∂(P.map Y),
      condDistrib (fun ω => X ω + Y ω) Y P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Y ω) Y P z)) (P.map Y))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) ∂volume) (P.map Y))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => X ω + Y ω))) :
    differentialEntropy (P.map X)
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) := by
  set W : Ω → ℝ := fun ω => X ω + Y ω with hW
  have hW_meas : Measurable W := hX.add hY
  -- Fibre identification (c=1): `h(X + 1·Y | Y) = h(X)`, and `1·Y = Y`.
  have h_fibre : condDifferentialEntropy W Y P = differentialEntropy (P.map X) := by
    have h := condDifferentialEntropy_indep_add_eq X Y P 1 hX hY hXY hX_ac
    simpa only [one_mul] using h
  -- Conditioning reduces entropy: `h(W | Y) ≤ h(W)`.
  have h_le : condDifferentialEntropy W Y P ≤ differentialEntropy (P.map W) :=
    condDifferentialEntropy_le W Y P hW_meas hY hW_ac h_ac h_int hκ_v hκ_logp_int
      hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int
  rw [← h_fibre]
  exact h_le

/-- **Phase 4 — case 2 ℝ≥0∞ lift** (X a.c. ∧ Y 特異): `N(X+Y) ≥ N(X) + N(Y)`。
`entropyPowerExt_singular hY_sing` で N(Y)=0 → RHS = N(X)。X, X+Y 共に a.c. かつ
有限微分エントロピー (`hX_ent`/`hW_ent` = X / X+Y の `negMulLog density` 可積分) なので
`entropyPowerExt_of_ac_integrable` で両者 `ofReal (exp (2h))`、Phase 3 の `h(X)≤h(X+Y)` を
`Real.exp_le_exp` → `ENNReal.ofReal_le_ofReal` で lift (2026-06-06 def-fix で finite-entropy 前提追加)。

8 integrability + 2 finite-entropy (`hX_ent`/`hW_ent`) は Phase 3 / `_of_ac_integrable` から
透過する honest regularity precondition (NOT load-bearing — X / X+Y の有限微分エントロピーを
表明するだけで EPI の核を encode しない)。
独立 honesty audit 2026-06-05: core は genuine Phase 3 補題を直接呼出 +
`entropyPowerExt_of_ac_integrable`/`_singular` lift、`#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free)。@audit:ok
(2026-06-06 def-fix で finite-entropy 前提追加)。
**def-fix 後再監査 PASS (2026-06-06)**: 新 `hX_ent`/`hW_ent` は a.c. 訂正 def 下で
`entropyPowerExt_of_ac_integrable` (有限差→workhorse) lift に必要な honest regularity precondition、
load-bearing でない。`#print axioms` = sorryAx-free 再確認。@audit:ok -/
theorem entropyPowerExt_mixed_add_ge
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_sing : ¬ P.map Y ≪ volume)
    (h_ac : (P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P
        ≪ (P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω)))
    (h_int : Integrable
      (llr ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P)
        ((P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω))))
      ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P))
    (hκ_v : ∀ᵐ z ∂(P.map Y),
      condDistrib (fun ω => X ω + Y ω) Y P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Y ω) Y P z)) (P.map Y))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) ∂volume) (P.map Y))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => X ω + Y ω)))
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- RHS = N(X) + N(Y) = N(X) + 0 = N(X).
  rw [entropyPowerExt_singular hY_sing, add_zero]
  -- X+Y is a.c. (convolution of an a.c. factor).
  have hW_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  -- Real core: `h(X) ≤ h(X+Y)`.
  have h_real : differentialEntropy (P.map X)
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) :=
    differentialEntropy_add_ge_of_indep X Y P hX hY hXY hX_ac hW_ac h_ac h_int hκ_v
      hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int
  -- Lift to ℝ≥0∞: both endpoints are a.c. with finite differential entropy, so `N = ofReal (exp (2h))`.
  rw [entropyPowerExt_of_ac_integrable hX_ac hX_ent, entropyPowerExt_of_ac_integrable hW_ac hW_ent]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-- **Phase 4 — case 2 対称版** (Y a.c. ∧ X 特異): `N(X+Y) ≥ N(X) + N(Y)`。
`X + Y = Y + X` (`add_comm` の funext) で `entropyPowerExt_mixed_add_ge` を Y/X 入替えて
再適用 (`hXY.symm : IndepFun Y X P`)。RHS は `N(X)+N(Y) = N(Y)+N(X)` を `add_comm` で合わせる。
inner call の `hX_ent`/`hW_ent` 位置には Y が X-role ゆえ `hY_ent` (Y の density) /
`hWyx_ent` (Y+X の density) を渡す。

8 integrability + 2 finite-entropy (`hY_ent`/`hWyx_ent`) は `Y+X` の path で本補題の honest
regularity precondition (NOT load-bearing)。
独立 honesty audit 2026-06-05: `entropyPowerExt_mixed_add_ge` (genuine) を Y/X 入替で直接再適用、
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。@audit:ok
(2026-06-06 def-fix で finite-entropy 前提追加)。
**def-fix 後再監査 PASS (2026-06-06)**: `hY_ent`/`hWyx_ent` は Y+X path の honest regularity
precondition、load-bearing でない。`#print axioms` = sorryAx-free 再確認。@audit:ok -/
theorem entropyPowerExt_mixed_add_ge_symm
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hY_ac : (P.map Y) ≪ volume) (hX_sing : ¬ P.map X ≪ volume)
    (h_ac : (P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P
        ≪ (P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω)))
    (h_int : Integrable
      (llr ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P)
        ((P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω))))
      ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P))
    (hκ_v : ∀ᵐ z ∂(P.map X),
      condDistrib (fun ω => Y ω + X ω) X P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => Y ω + X ω) X P z)) (P.map X))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) ∂volume) (P.map X))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => Y ω + X ω)))
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hWyx_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- `X + Y = Y + X` pointwise, and `N(X) + N(Y) = N(Y) + N(X)`.
  rw [show (fun ω => X ω + Y ω) = (fun ω => Y ω + X ω) from
        funext fun ω => add_comm _ _, add_comm (entropyPowerExt (P.map X))]
  exact entropyPowerExt_mixed_add_ge Y X P hY hX hXY.symm hY_ac hX_sing h_ac h_int hκ_v
    hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int hY_ent hWyx_ent

/-- **case 1 残核 — 両 a.c. + 両有限エントロピーの classical EPI** (named wall)。
両 a.c. かつ両入力が有限微分エントロピー (negMulLog density 可積分) のとき EPI。これは古典 EPI
そのもの。Phase A `entropy_power_inequality_of_density` (sorryAx-free) が **正則密度** (IsRegularDensityV2
等) sub-case を genuine に discharge 済。一般有限分散 a.c. は smoothing→正則化 + endpoint 連続性
(`heatFlowEntropyPower_continuousWithinAt_zero`) の方針 X (`epi-case1-difference-g3-closure-plan`)、
無限分散 a.c. は Lieb-Young 不在の genuine Mathlib 壁 (`epi-uncond-truncation-lsc-inventory.md` thread D)。
def-fix (2026-06-06) 後 statement は TRUE-as-stated。本 session では named wall として隔離。

独立 honesty audit 2026-06-06 (def-fix): **wall 分類 `wall:epi-finite-entropy-ac-classical` 妥当**。
(a) signature honest — `hX_ent`/`hY_ent` は有限微分エントロピー regularity precondition、結論
`N(X+Y) ≥ N(X)+N(Y)` を encode せず (古典 EPI を仮説 bundle しない)、循環/`:True`/退化なし。
(b) sufficiency — 両 a.c. + 両有限エントロピーで古典 EPI は数学的に真 (Shannon/Stam 定理、反例不在)、
false-as-framed でない。X+Y 側の有限性は不要 (LHS=∞ でも `≥` 成立)。
(c) wall 裏取り — Mathlib に `entropyPower`/`fisherInformation`/EPI 系 loogle Found 0、in-tree
`entropy_power_inequality_of_density` は正則密度のみ discharge、無限分散は thread D で構造的壁を独立記録。
正則密度 (Phase A 閉) + 一般有限分散 (method-X plan) + 無限分散 (真壁) を 1 named wall に集約する設計、
`plan:` 単独より `wall:` 分類が妥当 (複数 closure 経路を持つ 1 壁)。`#print axioms` = sorryAx (唯一の壁)。
@residual classification 検証済 = honest_residual。
`@residual(wall:epi-finite-entropy-ac-classical)` -/
theorem entropyPowerExt_add_ge_finite_ac
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  sorry

/-- **Phase 5 — 3-case 判定 dispatch スケルトン**.

`P.map X ≪ volume` / `P.map Y ≪ volume` の 4 分岐で組む:
* 両 a.c. (**case 1**): named wall `entropyPowerExt_add_ge_finite_ac` (両有限エントロピーの
  classical EPI) に置換。bare sorry は消え sorry は当該補題内 1 本に局所化
  (`@residual(wall:epi-finite-entropy-ac-classical)`)。threaded `hX_ent`/`hY_ent` を再利用。
* X a.c. ∧ Y 特異 (case 2): `entropyPowerExt_mixed_add_ge` (+ X+Y path の integrability + `hX_ent`/`hW_ent`)。
* Y a.c. ∧ X 特異 (case 2 対称): `entropyPowerExt_mixed_add_ge_symm` (+ Y+X path の integrability + `hY_ent`/`hWyx_ent`)。
* 両特異 (case 3): `entropyPowerExt_singular_add_ge` (型自明、RHS=0)。

case 3 (両特異) 枝は本 file 内で genuine に閉じる (`entropyPowerExt_singular_add_ge` 直接呼出)。
case 2 (X a.c. ∧ Y 特異) / case 2 対称 (Y a.c. ∧ X 特異) の 2 枝は、Phase 4 補題
`entropyPowerExt_mixed_add_ge` / `_symm` を **8 integrability + 2 finite-entropy precondition
つきで直接呼出** する。これらの integrability / finite-entropy は path 依存の honest regularity
precondition (X+Y path / Y+X path の a.c. 密度 + fibre regularity + 有限微分エントロピー、
**NOT load-bearing**)。X+Y path の 8 本を `h_*`、Y+X path の 8 本を `h_*_symm`、finite-entropy
4 本 (`hX_ent`/`hW_ent`/`hY_ent`/`hWyx_ent`) を dispatch signature に直接展開する
(結論を仮説に bundle しない)。

case 1 枝 (両 a.c.) は def-fix (2026-06-06) で bare sorry を named wall
`entropyPowerExt_add_ge_finite_ac` 呼出に置換 (threaded `hX_ent`/`hY_ent` を再利用)。bare sorry
は消え、sorry は named wall `wall:epi-finite-entropy-ac-classical` 内 1 本に局所化。旧
`@residual(plan:epi-stam-to-conclusion-plan)` は削除 (case-1 は新 named wall lemma へ移動)。

**全 4 枝 genuine か named wall delegation** (case 3 は vacuous でなく特異測度のエントロピーパワーが
真に 0、case 2 の前提は load-bearing でなく regularity precondition を Phase 4 補題に threading
するのみ、case 1 は named wall に delegation)。新 finite-entropy 前提 4 本は honest regularity
precondition (方針 X partial scope、load-bearing でない)。
独立 honesty audit 2026-06-05: case 2 / case 2 対称 枝は本 file の genuine Phase 4 補題を直接呼出、
integrability は honest regularity precondition、case 1 は named wall に delegation。
**def-fix 後再監査 PASS (2026-06-06)**: `#print axioms` 機械確認で case-2/3/symm 補題は全て
sorryAx-free (`[propext, Classical.choice, Quot.sound]`)、dispatch 自身は `[propext, sorryAx,
Classical.choice, Quot.sound]` = case-1 named wall のみが唯一の transitive sorry。旧 def の bare
sorry (埋めれば偽命題を証明する false-as-stated obligation) は named wall 1 本に局所化され消滅。
新 finite-entropy 前提 4 本 (`hX_ent`/`hW_ent`/`hY_ent`/`hWyx_ent`) は honest regularity
precondition (各 path の有限微分エントロピー表明、load-bearing でない)。@audit:ok (dispatch 構造、
ただし transitive sorry は named wall `wall:epi-finite-entropy-ac-classical` 由来で残存) -/
theorem entropyPowerExt_add_ge_dispatch_skeleton
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    -- case 2 (X a.c. ∧ Y 特異) 用 X+Y path の 8 integrability regularity precondition (NOT load-bearing)
    (h_ac : (P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P
        ≪ (P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω)))
    (h_int : Integrable
      (llr ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P)
        ((P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω))))
      ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P))
    (hκ_v : ∀ᵐ z ∂(P.map Y),
      condDistrib (fun ω => X ω + Y ω) Y P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Y ω) Y P z)) (P.map Y))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) ∂volume) (P.map Y))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => X ω + Y ω)))
    -- case 2 対称 (Y a.c. ∧ X 特異) 用 Y+X path の 8 integrability regularity precondition (NOT load-bearing)
    (h_ac_symm : (P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P
        ≪ (P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω)))
    (h_int_symm : Integrable
      (llr ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P)
        ((P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω))))
      ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P))
    (hκ_v_symm : ∀ᵐ z ∂(P.map X),
      condDistrib (fun ω => Y ω + X ω) X P z ≪ volume)
    (hκ_logp_int_symm : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int_symm : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int_symm : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => Y ω + X ω) X P z)) (P.map X))
    (h_cross_int_symm : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) ∂volume) (P.map X))
    (h_logq_int_symm : Integrable
      (fun x => Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => Y ω + X ω)))
    -- case 1 (両 a.c.) + case 2 / 対称 用 finite-entropy regularity precondition (NOT load-bearing)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hWyx_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hX_ac : P.map X ≪ volume
  · by_cases hY_ac : P.map Y ≪ volume
    · -- case 1 (両 a.c.): named wall `entropyPowerExt_add_ge_finite_ac` に delegation。
      -- bare sorry は消え、sorry は named wall 内 1 本に局所化。
      exact entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent
    · -- case 2 (X a.c. ∧ Y 特異): Phase 4 補題を 8 integrability + 2 finite-entropy precondition つきで直接呼出。
      exact entropyPowerExt_mixed_add_ge X Y P hX hY hXY hX_ac hY_ac h_ac h_int hκ_v
        hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int hX_ent hW_ent
  · by_cases hY_ac : P.map Y ≪ volume
    · -- case 2 対称 (Y a.c. ∧ X 特異): Phase 4 対称版を Y+X path integrability + 2 finite-entropy つきで直接呼出。
      exact entropyPowerExt_mixed_add_ge_symm X Y P hX hY hXY hY_ac hX_ac h_ac_symm h_int_symm
        hκ_v_symm hκ_logp_int_symm hκ_cross_int_symm h_fibreEnt_int_symm h_cross_int_symm
        h_logq_int_symm hY_ent hWyx_ent
    · -- case 3 (両特異): 型自明、RHS=0。
      exact entropyPowerExt_singular_add_ge X Y P hX_ac hY_ac

end InformationTheory.Shannon
