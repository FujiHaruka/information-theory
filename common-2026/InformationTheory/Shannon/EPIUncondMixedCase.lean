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
`entropyPowerExt_singular hY_sing` で N(Y)=0 → RHS = N(X)。X, X+Y 共に a.c. なので
`entropyPowerExt_of_ac` で両者 `ofReal (exp (2h))`、Phase 3 の `h(X)≤h(X+Y)` を
`Real.exp_le_exp` → `ENNReal.ofReal_le_ofReal` で lift。

8 integrability は Phase 3 から透過する honest regularity precondition (NOT load-bearing)。
独立 honesty audit 2026-06-05: core は genuine Phase 3 補題を直接呼出 + `entropyPowerExt_of_ac`/
`_singular` lift、`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。@audit:ok -/
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
      (P.map (fun ω => X ω + Y ω))) :
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
  -- Lift to ℝ≥0∞: both endpoints are a.c., so `N = ofReal (exp (2h))`.
  rw [entropyPowerExt_of_ac hX_ac, entropyPowerExt_of_ac hW_ac]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-- **Phase 4 — case 2 対称版** (Y a.c. ∧ X 特異): `N(X+Y) ≥ N(X) + N(Y)`。
`X + Y = Y + X` (`add_comm` の funext) で `entropyPowerExt_mixed_add_ge` を Y/X 入替えて
再適用 (`hXY.symm : IndepFun Y X P`)。RHS は `N(X)+N(Y) = N(Y)+N(X)` を `add_comm` で合わせる。

8 integrability は `Y+X` の path で本補題の honest regularity precondition (NOT load-bearing)。
独立 honesty audit 2026-06-05: `entropyPowerExt_mixed_add_ge` (genuine) を Y/X 入替で直接再適用、
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。@audit:ok -/
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
      (P.map (fun ω => Y ω + X ω))) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- `X + Y = Y + X` pointwise, and `N(X) + N(Y) = N(Y) + N(X)`.
  rw [show (fun ω => X ω + Y ω) = (fun ω => Y ω + X ω) from
        funext fun ω => add_comm _ _, add_comm (entropyPowerExt (P.map X))]
  exact entropyPowerExt_mixed_add_ge Y X P hY hX hXY.symm hY_ac hX_sing h_ac h_int hκ_v
    hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int

/-- **Phase 5 — 3-case 判定 dispatch スケルトン**.

`P.map X ≪ volume` / `P.map Y ≪ volume` の 4 分岐で組む:
* 両 a.c. (**case 1**): 既存 plan 群 (`epi-stam-to-conclusion-plan`) が closure する hard
  core。本 plan scope 外なので `sorry` + `@residual(plan:epi-stam-to-conclusion-plan)` で park。
* X a.c. ∧ Y 特異 (case 2): `entropyPowerExt_mixed_add_ge` (+ X+Y path の integrability)。
* Y a.c. ∧ X 特異 (case 2 対称): `entropyPowerExt_mixed_add_ge_symm` (+ Y+X path の integrability)。
* 両特異 (case 3): `entropyPowerExt_singular_add_ge` (型自明、RHS=0)。

case 3 (両特異) 枝は本 file 内で genuine に閉じる (`entropyPowerExt_singular_add_ge` 直接呼出)。
case 2 (X a.c. ∧ Y 特異) / case 2 対称 (Y a.c. ∧ X 特異) の 2 枝は、Phase 4 補題
`entropyPowerExt_mixed_add_ge` / `_symm` を **8 integrability precondition つきで直接呼出** する。
これらの integrability は path 依存の honest regularity precondition (X+Y path / Y+X path の
a.c. 密度 + fibre regularity、**NOT load-bearing**)。X+Y path の 8 本を `h_*`、Y+X path の 8 本を
`h_*_symm` として dispatch signature に直接展開する (結論を仮説に bundle しない)。

case 1 枝 (両 a.c.) のみ `sorry`: 既存 plan 群 (`epi-stam-to-conclusion-plan`) が closure する
hard core で本 plan scope 外。最終 headline `entropy_power_inequality_unconditional`
(S2 で確定する新型 statement、case1 を S5 経由無前提版に差替) の body 完成は傘 Phase 5。

**case 1 park 以外は genuine** (case 3 は vacuous でなく特異測度のエントロピーパワーが真に 0、
case 2 の前提は load-bearing でなく regularity precondition を Phase 4 補題に threading するのみ)。
独立 honesty audit 2026-06-05: case 2 / case 2 対称 枝は本 file の genuine Phase 4 補題を直接呼出、
integrability は honest regularity precondition、case 1 のみ `@residual(plan:...)` で park。
@residual(plan:epi-stam-to-conclusion-plan) -/
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
      (P.map (fun ω => Y ω + X ω))) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hX_ac : P.map X ≪ volume
  · by_cases hY_ac : P.map Y ≪ volume
    · -- case 1 (両 a.c.): hard core、本 plan scope 外で park。
      -- @residual(plan:epi-stam-to-conclusion-plan)
      sorry
    · -- case 2 (X a.c. ∧ Y 特異): Phase 4 補題を 8 integrability precondition つきで直接呼出。
      exact entropyPowerExt_mixed_add_ge X Y P hX hY hXY hX_ac hY_ac h_ac h_int hκ_v
        hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int
  · by_cases hY_ac : P.map Y ≪ volume
    · -- case 2 対称 (Y a.c. ∧ X 特異): Phase 4 対称版を Y+X path integrability つきで直接呼出。
      exact entropyPowerExt_mixed_add_ge_symm X Y P hX hY hXY hY_ac hX_ac h_ac_symm h_int_symm
        hκ_v_symm hκ_logp_int_symm hκ_cross_int_symm h_fibreEnt_int_symm h_cross_int_symm
        h_logq_int_symm
    · -- case 3 (両特異): 型自明、RHS=0。
      exact entropyPowerExt_singular_add_ge X Y P hX_ac hY_ac

end InformationTheory.Shannon
