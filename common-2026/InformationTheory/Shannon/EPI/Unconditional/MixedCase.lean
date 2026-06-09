import InformationTheory.Shannon.EntropyPower.Ext
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone
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
@audit:ok -/
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
@audit:ok -/
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
@audit:ok -/
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

**@audit:superseded-by(entropyPowerExt_add_ge_unconditional)** (2026-06-08): 本 case-2 補題 (8 integrability
+ 2 finite-entropy precondition) は旧 21-precondition `entropyPowerExt_add_ge_dispatch_skeleton` 専用。
Phase 5 endgame で gateway 単調性経由の無条件版 `entropyPowerExt_mixed_add_ge_uncond`
(`EPIUncondDispatchFull.lean`、precondition `hX_ac hY_sing` のみ) に置換され、完全無条件 headline
`entropyPowerExt_add_ge_unconditional` のチェーンからは到達しない (consumer = dead dispatch_skeleton + symm のみ)。
proof-done ゆえ削除せず残置。
@audit:ok -/
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

**@audit:superseded-by(entropyPowerExt_add_ge_unconditional)** (2026-06-08): case-2 対称版も #134 と同様、
旧 dispatch_skeleton 専用。無条件版 `entropyPowerExt_mixed_add_ge_symm_uncond` (`EPIUncondDispatchFull.lean`)
に置換され、無条件 headline チェーンからは到達しない (consumer = dead dispatch_skeleton のみ)。proof-done ゆえ残置。
@audit:ok -/
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

end InformationTheory.Shannon
