import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIUncondMixedCase
import InformationTheory.Shannon.EPIInfiniteVarianceCapstone
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic

/-!
# EPI 無条件化 方針 Y — 拡張エントロピー単調性 (W-Y1 gateway atom)

完全無条件 EPI (方針 Y) の gateway。`entropyPowerExt_mono_add`:
W a.c. ∧ V indep ⟹ `N(W+V) ≥ N(W)`。

設計: まず **`EReal` レベルの単調性** `differentialEntropyExt_mono_add`
(`differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (W+V))`) を
3 枝 (`⊥` / coe / `⊤`) で示し、`EReal.exp_monotone` で `entropyPowerExt` に lift する。

- **−∞ 枝** (`differentialEntropyExt (P.map W) = ⊥`): `bot_le`。genuine。
- **有限枝** (`differentialEntropyExt (P.map W)` が coe = 有限微分エントロピー):
  Real 中核 `differentialEntropy_add_ge_of_indep` (`EPIUncondMixedCase.lean:76`) を lift。
  ただし **V a.c. + 8 integrability + W+V 有限エントロピー** が要り、これらは
  `entropyPowerExt_mono_add` の signature (a.c. のみ) からは出ない obligation。
- **+∞ 枝** (`differentialEntropyExt (P.map W) = ⊤`): `differentialEntropyExt (P.map (W+V)) = ⊤`
  (+∞ 伝播)。capstone Case 2 (`EPIInfiniteVarianceCapstone.lean:344-403`) の対称版
  (正部 `A=⊤` の伝播)。

SoT 計画: `docs/shannon/epi-uncond-deffix-monotone-plan.md` (P2 拡張単調性) +
`docs/shannon/epi-uncond-monotone-inventory.md` (W-Y1 在庫)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **+∞ 伝播 (W-Y1 核)**: `differentialEntropyExt (P.map W) = ⊤` (= `h(W) = +∞`、正部発散)
かつ `W ⊥ V` ⟹ `differentialEntropyExt (P.map (W+V)) = ⊤`。

畳み込みが正部 (裾) を保つことから。capstone Case 2
(`EPIInfiniteVarianceCapstone.lean:entropyPowerExt_add_ge_infinite_variance` `:344-403`、
`¬integrable ∧ B<⊤ → A=⊤`) の対称版。Mathlib 壁でなく extended-entropy plumbing
(親 def-fix plan §2/§4 P2、`plan:epi-uncond-deffix-monotone-plan` 予約済)。

**本 session で詰まった obstruction (feasibility 報告)**: `hW_top` を `differentialEntropyExt_of_ac`
で展開すると `A_W − B_W = ⊤` (EReal)、これは `A_W = ⊤ ∧ B_W < ⊤` を意味する (正部発散)。
RHS `differentialEntropyExt (P.map (W+V)) = ⊤` を出すには `A_{W+V} = ⊤ ∧ B_{W+V} < ⊤` が要る。
2 つの obligation がいずれも本 signature (W a.c. のみ、V は a.c. でない) から出ない:
- **`B_{W+V} < ⊤`** (和の負部可積分): capstone P 版負部補題 `integrable_negPart_negMulLog_map_sum`
  (`EPIInfiniteVarianceCapstone.lean:74`) が雛形だが、**`hY_ac` (V a.c.) + `hY_ent` (V 有限
  エントロピー) を要求**。本 signature は V a.c. すら持たない (V 特異も許す mono 形)。
- **`A_{W+V} = ⊤`** (和の正部発散 = +∞ 伝播本体): `negMulLog` の畳み込み下界 lemma が Mathlib 不在
  (loogle `Real.negMulLog, MeasureTheory.Measure.conv` = Found 0)。`h(W+V) ≥ h(W)` (= 本補題の
  上位) を density tail 評価で直接組む必要があり、conv 密度同定 (`rnDeriv_map_sum_ae`) も V a.c. 要。

→ feasibility 結論: +∞ 伝播は **V a.c. を signature に足すか、V 特異 case を別経路で処理するか**の
設計判断 (proof-pivot-advisor 案件) が要る。capstone Case 2 が単独測度 (¬integrable) で `A=⊤` を
出す機構は density 経由でなく非可積分性の直接対偶ゆえ、独立和の正部発散には移植できない。

独立 honesty audit 2026-06-07 (commit 4f81972): 4-check 全 PASS、classification `plan:` 妥当。
(1) 非循環 — 仮説 `differentialEntropyExt (P.map W) = ⊤` は W 単独の事実 (= `A_W=⊤ ∧ B_W<⊤`
正部発散)、結論は W+V について、body は `sorry` で `:= h` でない。(2) 非バンドル — 仮説は
measurability/indep/a.c./`= ⊤` で全て precondition、和の正部発散 (= 結論) を仮説に encode せず。
(3) 非退化 — 具体的 EReal 等式、退化境界 V≡0 (Dirac、特異、signature 許容) では W+V=W ゆえ
`h(W+V)=h(W)=⊤` で非 vacuous に成立。(4) **sufficiency — TRUE-as-framed**: 畳み込みは独立 V
との合成で裾 (正部発散) を消さない (和密度の裾は重い方の因子の裾が支配) ゆえ `A_{W+V}=⊤`、退化境界で
反例構成不能。**classification 判定**: `plan:epi-uncond-deffix-monotone-plan` 妥当 (wall でない)。
plan 実在 (§2/§4 P2)、loogle `Real.negMulLog, Measure.conv` = Found 0 (bare + conclusion-shape
`|- _ ≤ _` 二段とも 0、Mathlib off-the-shelf 不在) は確認したが、conv が裾を保つ lintegral 評価は
elementary measure theory で self-buildable plumbing (genuine Mathlib gap でない)、plan が closure を
明示所有 (~80-150 行見積、inventory L198-201/223-224)。現 signature が V a.c. を欠くため
`rnDeriv_map_sum_ae` (V a.c. 要) 経由の conv 密度同定が呼べない = signature 設計課題だが、これは
plan 内で V a.c. 追加 or 別経路で解決する範囲 (closeable)。verdict: honest_residual。

@residual(plan:epi-uncond-deffix-monotone-plan) -/
theorem differentialEntropyExt_top_of_indep_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  sorry

/-- **EReal レベル拡張単調性** (W-Y1): `W a.c. ∧ W ⊥ V ⟹
`differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (W+V))`。

3 枝:
- `⊥` 枝: `bot_le` (genuine)。
- coe (有限) 枝: Real 中核 `differentialEntropy_add_ge_of_indep` を lift。V a.c. + 8 integrability +
  W+V 有限エントロピー要 (signature の a.c. のみからは出ない obligation)。
- `⊤` 枝: `differentialEntropyExt_top_of_indep_add` (+∞ 伝播)。

複数 sorry: 各 sorry 直前に `@residual` を付す。

独立 honesty audit 2026-06-07 (commit 4f81972): 4-check 全 PASS。⊥ 枝 = `bot_le` genuine、
⊤ 枝 = `_top_of_indep_add` thread (genuine reduction、循環でない)。有限枝 sorry (`:97`) の
classification `plan:` 妥当: Real 中核 `differentialEntropy_add_ge_of_indep` (`EPIUncondMixedCase.lean:76`)
を lift する経路は genuine だが、その 8+ integrability/a.c. precondition (`hW_ac` for `P.map Y`、
compProd `h_ac`、fibre/cross integrability 等) は `hW_ac` (W a.c.) 単独からは出ない genuine
regularity obligation で、和エントロピー結論を仮説に encode しない (非バンドル)。plan §3 が
closure を所有。verdict: honest_residual (⊤/有限 両 sorry とも)。 -/
theorem differentialEntropyExt_mono_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (fun ω => W ω + V ω)) := by
  -- trichotomy on `differentialEntropyExt (P.map W) ∈ {⊥, ⊤, coe}`.
  rcases eq_bot_or_bot_lt (differentialEntropyExt (P.map W)) with hbot | hpos
  · -- −∞ 枝 (h(W) = −∞ ピーク密度): `⊥ ≤ _`. genuine.
    rw [hbot]; exact bot_le
  · rcases eq_top_or_lt_top (differentialEntropyExt (P.map W)) with htop | hfin
    · -- +∞ 枝 (h(W) = +∞ 裾密度): `+∞ 伝播` で RHS = ⊤、`le_top`.
      rw [differentialEntropyExt_top_of_indep_add W V P hW hV hWV hW_ac htop]
      exact le_top
    · -- 有限枝 (h(W) coe ↑x): Real 中核 `differentialEntropy_add_ge_of_indep` を lift。
      -- ただし V a.c. + 8 integrability + W+V 有限エントロピー要 = signature (a.c. のみ) からは
      -- 出ない obligation。
      -- @residual(plan:epi-uncond-deffix-monotone-plan)
      sorry

/-- **拡張エントロピーパワー単調性** (W-Y1 gateway atom): `W a.c. ∧ W ⊥ V ⟹ N(W+V) ≥ N(W)`。
`differentialEntropyExt_mono_add` (EReal 単調性) を `EReal.exp_monotone` で `entropyPowerExt`
(= `EReal.exp (2 · differentialEntropyExt)`) に lift する。

方針 Y (完全無条件 EPI) の gateway: case-2 (X a.c., Y 特異) や ±∞ 退化境界の closure に使う。
genuine lift: hard core は `differentialEntropyExt_mono_add` 内。

独立 honesty audit 2026-06-07 (commit 4f81972): lift 自体は genuine (`EReal.exp_monotone` +
`mul_le_mul_of_nonneg_left`、循環/バンドル/退化なし、signature は integrability を encode せず
`hW`/`hV`/`hWV`/`hW_ac` のみ = 非バンドル PASS)。ただし **`@audit:ok` (tier 1) ではない**:
本 atom は `differentialEntropyExt_mono_add` の有限枝・⊤ 枝 sorry を transitive 継承する
(`#print axioms` は `sorryAx` 依存になる見込み)。verdict: honest_residual (transitive、
上流 2 sorry が `plan:epi-uncond-deffix-monotone-plan` で closure された時点で proof-done 昇格)。 -/
theorem entropyPowerExt_mono_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    entropyPowerExt (P.map (fun ω => W ω + V ω)) ≥ entropyPowerExt (P.map W) := by
  unfold entropyPowerExt
  apply EReal.exp_monotone
  exact mul_le_mul_of_nonneg_left
    (differentialEntropyExt_mono_add W V P hW hV hWV hW_ac) (by norm_num)

end InformationTheory.Shannon
