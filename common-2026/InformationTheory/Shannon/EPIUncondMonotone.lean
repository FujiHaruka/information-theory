import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIUncondMixedCase
import InformationTheory.Shannon.EPIInfiniteVarianceCapstone
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# EPI 無条件化 方針 Y — 拡張エントロピー単調性 (W-Y1 gateway atom)

完全無条件 EPI (方針 Y) の gateway。`entropyPowerExt_mono_add`:
W a.c. ∧ V indep ⟹ `N(W+V) ≥ N(W)`。

設計 (2026-06-07 route α-ii、§7-6 SoT): **単一 crux 恒等式 (i-a)** を中心に restructure。
trichotomy 分解 (⊥/coe/⊤ 枝の個別 sorry) を廃し、唯一の RED を恒等式本体に局所化する。

- **crux 恒等式 (i-a)** `differentialEntropyExt_indep_add_eq_add_klDiv`:
  `h_ext(W+V) = h_ext(W) + I(W+V;V)` (`I = klDiv(joint ‖ product) ≥ 0`、ℝ≥0∞ → EReal coe)。
  `h(W) ≠ ⊥` 制限必須 (h(W)=⊥ で `⊥+⊤=⊥` ≠ 有限 LHS で FALSE、⊥ 枝は `bot_le` で別処理)。
  本体は EReal chain rule の self-build (§7-6 道 A = condDifferentialEntropyExt 経由)、唯一の sorry。
- **単調性** `differentialEntropyExt_mono_add`: (i-a) で書換 → `a ≤ a + (klDiv:EReal)` (nonneg)。
  ⊥ 枝は `bot_le`。**modulo (i-a) で genuine** (旧 coe/⊤ 枝 sorry は消滅、8 integrability obligation 不要化)。
- **+∞ 伝播** `differentialEntropyExt_top_of_indep_add`: mono の **genuine 系**
  (`h(W)=⊤ ≤ h(W+V) ⟹ h(W+V)=⊤`、`top_le_iff`)。旧 sorry 削除。
- **gateway atom** `entropyPowerExt_mono_add`: mono を `EReal.exp_monotone` で lift (変更不要)。

定義順 (循環回避): (i-a) → `mono_add` → `top_of_indep_add` → `entropyPowerExt_mono_add`。

SoT 計画: `docs/shannon/epi-uncond-deffix-monotone-plan.md` §7 (特に §7-6) +
`docs/shannon/epi-uncond-monotone-inventory.md` (W-Y1 在庫)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **crux 恒等式 (route α-ii、§7-6 SoT)**: `W a.c. ∧ W ⊥ V ∧ h(W) ≠ ⊥` ⟹
`h_ext(W+V) = h_ext(W) + I(W+V; V)`、ここで `I = klDiv(joint ‖ product)` は ℝ≥0∞ 値で非負、
`joint = (P.map V) ⊗ₘ condDistrib (W+V) V P`、`product = (P.map V) ⊗ₘ Kernel.const ℝ (P.map (W+V))`。

機構: `h(W+V) = h(W+V | V) + I(W+V; V)` (chain rule) かつ `h(W+V | V) = h(W)` (fibre 同定 c=1、
独立和の fibre は z 非依存定数 `h_ext(P.map W)`) で `h(W+V) = h(W) + I`。本体 = EReal chain rule の
self-build (§7-6 道 A = `condDifferentialEntropyExt : … → EReal` 新規定義 + 既存 genuine 2 lemma
`condDifferentialEntropy_indep_add_eq` (fibre 同定) / `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv`
(chain rule、Real bridge) の EReal 版自作)、~150-300 行 multi-session moonshot。

**`h(W) ≠ ⊥` 制限の理由**: h(W)=⊥ では RHS = `⊥ + ⊤ = ⊥` ≠ 有限/⊤ の LHS で FALSE になりうる
(⊥ 枝は `bot_le` で別処理、本恒等式の対象外)。これは regularity precondition であり結論を仮説に
encode しない (klDiv 項は結論の一部、仮説でない)。`hW_ac` は密度同定 (`rnDeriv_map`) の precondition。

§7-6 GREEN (probe `/tmp/epi_route_alpha_probe.lean` `probe_target_identity_clean` で型整合確認済):
本恒等式 1 本 landing で gateway atom の +∞ 伝播・有限枝 sorry が一括 closure し trichotomy 分解ごと
不要化 (`probe_mono_from_identity` が「恒等式 ⟹ mono 3 枝」を 0 sorry 確認、`probe_top_propagation_from_identity`
が ⊤ 伝播を確認)。RED = 本恒等式本体のみ。classification `plan:`: known-shape self-build (EReal-conditioning)、
Mathlib-不能 wall でない (§7-6、道 A chain rule が型壁で 2-3 session 詰まれば §7-4 判断点で `wall:` 昇格)。

独立 honesty audit 2026-06-07 (crux i-a): **honest_residual** (PASS、tier 2)。4-check:
(1) 非循環 — 結論 = entropy 分解恒等式、いずれの仮説型 (Measurable/IndepFun/≪/≠⊥) とも非同型、body は素の sorry。
(2) 非バンドル — 全仮説が regularity (可測性・独立・絶対連続・有限側 `≠⊥`)、`*Hypothesis`/`IsXxxClaim` predicate 不在。
**klDiv 項は結論 RHS の一部** (I(W+V;V)、`InformationTheory.klDiv : Measure→Measure→ℝ≥0∞` を EReal coe)、
仮説に不等式核を抱えていない (load-bearing でない、core-reconstruction 不発火)。
(3) 非退化 — `hW_ne_bot` は vacuous truth 化でなく、h(W)=⊥ の **偽になる枝を除外** する honest scope (⊥ 枝は mono 側
`bot_le` で別処理)、body は exfalso 退化悪用なし (素の sorry)。signature は将来も vacuous 化しない (≠⊥ は実質制約)。
(4) sufficiency — 反例 3 試行で棄却: V≡0(Dirac) で W+V=W・joint=product・klDiv=0 → `h(W)=h(W)+0` ✓;
W⊥V 非退化・h(W) 有限 で恒等式 = MI 分解 I(W+V;V)=h(W+V)−h(W+V|V)・h(W+V|V=v)=h(W)(定数 shift 不変) ✓;
h(W)=⊥ 退化境界は `hW_ne_bot` が正しく除外 (この枝で恒等式 FALSE)。仮説⊢結論が semantic に follow、under-hypothesized でない。
classification `plan:` **妥当** (PASS): plan 実在 (`docs/shannon/epi-uncond-deffix-monotone-plan.md` §7-2/§7-6 が closure 所有)、
機構 2 lemma の Real 版が genuine 既存 (`EPIG2ConvEntropyMonotone.lean:328` fibre 同定 / `:124` chain rule bridge)、
残務 = それらの EReal 版 self-build = known-shape (Mathlib-不能 wall でない)。`wall:` 過大評価でない: 道 B 入口
`klDiv_eq_lintegral_klFun_of_ac` は Mathlib 存在 (loogle 確認)、道 A は既存 Real 資産の EReal 化で回避可。conclusion-shape
反証義務充足 (機構部品が genuine に在庫、loogle Found 0 は道 B の condDistrib↔rnDeriv 繋ぎ 1 component のみ)。
@residual(plan:epi-uncond-deffix-monotone-plan) -/
theorem differentialEntropyExt_indep_add_eq_add_klDiv
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_ne_bot : differentialEntropyExt (P.map W) ≠ ⊥) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω))
      = differentialEntropyExt (P.map W)
        + (((InformationTheory.klDiv ((P.map V) ⊗ₘ condDistrib (fun ω => W ω + V ω) V P)
                ((P.map V) ⊗ₘ Kernel.const ℝ (P.map (fun ω => W ω + V ω)))) : ℝ≥0∞) : EReal) := by
  sorry

/-- **EReal レベル拡張単調性** (W-Y1): `W a.c. ∧ W ⊥ V ⟹
`differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (W+V))`。

route α-ii (§7-6): 恒等式 (i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` で書換 →
`a ≤ a + (klDiv:EReal)` (klDiv ≥ 0)。⊥ 枝のみ `bot_le` で別処理 (恒等式の `h(W)≠⊥` 制限外)。

**modulo (i-a) で genuine**: trichotomy 分解 (旧 coe/⊤ 枝の個別 sorry + 8 integrability obligation)
は不要化、(i-a) が internalize する。⊥ 枝 = `bot_le` genuine、非⊥ 枝 = §7-6 GREEN 算術
(probe `probe_mono_from_identity` 移植、0 sorry)。

独立 honesty audit 2026-06-07: **honest_residual** (PASS、modulo i-a)。body に独立 sorry なし、
`#print axioms` (transient) = `[propext, sorryAx, Classical.choice, Quot.sound]` で sorryAx は (i-a)
**transitive 継承のみ** (機械確認、build clean: line 64 crux のみ sorry warning)。⊥ 枝 `bot_le` genuine、
非⊥ 枝は (i-a) を rw 後 `a ≤ a + ((klDiv:ℝ≥0∞):EReal)` を `klDiv≥0` (= `ℝ≥0∞` の `bot_le` を EReal coe、
**型自明** な非負) + `add_le_add_right` で閉じる genuine 算術。循環/バンドル/退化なし、signature は
`hW`/`hV`/`hWV`/`hW_ac` のみ (integrability/結論を encode せず非バンドル)。(i-a) closure で proof-done 昇格。 -/
theorem differentialEntropyExt_mono_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (fun ω => W ω + V ω)) := by
  rcases eq_bot_or_bot_lt (differentialEntropyExt (P.map W)) with hbot | hpos
  · -- ⊥ 枝 (h(W) = −∞): `⊥ ≤ _`. genuine.
    rw [hbot]; exact bot_le
  · -- h(W) ≠ ⊥: 恒等式 (i-a) で書換 → `a ≤ a + (klDiv:EReal)` (nonneg).
    have hne_bot : differentialEntropyExt (P.map W) ≠ ⊥ := hpos.ne'
    rw [differentialEntropyExt_indep_add_eq_add_klDiv W V P hW hV hWV hW_ac hne_bot]
    have hi : (0 : EReal) ≤
        (((InformationTheory.klDiv ((P.map V) ⊗ₘ condDistrib (fun ω => W ω + V ω) V P)
              ((P.map V) ⊗ₘ Kernel.const ℝ (P.map (fun ω => W ω + V ω)))) : ℝ≥0∞) : EReal) := by
      exact_mod_cast (bot_le : (⊥ : ℝ≥0∞) ≤ _)
    calc differentialEntropyExt (P.map W)
        = differentialEntropyExt (P.map W) + 0 := (add_zero _).symm
      _ ≤ differentialEntropyExt (P.map W) + _ := add_le_add_right hi _

/-- **+∞ 伝播 (mono の genuine 系)**: `h(W) = ⊤` ⟹ `h(W+V) = ⊤`。
単調性 `differentialEntropyExt_mono_add` (`h(W) ≤ h(W+V)`) + `top_le_iff`。

旧 sorry 削除 (genuine corollary)。定義順: (i-a) → `mono_add` → 本系 (mono を呼ぶ)、
元の forward 依存 (`mono_add` が本系を呼ぶ) は逆転済で循環なし。

独立 honesty audit 2026-06-07: **honest_residual** (PASS、modulo i-a)。**循環なし機械確認**: body は
`mono_add` を呼び `top_le_iff` で閉じる (top → mono → (i-a) の acyclic chain)、`mono_add` は (i-a) を直接
呼び本系を呼ばない (forward 逆転後の再循環なし)。`#print axioms` (transient) で sorryAx は (i-a) transitive
継承のみ (独自 sorry なし、build で line 64 crux のみ sorry warning)。`hW_top` は h(W)=⊤ を表明する
場合分け precondition (load-bearing でない)。genuine corollary、(i-a) closure で proof-done 昇格。 -/
theorem differentialEntropyExt_top_of_indep_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  have h := differentialEntropyExt_mono_add W V P hW hV hWV hW_ac
  rw [hW_top] at h
  exact top_le_iff.mp h

/-- **拡張エントロピーパワー単調性** (W-Y1 gateway atom): `W a.c. ∧ W ⊥ V ⟹ N(W+V) ≥ N(W)`。
`differentialEntropyExt_mono_add` (EReal 単調性) を `EReal.exp_monotone` で `entropyPowerExt`
(= `EReal.exp (2 · differentialEntropyExt)`) に lift する。

方針 Y (完全無条件 EPI) の gateway: case-2 (X a.c., Y 特異) や ±∞ 退化境界の closure に使う。
genuine lift: hard core は `differentialEntropyExt_mono_add`、その唯一の RED は crux 恒等式
`differentialEntropyExt_indep_add_eq_add_klDiv` (i-a)。

lift 自体は genuine (`EReal.exp_monotone` + `mul_le_mul_of_nonneg_left`、循環/バンドル/退化なし、
signature は integrability を encode せず `hW`/`hV`/`hWV`/`hW_ac` のみ = 非バンドル)。ただし
**`@audit:ok` (tier 1) ではない**: 本 atom は (i-a) sorry を transitive 継承する
(`#print axioms` は `sorryAx` 依存になる見込み)。(i-a) が `plan:epi-uncond-deffix-monotone-plan`
で closure された時点で本 atom + mono + 伝播が一括 proof-done 昇格。 -/
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
