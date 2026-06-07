import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIUncondCondEntropyExt
import InformationTheory.Shannon.EPIUncondMonotone
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

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

/-- **per-n finite-entropy 単調性**: 各 n で `h(W_n) ≤ h(W_n + V)` を finite ②
(`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite`、11 regularity 仮説、`@audit:ok`) or
有限枝単調性経由で建てる。`truncW P W n` は compact support ゆえ有限分散・有限エントロピーで、
finite ② の 11 仮説 (joint 密度可測 / per-fibre KL 有限 等) を condDistrib で供給する。

route β' Phase 2 で埋める。`hn` (positive mass) は条件付けが well-defined な n を選ぶ scope
(load-bearing でない)。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(単調不等式 `h(W_n) ≤ h(W_n+V)`) は 6 仮説と非同型。(2) 非バンドル — `hW`/`hV`/`hWV`/`hW_ac`
は可測/独立/絶対連続の regularity、`hn` は cond well-defined の scope precondition、いずれも
単調性の核を encode せず (供給元 finite ② = `differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite`
が body 側に来る)。(3) 非退化 — `:True` slot なし。(4) sufficiency — compact support
(`{|W|≤n}` 条件付け) の有限分散・有限エントロピー measure で単調性が立つのは正しい (route T
が同 truncation で sorryAx-free 実証済)。`plan:` 妥当。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_mono_add_truncW
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) (n : ℕ) (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    differentialEntropyExt ((truncW P W n).map W)
      ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
  sorry

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
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  sorry

end InformationTheory.Shannon
