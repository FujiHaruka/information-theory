/-
# 無限分散 a.c. 古典 EPI — conditioning truncation ルート (route T)

`entropyPowerExt_add_ge_infinite_variance` (`EPICase1SmoothingLimit.lean:1407`,
`@residual(wall:epi-infinite-variance-classical)`) の genuine closure を目指す moonshot
の skeleton (Phase 1)。両 a.c. + 両有限微分エントロピー + 無限分散の独立和に対する古典
entropy power inequality `Nₑ(X+Y) ≥ Nₑ(X) + Nₑ(Y)` を、有限分散 EPI 黒箱
`entropyPowerExt_add_ge_of_finite_variance` (`:1351`, sorryAx-free) を conditioning 切詰
`X_n := X | {|X|≤n ∧ |Y|≤n}` に適用して R→∞ で繋ぐルート T で構築する。

## Approach (route T, Phase 0 で確定)

`P_n := P[| {ω | |X ω| ≤ n ∧ |Y ω| ≤ n}]` (両成分同時 conditioning) は:
- compact support (両成分有界) → 有限 2 次モーメント (有限分散) + 有限微分エントロピー
- a.c. 保存 (`cond_absolutelyContinuous` + `Measure.map` の a.c. mono)
- 独立性保存 (joint 矩形事象 `X⁻¹[-n,n] ∩ Y⁻¹[-n,n]` での conditioning は `IndepFun X Y` を保つ)

ゆえに各 n で黒箱 EPI が立つ: `Nₑ(P_n.map (X+Y)) ≥ Nₑ(P_n.map X) + Nₑ(P_n.map Y)`。

最終 assembly (clean limsup chain, moment 非依存):
1. 黒箱 per n: `N(P_n.map(X+Y)) ≥ N(P_n.map X) + N(P_n.map Y)`。
2. crux usc: `N(P.map(X+Y)) ≥ limsup_n N(P_n.map(X+Y))` (Gibbs + cross-entropy DCT)。
3. RHS 収束: `N(P_n.map X) → N(P.map X)`, `N(P_n.map Y) → N(P.map Y)`。
4. 合成: `N(P.map(X+Y)) ≥ limsup N(P_n.map(X+Y)) ≥ lim[N(P_n.map X)+N(P_n.map Y)]
   = N(P.map X)+N(P.map Y)`。

crux usc は Gibbs step (`(klDiv (P_n.map(X+Y)) (P.map(X+Y))).toReal ≥ 0`、in-tree template
`differentialEntropy_le_gaussian_of_variance_le` を Gaussian → 一般参照 generalize) +
cross-entropy DCT (優関数 `p_n∗q_n ≤ C²(p∗q)`、`tendsto_integral_of_dominated_convergence`)。
分散発散は red herring (固定参照 = p∗q で moment 非依存に閉じる)。

## skeleton 注記 (Phase 1)

本 file は全 signature + `:= by sorry` の skeleton。各 `sorry` は
`@residual(plan:epi-infinite-variance-truncation-plan)` (buildable な未完成、wall でない)。
fill は別 Phase で dispatch。helper は plan §推奨分解 (1-6) に対応。

設計判断:
- **R の型**: `n : ℕ`、切詰集合 `{|X|≤n ∧ |Y|≤n}` (monotone over n、`atTop` filter で
  monotone/dominated convergence が素直、在庫 B8b と整合)。
- **conditioning API**: `ProbabilityTheory.cond P s = (P s)⁻¹ • P.restrict s`
  (`ConditionalProbability.lean:74`)。a.c. 保存は `cond_absolutelyContinuous` (`:183`)。
- **構成手段**: 素朴 indicator truncation `1_{|X|≤n}·X` は law に atom を作り a.c. を壊す
  (在庫 §E #2 隠れ難所)。conditioning で迂回。
- **Measure.conv 非使用**: 黒箱は RV 形 `P.map (fun ω => X ω + Y ω)` で動く。畳込みは
  `P_n.map (X+Y)` に暗黙に含まれ、`Measure.conv` を明示展開しない。
- **独立性保存**: 黒箱は `IndepFun X Y P_n` を要求。同時 conditioning で矩形事象ゆえ保存
  (helper `indepFun_cond_truncSet`)。
-/
import InformationTheory.Shannon.EPICase1SmoothingLimit

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **切詰集合** `truncSet X Y n := {ω | |X ω| ≤ n ∧ |Y ω| ≤ n}` (両成分同時切詰、
矩形事象)。`n : ℕ` で monotone increasing、`⋃ n = univ` (各 ω で `|X ω|, |Y ω|` 有限)。 -/
def truncSet (X Y : Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | |X ω| ≤ (n : ℝ) ∧ |Y ω| ≤ (n : ℝ)}

/-- 切詰集合は可測 (X, Y 可測から). -/
theorem measurableSet_truncSet {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (n : ℕ) :
    MeasurableSet (truncSet X Y n) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- 切詰集合の単調性 (`n ≤ m → truncSet X Y n ⊆ truncSet X Y m`)。 -/
theorem truncSet_mono {X Y : Ω → ℝ} : Monotone (truncSet X Y) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- 切詰集合の和集合は全体 (`⋃ n, truncSet X Y n = univ`)。各 ω で `|X ω|, |Y ω|` が
有限ゆえ十分大きい n で含まれる (`exists_nat_ge`). -/
theorem iUnion_truncSet (X Y : Ω → ℝ) : ⋃ n, truncSet X Y n = Set.univ := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **conditioning 確率測度** `P_n := P[| truncSet X Y n]`。十分大きい n で
`P (truncSet X Y n) > 0` (和集合が全体ゆえ measure → 1) なので probability measure。 -/
noncomputable def condTrunc (P : Measure Ω) (X Y : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P (truncSet X Y n)

/-! ### Helper 1 — truncation 構成 + regularity (plan §推奨分解 1) -/

/-- `P (truncSet X Y n) → 1` (n→∞、和集合が全体 + `IsProbabilityMeasure`)。
ゆえに十分大きい n で `P (truncSet X Y n) ≠ 0`。 -/
theorem measure_truncSet_tendsto_one (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Tendsto (fun n => P (truncSet X Y n)) atTop (𝓝 1) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- 十分大きい n では `P (truncSet X Y n) ≠ 0` (measure → 1)。
以降の per-n 補題は `n ≥ N₀` (positive mass) で立てる。 -/
theorem eventually_measure_truncSet_pos (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    ∀ᶠ n in atTop, P (truncSet X Y n) ≠ 0 := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- `condTrunc P X Y n` は確率測度 (positive mass の n で)。 -/
theorem isProbabilityMeasure_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    IsProbabilityMeasure (condTrunc P X Y n) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **独立性保存**: `IndepFun X Y P` → `IndepFun X Y (condTrunc P X Y n)`。
同時 conditioning が矩形事象 `X⁻¹[-n,n] ∩ Y⁻¹[-n,n]` ゆえ独立性を保つ。
honest: 結論 `IndepFun` を仮説 `IndepFun` から導く regularity 保存補題。 -/
theorem indepFun_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    IndepFun X Y (condTrunc P X Y n) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **a.c. 保存**: `(P.map X) ≪ volume` → `((condTrunc P X Y n).map X) ≪ volume`。
`cond_absolutelyContinuous` (`(condTrunc) ≪ P`) + `Measure.map` の a.c. mono で合成。 -/
theorem map_condTrunc_absolutelyContinuous (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume) {n : ℕ} :
    ((condTrunc P X Y n).map Z) ≪ volume := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 2 — per-n regularity 供給 (plan §推奨分解 2) -/

/-- **per-n 有限 2 次モーメント** `Integrable ((Z ·)²) (condTrunc P X Y n)`。
`condTrunc` は `truncSet ⊆ {|X|≤n ∧ |Y|≤n}` に supported → Z = X or Y は有界 (`|Z|≤n`)
→ 2 次モーメント有界。`MemLp 2` 自動 (compact support)。在庫 §D `IndepFun.variance_add`
の `MemLp 2` 前提を満たすための核。 -/
theorem integrable_sq_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) (hZ : Z = X ∨ Z = Y) :
    Integrable (fun ω => (Z ω) ^ 2) (condTrunc P X Y n) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **per-n 有限微分エントロピー (各成分)** `Integrable (negMulLog (rnDeriv ·)) volume` for
`(condTrunc P X Y n).map Z`。compact support → bounded density → integrable。
黒箱 `entropyPowerExt_add_ge_of_finite_variance` の `hX_ent`/`hY_ent` 引数を再供給。 -/
theorem integrable_negMulLog_map_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume) {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => Real.negMulLog (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal) volume := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **per-n 和の有限微分エントロピー** (`hent_sum` 再供給)。compact support の和 X+Y も
有界密度 → integrable。黒箱 `entropyPowerExt_add_ge_of_finite_variance` は `hent_sum` を
明示引数で要求するので必須 (wall theorem 側には無い、在庫 §D)。 -/
theorem integrable_negMulLog_map_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => Real.negMulLog
        (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 黒箱配線 — per-n EPI -/

/-- **per-n 有限分散 EPI** (黒箱 `entropyPowerExt_add_ge_of_finite_variance` への配線)。
helper 1/2 で全 regularity を供給し、各 n (positive mass) で
`Nₑ(P_n.map(X+Y)) ≥ Nₑ(P_n.map X) + Nₑ(P_n.map Y)` を得る。 -/
theorem entropyPowerExt_condTrunc_add_ge (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt ((condTrunc P X Y n).map X)
        + entropyPowerExt ((condTrunc P X Y n).map Y) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 3 — 優関数 + generalized Gibbs (plan §推奨分解 3) -/

/-- **generalized Gibbs (cross-entropy 下界)**: a.c. な `μ ≪ ν` (ともに probability) で
`differentialEntropy μ ≤ -∫ x, log (ν.rnDeriv volume x).toReal ∂μ` (cross-entropy)。
`(klDiv μ ν).toReal ≥ 0` (klDiv は ℝ≥0∞ 値、`ENNReal.toReal_nonneg` で型自明) +
`toReal_klDiv_of_measure_eq` の llr 分解から。in-tree template
`differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`) の
Gaussian 参照 ν を一般参照に generalize した版。 -/
theorem differentialEntropy_le_cross_entropy {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_ac : μ ≪ volume) (hν_ac : ν ≪ volume) (hμν : μ ≪ ν)
    (hμ_ent : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume)
    (h_cross_int : Integrable
      (fun x => Real.log ((ν.rnDeriv volume x).toReal)) μ) :
    differentialEntropy μ ≤ - ∫ x, Real.log ((ν.rnDeriv volume x).toReal) ∂μ := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 4 — crux usc (plan §推奨分解 4, genuine sub-wall 候補) -/

/-- **crux usc (微分エントロピー版)**: `limsup_n h(P_n.map(X+Y)) ≤ h(P.map(X+Y))`。
Gibbs step (`differentialEntropy_le_cross_entropy` で h(P_n.map(X+Y)) を cross-entropy
`-∫(p_n∗q_n)log(p∗q)` で上から抑える) + cross-entropy DCT (優関数 `C²(p∗q)|log(p∗q)|`、
和の有限微分エントロピーで可積分、`tendsto_integral_of_dominated_convergence` で
`→ -∫(p∗q)log(p∗q) = h(p∗q)`)。本 moonshot の核。 -/
theorem differentialEntropy_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **crux usc (entropyPower 版)**: `limsup_n Nₑ(P_n.map(X+Y)) ≤ Nₑ(P.map(X+Y))`。
微分エントロピー版 (`differentialEntropy_condTrunc_sum_limsup_le`) を `entropyPowerExt`
= `exp (2·h)` の単調連続変換で lift。 -/
theorem entropyPowerExt_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ entropyPowerExt (P.map (fun ω => X ω + Y ω)) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 5 — RHS 収束 (plan §推奨分解 5) -/

/-- **RHS 収束 (微分エントロピー版)**: `h(P_n.map Z) → h(P.map Z)` (各成分)。
恒等式 `-∫ p_n log p_n = -(1/m_n)∫_{truncSet} p log p + log m_n`、第 1 項は固定可積分
`p log p` の growing-set monotone/dominated convergence、第 2 項は `m_n → 1` → `log m_n → 0`。
moment 非依存 (固定可積分関数 `p log p` のみ)。 -/
theorem differentialEntropy_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => differentialEntropy ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (differentialEntropy (P.map Z))) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **RHS 収束 (entropyPower 版)**: `Nₑ(P_n.map Z) → Nₑ(P.map Z)`。
微分エントロピー版を `entropyPowerExt = exp (2·h)` の連続変換で lift。 -/
theorem entropyPowerExt_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (entropyPowerExt (P.map Z))) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 6 — headline 法則版 + assembly (plan §推奨分解 6, Phase 4) -/

/-- **headline (法則版)**: 無限分散 a.c. 古典 EPI。
per-n 黒箱 EPI (`entropyPowerExt_condTrunc_add_ge`) + crux usc
(`entropyPowerExt_condTrunc_sum_limsup_le`) + RHS 収束
(`entropyPowerExt_map_condTrunc_tendsto` ×2) を R→∞ で合成:
`N(X)+N(Y) = lim RHS_n ≤ limsup LHS_n ≤ N(X+Y)`。

⚠ 本版は和の有限微分エントロピー `hent_sum` を crux usc に渡すため明示引数で受ける
(wall theorem 側 signature には無い)。assembly で wall body から供給する設計
(compact support 経由 or 別途確立)。`hent_sum` は regularity precondition (有限微分
エントロピー)、結論を encode しない load-bearing でない。 -/
theorem entropyPowerExt_add_ge_infinite_variance_truncation
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
