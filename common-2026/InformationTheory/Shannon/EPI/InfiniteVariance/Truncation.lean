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

## 進捗注記 (2026-06-07: 全 declaration genuine 化)

旧 Phase 1 では全 signature + `:= by sorry` の skeleton (各 `sorry` は
`@residual(plan:epi-infinite-variance-truncation-plan)`) だったが、現在は file 内 literal
`sorry` 0 件・全 declaration `@audit:ok` (sorryAx-free、独立 honesty audit 2026-06-07 PASS)。
helper は plan §推奨分解 (1-6) に対応。headline `entropyPowerExt_add_ge_infinite_variance_truncation`
も sorryAx-free (wall theorem `:1407` への接続は assembly で `hent_sum` 導出が残課題)。

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
import InformationTheory.Shannon.EPI.Case1.SmoothingLimit
import InformationTheory.Shannon.EPI.Stam.SupplyTwoTime
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Construction
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Density
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Convergence

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Helper 6 — headline 法則版 + assembly (plan §推奨分解 6, Phase 4) -/

/-- **headline (法則版)**: 無限分散 a.c. 古典 EPI。
per-n 黒箱 EPI (`entropyPowerExt_condTrunc_add_ge`) + crux usc
(`entropyPowerExt_condTrunc_sum_limsup_le`) + RHS 収束
(`entropyPowerExt_map_condTrunc_tendsto` ×2) を R→∞ で合成:
`N(X)+N(Y) = lim RHS_n ≤ limsup LHS_n ≤ N(X+Y)`。

⚠ 本版は和の有限微分エントロピー `hent_sum` を crux usc に渡すため明示引数で受ける
(wall theorem 側 signature には無い)。assembly で wall body から供給する設計
(compact support 経由 or 別途確立)。`hent_sum` は regularity precondition (有限微分
エントロピー)、結論を encode しない load-bearing でない。

独立 honesty audit 2026-06-07 (skeleton 段階、signature honesty + classification):
`hent_sum` は load-bearing でなく regularity precondition と確認 (core-reconstruction:
和エントロピー=+∞ なら Nₑ(P.map(X+Y))=⊤ で EPI 自明ゆえ、`hent_sum`=有限 は route T 適用
領域を切り出す前提であって EPI 不等式を encode しない)。⚠Phase 4 接続課題: wall theorem
`:1407` の仮説は global `hX_ent`/`hY_ent` (各成分) で `hent_sum` (和) を持たないため、
assembly では `hent_sum` を各成分の有限 entropy + a.c. から **genuine 導出** する必要がある
(両成分有限 entropy ⊬ 和有限 entropy は自明でない)。この導出が詰まっても `hent_sum` を
wall theorem の新規仮説に**昇格させない** (= signature load-bearing 化、tier 5)。詰まる
場合は当該導出補題に `sorry` + `@residual` で park。 -/
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
  -- Goal: `Nₑ(P.map X) + Nₑ(P.map Y) ≤ Nₑ(P.map(X+Y))`.
  rw [ge_iff_le]
  -- (1) RHS 収束: `Nₑ(P_n.map X) + Nₑ(P_n.map Y) → Nₑ(P.map X) + Nₑ(P.map Y)`.
  have hX_tendsto :
      Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map X)) atTop
        (𝓝 (entropyPowerExt (P.map X))) :=
    entropyPowerExt_map_condTrunc_tendsto P hX hY hXY (Or.inl rfl) hX_ac hX_ent
  have hY_tendsto :
      Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map Y)) atTop
        (𝓝 (entropyPowerExt (P.map Y))) :=
    entropyPowerExt_map_condTrunc_tendsto P hX hY hXY (Or.inr rfl) hY_ac hY_ent
  have hRHS_tendsto :
      Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map X)
          + entropyPowerExt ((condTrunc P X Y n).map Y)) atTop
        (𝓝 (entropyPowerExt (P.map X) + entropyPowerExt (P.map Y))) :=
    hX_tendsto.add hY_tendsto
  -- (2) per-n 不等式 (eventually): `Nₑ(P_n.map X) + Nₑ(P_n.map Y) ≤ Nₑ(P_n.map(X+Y))`.
  have hper_n :
      ∀ᶠ n in atTop,
        entropyPowerExt ((condTrunc P X Y n).map X)
            + entropyPowerExt ((condTrunc P X Y n).map Y)
          ≤ entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) := by
    filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
    exact entropyPowerExt_condTrunc_add_ge P hX hY hXY hX_ac hY_ac hX_ent hY_ent hpos
  -- (3) limsup chain.
  calc
    entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)
        = Filter.limsup (fun n => entropyPowerExt ((condTrunc P X Y n).map X)
            + entropyPowerExt ((condTrunc P X Y n).map Y)) atTop :=
          hRHS_tendsto.limsup_eq.symm
    _ ≤ Filter.limsup
          (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop :=
          Filter.limsup_le_limsup hper_n
    _ ≤ entropyPowerExt (P.map (fun ω => X ω + Y ω)) :=
          entropyPowerExt_condTrunc_sum_limsup_le
            P hX hY hXY hX_ac hY_ac hX_ent hY_ent hent_sum

end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
