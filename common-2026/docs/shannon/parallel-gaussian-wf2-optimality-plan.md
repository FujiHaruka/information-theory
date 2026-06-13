# Parallel Gaussian: L-WF2 water-filling 最適性 discharge サブ計画

> **Parent**: [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md) §撤退ライン **L-WF2**
>
> ✅ **DONE (2026-06-13)**: `KKT.isWaterFillingOptimal_of_kkt` genuine closure 完了
> (sorryAx-free `[propext, Classical.choice, Quot.sound]`、独立 honesty 監査 PASS = `@audit:ok`)。
> headline `parallel_gaussian_capacity_formula_minimal` も sorryAx-free 化。実装は当初計画の
> 凹 tangent 機構を使わず **`Real.log_le_sub_one_of_pos` を `u=(N_i+P'_i)/(N_i+P*_i)` に適用して
> tangent 上界 `1/(2(N_i+P*_i))` を直接導出**するより簡潔なルートで着地 (ConcaveOn/HasDerivAt 不要
> → tangent 補題移設も不要、orphan な `WFCertBody.lean` は削除)。

## 進捗

- [x] M0 在庫調査 — `Real.log_le_sub_one_of_pos` で tangent 上界を直接化 (ConcaveOn 機構不要と判明) ✅
- [x] skeleton — helper (`noise_pos` / `waterFillingKKT_level_pos` / `waterFillingCost_tangent_le`) ✅
- [x] 本体実装 — `isWaterFillingOptimal_of_kkt` genuine 証明 (sorryAx-free、`@audit:ok`) ✅

## ゴール / Approach

`KKT.isWaterFillingOptimal_of_kkt` の sorry を閉じる:

```
(P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i:ℝ) ≠ 0)
(ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) ⊢ IsWaterFillingOptimal P N ν
```

すなわち KKT 水準 `ν`(`∑ max(0, ν−N_i) = P`)において、water-filling 配分
`P_i^* = max(0, ν−N_i)` が制約集合 `{P' : ∀i 0≤P'_i, ∑P'_i ≤ P}` 上で凹和
`∑ (1/2)log(1+P'_i/N_i)` を最大化すること(Cover-Thomas 9.4.1 の最適化ステップ)。

**Approach (overall shape)**: 共通 KKT 乗数 `λ = 1/(2ν)` での凹 tangent 上界を各座標で足し上げ、
線形剰余を相補スラックネス + `λ≥0` + `∑P'_i ≤ P` で潰す Lagrange reduction。

1. **Phase A (済)**: 凹 tangent 上界 `ConcaveOn.le_tangent_of_hasDerivAt`
   (`WFCertBody.lean`、Mathlib slope 補題から汎用に discharge 済)。
2. **Phase B**: per-coord cost `g_i(t) = (1/2)log(1+t/N_i)` の凹性 + 導関数
   `g_i'(t) = 1/(2(N_i+t))`(Mathlib `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` 系 /
   `Real.log` concavity)。
3. **Phase C**: 共通乗数 `λ = 1/(2ν)` での per-coord stationarity 上界
   `g_i(P'_i) ≤ g_i(P_i^*) + λ·(P'_i − P_i^*)`(active: `N_i+P_i^*=ν` で導関数 `=λ`、
   inactive `P_i^*=0`: `g_i'(0)=1/(2N_i) ≤ λ` の slack を `P'_i−0 ≥ 0` が吸収)。
4. **Phase D**: 足し上げ + 相補スラックネス(`∑P_i^* = P` は h_kkt、`λ≥0` は `ν>0`)で
   `∑ g_i(P'_i) ≤ ∑ g_i(P_i^*)`。`ν > 0` は `h_kkt + hP` から(`ν ≤ min N_i` なら全 inactive で
   `∑=0≠P`)。

**壁ではない根拠**: 凸/凹解析 (`ConcaveOn`, slope, `HasDerivAt`) は Mathlib に揃っており、
Phase A は既に通っている。残りは self-buildable な ~150-250 行の KKT/concavity 代数。

## Phase 詳細

(M0 着手時に Phase B–D を per-step `- [ ]` で書き下す。)

## 判断ログ

- **2026-06-13 起票**: 旧 `WFCertBody.lean` / `WFStationarityBody.lean` の discharge は Phase A
  のみ実装で頓挫(後者は空スケルトンのため削除)。L-WF2 は headline で load-bearing 仮説 `h_opt`
  として運ばれていたが、ユーザー判断で sorry-routed に移行(`KKT.isWaterFillingOptimal_of_kkt`、
  `@residual(plan:parallel-gaussian-wf2-optimality-plan)`)。headline は L-WF2 について無条件形に
  なったが tier-2(transitive sorry)。本 plan はこの sorry の genuine closure を担う。
