# EPI Stam → conclusion Phase A: Stam + de Bruijn 合流 (Csiszár scaling) サブ計画

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A (line 467-547)
> **Created**: 2026-05-25 (Phase D 合流 commit `c0edbe1` 直後、planner 起草)
> **Status**: 設計起草 (Phase A 着手前の Mathlib-shape-driven mini-plan)

## Position

- 親 sub-plan: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) Phase A
  (Stam + de Bruijn 合流 → `IsStamToEPIBridgeHyp` genuine 化)
- 上流入力 (両方とも Phase D 完了済、sister 出力):
  - [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) Phase D — `IsStamInequalityHyp`
    の genuine discharge (Cover-Thomas Lemma 17.7.2 内部)
  - [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) Phase D
    (= [`epi-debruijn-integration-phaseD-plan.md`](epi-debruijn-integration-phaseD-plan.md)、
    今日 commit `c0edbe1`) — `csiszarGap` 定義 + endpoint lemma + `rfl` shape contract
- 下流: 本 Phase 完了で主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232`)
  が hypothesis-free `theorem` に格上げ、続いて親 plan §Phase B / §Phase V へ進行

## Motivation

Phase 0 (commit `0d54e89`/`78cf2ec`/`2809168`) で `IsStamToEPIScalingHyp`
(`EPIStamToBridge.lean:202-216`) の signature を `∃ Z_X Z_Y, ... ∧ AntitoneOn gap (Set.Icc 0 1)`
に refactor 済。Phase D (commit `c0edbe1`) で sister の `csiszarGap`
(`EPIL3Integration.lean:1160-1164`) が新規 `IsStamToEPIScalingHyp` body の `AntitoneOn` 引数
lambda body と **verbatim 同形** で publish され、`csiszarGap_shape_for_sister`
(`EPIL3Integration.lean:1279-1287`) `rfl` lemma で接続を保証。

本 Phase A はこの 2 つの handoff を消費して **`AntitoneOn (fun s => csiszarGap X Y Z_X Z_Y P s)
(Set.Icc 0 1)` を Stam + de Bruijn から genuine 構築する**:

1. **path-derivative `d/ds (csiszarGap _) ≤ 0`** を de Bruijn V2 + Stam で導出
2. **`antitoneOn_of_deriv_nonpos`** (Mathlib) で `AntitoneOn` 結論を構成
3. これを `IsStamToEPIScalingHyp` の existential witness `Z_X, Z_Y` 構築 (standard normal,
   joint independent) と合わせて genuine constructor
   `isStamToEPIScalingHyp_of_stam_debruijn` として publish
4. 既存 `isStamToEPIBridgeHyp_of_scaling` (`EPIStamToBridge.lean:672`、`@audit:ok`、
   `IsStamToEPIScalingHyp` 単独で `IsStamToEPIBridgeHyp` 構築、`IsStamToEPILimitHyp` 不要)
   経由で `IsStamToEPIBridgeHyp` genuine 化、`IsEPIL3IntegratedPipeline.bridge` field を
   hypothesis-free に (2026-05-25 A-5 simplify: 当初 `_of_scaling_limit` 経由予定だったが、
   `_of_scaling` 直接呼出に simplify、`IsStamToEPILimitHyp` 構築の design error も解消)
5. 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232-240`) の `h_bridge`
   引数を削除 (`h_bridge := isStamToEPIBridgeHyp_of_stam_debruijn ...`)、genuine `theorem` 格上げ

**前提条件 verbatim 照合** (CLAUDE.md「具体的数値・型予測の verbatim 確認」遵守、Phase D 由来の
drift 防止):

| 確認対象 | 実コード | verbatim 値 |
|---|---|---|
| `entropyPower (Measure.dirac 0)` | `DifferentialEntropy.lean:147` + `entropyPower` def `EntropyPowerInequality.lean:80` | `= Real.exp (2 · 0) = 1` (∴ Y := 0 退化境界は constant `-1` gap 発生、trivially `AntitoneOn` で degenerate-definition exploitation 直撃) |
| `heatFlowPath2 X Z 0` | `HeatFlowPath.lean:49-52` | `= X` (funext, `Real.sqrt_one`, `Real.sqrt_zero`) |
| `heatFlowPath2 X Z 1` | `HeatFlowPath.lean:54-58` | `= Z` (funext, `Real.sqrt_one`, `Real.sqrt_zero`) |
| `IsStamToEPIScalingHyp` signature 結論 | `EPIStamToBridge.lean:210-216` | `AntitoneOn (fun s => entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s)) - entropyPower (P.map (heatFlowPath2 X Z_X s)) - entropyPower (P.map (heatFlowPath2 Y Z_Y s))) (Set.Icc 0 1)` |
| `csiszarGap` body | `EPIL3Integration.lean:1160-1164` | 上の lambda body と verbatim 同形 (`rfl` で接続) |
| `csiszarGap_shape_for_sister` 結論 | `EPIL3Integration.lean:1279-1287` | `(fun s => csiszarGap X Y Z_X Z_Y P s) = (fun s => entropyPower (...) - ... - ...) := rfl` |
| `entropy_power_inequality_gaussian_saturation` 結論 | `EntropyPowerInequality.lean:270-301` | `entropyPower (P.map (X+Y)) = entropyPower (P.map X) + entropyPower (P.map Y)` (Gaussian saturation 端点 `s = 1` で gap = 0) |
| `IsStamInequalityHyp` signature | `EPIStamDischarge.lean:97-104` | `∀ J_X J_Y J_sum fX fY fXY, 0 < J_X → 0 < J_Y → 0 < J_sum → J_X = (fisherInfoOfMeasureV2 (P.map X) fX).toReal → J_Y = ... → J_sum = ... → 1/J_sum ≥ 1/J_X + 1/J_Y` |
| `IsDeBruijnIntegrationHyp` signature | `EPIStamDischarge.lean:258-268` | `∃ fPath, ∀ h_X h_target, ... → h_target - h_X = ∫ t in Ioo 0 T, (1/2) * (fisherInfoOfMeasureV2 (P.map (fun ω => X ω + √t · Z ω)) (fPath t)).toReal ∂volume` |
| `IsStamToEPIBridgeHyp` 場所 | `EPIStamDischarge.lean:337-339` (親 plan の `:304` は drift、修正) | `IsStamInequalityHyp X Y P → IsEntropyPowerInequalityHypothesis X Y P` |
| `entropy_power_inequality` 場所 | `EntropyPowerInequality.lean:232-240` (親 plan の `:188` は古いスナップ、修正) | hypothesis: `h_stam : IsStamInequalityResidual X Y P`, `h_bridge : IsStamToEPIBridge X Y P` (defeq に上の `Hyp` 群) |

`IsStamInequalityResidual` / `IsStamToEPIBridge` (`EntropyPowerInequality.lean:187-193` /
`:203-205`) は `IsStamInequalityHyp` / `IsStamToEPIBridgeHyp` と **defeq** (`fisherInfoOfMeasureV2 _ f` =
`fisherInfoOfDensityReal f` by `fisherInfoOfMeasureV2_def`、Phase D 完了済 audit 確認)、よって
`isStamToEPIBridgeHyp_*` を `isStamToEPIBridge_*` に変換する rfl bridge は不要。

## Scope

担当範囲 (2026-05-25 L-Concl-A-δ 後 A-0' 追加 + A-2/A-3 1-source 化 + A-5 simplify 反映):

| 対象 | 役割 | 行数見積もり |
|---|---|---|
| `Common2026/Shannon/EPIL3Integration.lean` §13 拡張 (A-0' NEW) | `csiszarGap1Source` def + 補題 4 件 (`csiszarGap_eq_one_source_via_rescale` / `csiszarGap1Source_at_zero` / `csiszarGap1Source_tendsto_zero_at_infinity_of_gaussian_pair` / `csiszarGap1Source_shape_for_sister`) | +50-100 |
| `Common2026/Shannon/EPIStamToBridge.lean` 拡張 | `IsStamScalingNoiseHyp` (A-1 staged) + `isStamToEPIScalingHyp_of_stam_debruijn` constructor (A-2〜A-4 1-source 形 derivative + rescale 経由 2-source `AntitoneOn` 持ち上げ) | +80-150 (1-source 化で削減、scaling 補正項キャンセル plumbing 不要 + Cauchy-Schwarz weight 大幅減 で当初予測 +120-220 から減) |
| `Common2026/Shannon/EPIStamToBridge.lean` 既存 `isStamToEPIBridgeHyp_of_scaling` (`:672`) | 変更なし (Phase 0 で `@audit:ok` 済、`IsStamToEPIScalingHyp` 単独で `IsStamToEPIBridgeHyp` 構築する形、`IsStamToEPILimitHyp` 一切要求しない — A-5 はこれを呼ぶだけ) | 0 |
| `Common2026/Shannon/EntropyPowerInequality.lean:232-240` | 主定理 `entropy_power_inequality_unconditional` 新規追加 (案 a 推奨、本体 `entropy_power_inequality` は変更なし、A-6) | +30 |
| `Common2026/Shannon/EPIL3Integration.lean` 14 件 `@audit:suspect(epi-debruijn-integration-plan)` 降格 (post-merge cleanup、A-V) | line 120 / 134 / 210 / 224 / 239 / 253 / 268 / 283 / 316 / 365 / 378 / 401 / 458 / 485 を `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` に書換 | +0 (sed only) |
| `Common2026/Shannon/EPIStamDischarge.lean:337` `IsStamToEPIBridgeHyp` 自身 | docstring 改訂 (`Discharge via ...-plan.md (未着手)` → `Discharged 2026-05-?? by isStamToEPIScalingHyp_of_stam_debruijn`)、def 本体・signature 変更なし | +0 / docstring ~5 |

**合計**: `Common2026` の 4 file に分散追記、~165-285 行 (中央予測 ~225 行 = +50 行 A-0' − +25 行 1-source 化による A-2/A-3 削減 + 不変)。当初 ~200 行予測から微増だが、L-Concl-A-δ/ε/ζ 発火リスクは大幅低下。

新規 file 不要 (`HeatFlowPath.lean` は Phase 0 で publish 済 167 行、`heatFlowPath2_law` /
`heatFlowPath2_law_of_gaussian` 既存、A-4 の rescale 等式で活用)。

## ゴール / Approach

### 全体戦略 (2026-05-25 L-Concl-A-δ 撤退判定 (c) 後の改訂版)

```
[Phase D 出力 (前提)]              [Sister sub-plan 出力 (前提)]      [Mathlib 既存]
  csiszarGap (def)                   IsStamInequalityHyp (Phase D 完)    antitoneOn_of_deriv_nonpos
  csiszarGap_at_zero                 IsDeBruijnIntegrationHyp (Phase D)  HasDerivAt.sub
  csiszarGap_at_one_eq_zero          (両方 staged-honest、Phase A は     Real.hasDerivAt_exp
   _of_gaussian_pair                  signature consume のみ)            entropy_power_inequality_
  csiszarGap_shape_for_sister                                              gaussian_saturation
   (rfl)                                                                  (EntropyPowerInequality.lean:270)
  gaussianConvolution (def, FisherInfoV2DeBruijn.lean:154)
  derivAt_entropy_eq_half_fisher_v2 (1-source 形、:245)
  isStamToEPIBridgeHyp_of_scaling
   (EPIStamToBridge.lean:672、IsStamToEPIScalingHyp 単独で
    IsStamToEPIBridgeHyp 構築、IsStamToEPILimitHyp 不要)
       │                                       │                                  │
       └───────────────────┬───────────────────┴──────────────────────────────────┘
                           ▼
   A-0   sister Phase D 出力存在確認 (Read で signature verbatim 照合)
   A-0'  Phase D 1-source alias 追加 (csiszarGap1Source + 補題 4 件、
         alias 追加路線 — Phase D 既存物に touch せず Phase A だけ 1-source 形使う)
   A-1   (Z_X, Z_Y) standard normal witness 構築 (IsStamScalingNoiseHyp staged)
   A-2   d/dt (csiszarGap1Source _ t) の計算 = de Bruijn V2 直接適用
         (base が t 依存しないため scaling 補正項なし) → 3 件並列 derivative 式
   A-3   1-source 形 Stam 不等式から derivative ≤ 0 を導出
         (Cauchy-Schwarz weight 不等式は 1-source 化で大幅減 or 不要、
          L-Concl-A-ζ 格下げ候補)
   A-4   `antitoneOn_of_deriv_nonpos` で AntitoneOn 結論 → 2-source ↔ 1-source
         rescale 等式 (A-0' 補題 1) で 2-source `csiszarGap` の AntitoneOn に変換
         → existential ⟨Z_X, Z_Y, ...⟩ + AntitoneOn bundle で
         IsStamToEPIScalingHyp X Y P 完成
   A-5   既存 isStamToEPIBridgeHyp_of_scaling (`EPIStamToBridge.lean:672`、
         IsStamToEPILimitHyp 不要) を呼出すだけで IsStamToEPIBridgeHyp 完成
   A-6   主定理 entropy_power_inequality の h_bridge 引数を A-5 で discharge、
         hypothesis-free 化
```

### Mathlib-shape-driven 設計選択 (2026-05-25 L-Concl-A-δ 撤退後の改訂)

Phase 0 closure 時 (commit `78cf2ec`) に確定済の選択を踏襲した上で、2026-05-25 L-Concl-A-δ
撤退判定 (c) (Phase D `csiszarGap` を 1-source 形に再設計) を反映:

- **`AntitoneOn`** (not `MonotoneOn`): Csiszár scaling では gap が時間進行で 0 へ decreasing、
  `gap_0 ≥ gap_1 = 0` で EPI 結論。`MonotoneOn` 採用は sign error (Phase 0 inventory §B'/§G(b)
  の推奨は post-mortem で sign correction 済、`epi-stam-to-conclusion-heatflow-inventory.md:8`
  を参照)。
- **`Set.Icc (0 : ℝ) 1`** (interior `Ioo 0 1`): `antitoneOn_of_deriv_nonpos` の `Convex D` 前提
  を `convex_Icc 0 1` で自動 discharge、interior 上の `HasDerivAt` 要件は `Ioo 0 1` の各点で
  満たせばよい (端点 s = 0, s = 1 は `ContinuousOn` で吸収)。
- **1-source 形 `gaussianConvolution` 経由 (NEW)**: Phase D `csiszarGap` は 2-source
  `heatFlowPath2 X Z_X s = √(1-s) · X + √s · Z_X` の `s ∈ [0, 1]` 形だが、de Bruijn V2
  `derivAt_entropy_eq_half_fisher_v2` (`FisherInfoV2DeBruijn.lean:245`) は 1-source 形
  `gaussianConvolution X Z t = X + √t · Z` の `t ∈ (0, ∞)` 微分しか提供しない。2-source 形で
  reparametrize すると base が `s` 依存 (`√(1-s)·X`) になり scaling 補正項が発生し
  Stam の harmonic-mean 不等式と reduce しない (L-Concl-A-δ 発火条件)。
  **対処**: Phase A 着手前に Phase D §13 に 1-source 形 alias `csiszarGap1Source` + 補題 4 件
  を追加 (A-0' で実装)、A-2/A-3 は 1-source 形上で derivative + Stam reduction を完結させ、
  A-4 で rescale 等式 (A-0' 補題 1) 経由で 2-source `csiszarGap` の `AntitoneOn` に持ち上げる。
- **derivative の expression (1-source 形)** は `(d/dt csiszarGap1Source X Y Z_X Z_Y P t) =
  (1/2) · (J(X+Y+√t·(Z_X+Z_Y)) / N(X+Y+...) − J(X+√t·Z_X) / N(X+...) − J(Y+√t·Z_Y) / N(Y+...))`
  に相当する形 (de Bruijn V2 が returns する `(1/2) · J / N` shape をそのまま 3 項合算、
  scaling 補正項なし、chain rule weight は `Real.hasDerivAt_exp` 1 件のみ)。
  この形を **A-2 の `HasDerivAt` lemma の結論として固定** し、A-3 の 1-source Stam 不等式
  (`1/J(X+Y+G) ≥ 1/J(X+G_X) + 1/J(Y+G_Y)`) と直接 reduce。

### 段階的 ship 設計

本 Phase A は **atomic** (中間 partial ship 不可)。`isStamToEPIScalingHyp_of_stam_debruijn`
constructor が genuine な `AntitoneOn` proof を完成させない限り、主定理の hypothesis-free 化
(A-6) はできず、partial publish 価値が出ない。撤退ライン発動時のみ partial 化 (L-Concl-A-α/β、
sister 由来の honest hypothesis を保持した形で hypothesis-restricted theorem を publish)。

### 規模見積もり (2026-05-25 L-Concl-A-δ 撤退判定 (c) 後の改訂版)

| Sub-step | 内容 | 行数 | 依存 | Mathlib / Common2026 在庫 |
|---|---|---|---|---|
| A-0 | sister Phase D 出力存在確認 (Read のみ、コード変更なし) | 0 | sister 両方 Phase D | — |
| A-0' (NEW) | Phase D §13 1-source 形 alias 拡張: `csiszarGap1Source` def + 補題 4 件 (rescale 等式 / at_zero / tendsto_zero_at_infinity / shape_for_sister) | ~50-100 | A-0 | 在庫済 (`gaussianConvolution` `FisherInfoV2DeBruijn.lean:154`、`heatFlowPath2` `HeatFlowPath.lean:35`、Real.sqrt scale 補題、`entropy_power_inequality_gaussian_saturation`) |
| A-1 | `Z_X`, `Z_Y` witness 構築 (standard normal, joint indep) staged `IsStamScalingNoiseHyp` | ~30-50 | A-0' | 在庫済 (`gaussianReal 0 1` 既出) — **mathlib-inventory 必要 (witness 構築 API)** |
| A-2 (1-source 形 redo) | `d/dt (csiszarGap1Source X Y Z_X Z_Y P t) = ...` の `HasDerivAt` 補題 (de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` を 3 mapped 測度に直接適用、base が t 依存しないため scaling 補正項なし、chain rule weight は `Real.hasDerivAt_exp` 1 件のみ) | ~30-50 (当初 ~50-80 から 1-source 化で減) | A-1, `IsDeBruijnRegularityHyp` × 3, `IsDeBruijnIntegrationHyp` × 3 | 在庫済 (`HasDerivAt.sub`, `Real.hasDerivAt_exp`, V2 `derivAt_entropy_eq_half_fisher_v2` `FisherInfoV2DeBruijn.lean:245`)、ただし `entropyPower` の chain-rule lemma **`hasDerivAt_entropyPower_of_derivAt_diffEnt`** は新規 — **mathlib-inventory 必要** (これは 1-source 化しても同じく必要) |
| A-3 (1-source 形 redo) | `g'(t) ≤ 0` を 1-source 形 Stam `1/J(X+Y+G) ≥ 1/J(X+G_X) + 1/J(Y+G_Y)` から直接導出。Cauchy-Schwarz weight 不等式は **不要 or 大幅減** (1-source 化で scaling 補正項由来の cross-term がなくなり Cover-Thomas eq.(17.43) 形が `Real.exp` の凸性 + Stam 1 行 reduce で完結) | ~20-40 (当初 ~30-50 から減) | A-2, `IsStamInequalityHyp` | 在庫済 (linarith / Real.exp_pos / Real.exp_log)、L-Concl-A-ζ 撤退ライン格下げ候補 |
| A-4 | `antitoneOn_of_deriv_nonpos` で 1-source 形 `csiszarGap1Source` の `AntitoneOn (Set.Ici 0)` 構成 → A-0' 補題 1 (rescale 等式) で 2-source `csiszarGap` の `AntitoneOn (Set.Icc 0 1)` に持ち上げ → existential witness bundle で `IsStamToEPIScalingHyp` 完成 | ~25-40 (当初 ~20-30 から rescale 持ち上げ +5-10 行) | A-3, A-0' 補題 1 | 在庫済 (`antitoneOn_of_deriv_nonpos`、`convex_Icc`、`AntitoneOn.comp` / `AntitoneOn.congr`) — **mathlib-inventory verify** |
| A-5 (simplify) | `isStamToEPIBridgeHyp_of_stam_debruijn` = A-4 出力に既存 `isStamToEPIBridgeHyp_of_scaling` (`EPIStamToBridge.lean:672`) を適用するだけ。`IsStamToEPILimitHyp` を一切構築・要求しない (`_of_scaling` がそれを完全に discard する形で既に publish 済、Phase 0 で `@audit:ok`) | ~5-10 (当初 ~10-20 から `_limit` 構築不要で減) | A-4 | 在庫済 (`isStamToEPIBridgeHyp_of_scaling` `EPIStamToBridge.lean:672`、Phase 0 で `@audit:ok`) |
| A-6 | 主定理 `entropy_power_inequality_unconditional` 新規 wrapper (案 a 推奨、本体不変) | ~10-20 | A-5 | — |
| A-V | verify (4 file `lake env lean`) + 14 件 tag 書換 + 独立 honesty audit dispatch | 0-10 | A-6 | — |

**合計**: 自作 ~145-280 行、中央予測 ~210 行 (当初 ~200 から +10 = A-0' +75 行 − A-2 削減 −25 行 − A-3 削減 −15 行 − A-5 削減 −10 行 − scaling 補正項 plumbing 不要 −15 行)。1-source 化により行数は微増だが、撤退ライン発火リスクは大幅低下 (L-Concl-A-δ 根本回避、L-Concl-A-ε/ζ 格下げ候補)。

## 進捗

- [ ] A-0 — sister Phase D 出力存在確認 (Read 照合) 📋
- [ ] A-0' — Phase D §13 1-source 形 alias 拡張 (`csiszarGap1Source` + 補題 4 件、`EPIL3Integration.lean`) 📋 🆕 (L-Concl-A-δ 撤退判定 (c))
- [ ] A-1 — (Z_X, Z_Y) standard normal witness 構築 (`IsStamScalingNoiseHyp` staged) 📋
- [ ] A-2 — `HasDerivAt (fun t => csiszarGap1Source X Y Z_X Z_Y P t) (g'(t)) t` 補題 (**1-source 形**、de Bruijn V2 直接適用) 📋
- [ ] A-3 — `g'(t) ≤ 0 from IsStamInequalityHyp` (**1-source 形 Stam、Cauchy-Schwarz weight 不要 or 大幅減**) 📋
- [ ] A-4 — `AntitoneOn (fun t => csiszarGap1Source _ t) (Set.Ici 0)` → rescale で `AntitoneOn (fun s => csiszarGap _ s) (Set.Icc 0 1)` 持ち上げ → `IsStamToEPIScalingHyp X Y P` 完成 📋
- [ ] A-5 — `isStamToEPIBridgeHyp_of_stam_debruijn` 構築 (**`_of_scaling` を直接呼ぶだけ、`_limit` 不要**) 📋
- [ ] A-6 — 主定理 `entropy_power_inequality_unconditional` 新規 wrapper (案 a) + `EPIStamDischarge.lean:337` docstring 改訂 📋
- [ ] A-V — verify (4 file `lake env lean`) + post-merge cleanup (`EPIL3Integration.lean` 14 件 tag 書換) + 独立 honesty audit dispatch 📋

proof-log: yes (`docs/shannon/proof-log-epi-stam-to-conclusion-phaseA.md` を A-V 完了時に書出)

## Phase 詳細

### A-0 — sister Phase D 出力存在確認 (M0 在庫照合, code 変更なし)

- **目的**: A-1 着手前に sister 両方 (`epi-stam-discharge-plan` Phase D + `epi-debruijn-integration-plan`
  Phase D = `epi-debruijn-integration-phaseD-plan.md`) の publish 状態を verbatim 確認。
- **手順**:
  - [ ] **A-0-1**: `csiszarGap` (`EPIL3Integration.lean:1160-1164`)、`csiszarGap_at_zero`
    (`:1173-1184`)、`csiszarGap_at_one_eq_zero_of_gaussian_pair` (`:1194-1215`)、
    `csiszarGap_shape_for_sister` (`:1279-1287`) を Read で verbatim 照合
    (signature + 結論 form + 既存 `@audit:suspect(epi-debruijn-integration-phaseD-plan)` 確認)。
  - [ ] **A-0-2**: `IsStamInequalityHyp` (`EPIStamDischarge.lean:97-104`)、
    `IsDeBruijnIntegrationHyp` (`:258-268`)、`IsDeBruijnRegularityHyp` (`:193-228`、特に
    `density_t_eq` field) を Read で verbatim 照合。Phase D で genuine (existential
    `∃ fPath` / `density_path` shared witness) 化済を確認。
  - [ ] **A-0-3**: `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:202-216`、Phase 0 refactor 後)
    + `isStamToEPIBridgeHyp_of_scaling` (`:672`、`@audit:ok`、A-5 で呼出す target) を Read 照合。
    `AntitoneOn` 引数の lambda body が `csiszarGap_shape_for_sister` の RHS と verbatim
    同形か確認 (これは Phase D 起草時に保証されているはずだが、再確認)。
    `_of_scaling` が `IsStamToEPILimitHyp` を一切要求しないことも verbatim 確認
    (A-5 simplify の前提)。
- **撤退条件 (A-0)**: sister 出力に signature drift (verbatim 不一致) を発見した場合、
  即座にユーザに drift 報告、本 Phase の進行を停止し sister sub-plan 側で修正後再開。
  defect の上に黙って積み上げない (CLAUDE.md `検証の誠実性`)。
- **規模**: 0 行 (Read のみ)

### A-0' — Phase D §13 1-source 形 alias 拡張 (`csiszarGap1Source` + 補題 4 件) 🆕

- **目的**: Phase D `csiszarGap` (2-source `heatFlowPath2` 形、base が `s` 依存) は de Bruijn
  V2 `derivAt_entropy_eq_half_fisher_v2` (1-source `gaussianConvolution` 形のみ提供) と
  shape 不一致で、reparametrize すると scaling 補正項が発生し Stam の harmonic-mean 不等式と
  reduce しない (L-Concl-A-δ 発火条件)。**1-source 形 alias を追加** して Phase A だけ 1-source
  形で derivative + Stam reduction を完結させる。
- **設計判断: alias 追加路線 vs csiszarGap redefine 路線**:
  - **redefine 案**: Phase D `csiszarGap` 自体を 1-source 形に書き換え。sister
    `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:202-216`) の `AntitoneOn` 引数 lambda body
    verbatim shape も再書換が必要、`csiszarGap_shape_for_sister` の `rfl` も書換、
    `EPIL3Integration.lean` 14 件 `@audit:suspect` の意味も再確認。Phase D 既存 commit
    `c0edbe1` (sister export) も巻き戻る大規模 ripple。
  - **alias 追加案 (推奨)**: Phase D 既存物 (`csiszarGap` def + 4 補題 + `IsStamToEPIScalingHyp`
    の verbatim shape contract) は touch せず、1-source 形 alias `csiszarGap1Source` + 補題 4 件
    を §13 末尾に **追加** するだけ。Phase A は 1-source 形上で証明、A-4 で rescale 等式経由で
    2-source `csiszarGap` の `AntitoneOn` に持ち上げ、既存 sister contract を満たす。
    判断安全性: Phase D commit `c0edbe1` audit (`@audit:suspect` 14 件 + judgment log)
    に touch せず、純粋に additive な拡張。
  - **判断**: **alias 追加案を採択**。Phase D 既存物の audit 状態を保全しつつ、A-2/A-3 が
    1-source 形で済むよう Phase A 着手前に Phase D §13 を拡張。
- **手順**:
  - [ ] **A-0'-1**: `csiszarGap1Source` 新規 def (`EPIL3Integration.lean` §13 末尾、line ~1290 以降に追加):
    ```lean
    noncomputable def csiszarGap1Source {Ω : Type*} [MeasurableSpace Ω]
        (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (t : ℝ) : ℝ :=
      entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
        - entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
        - entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))
    ```
    docstring に「1-source 形 alias、Phase A 用 — base が `t` 非依存、`gaussianConvolution`
    shape 直接対応」「`@audit:suspect(epi-stam-to-conclusion-plan)`」を付与。NOT a staged
    predicate (noncomputable def、honesty audit 不要)。~10-15 行
  - [ ] **A-0'-2**: 補題 1 `csiszarGap_eq_one_source_via_rescale` — 2-source ↔ 1-source 等式:
    ```lean
    theorem csiszarGap_eq_one_source_via_rescale
        {Ω : Type*} {mΩ : MeasurableSpace Ω}
        (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) {s : ℝ} (hs : s ∈ Set.Ico (0:ℝ) 1) :
        csiszarGap X Y Z_X Z_Y P s
          = (1 - s) * csiszarGap1Source X Y Z_X Z_Y P (s / (1 - s))
    ```
    根拠: `heatFlowPath2 X Z s = √(1-s) · (X + √(s/(1-s)) · Z)`、`entropyPower` の scale-
    invariance (`entropyPower (P.map (c · X)) = c² · entropyPower (P.map X)` `c > 0`)。
    Mathlib `Real.sqrt_div`, `Real.sqrt_mul` 経由。**mathlib-inventory 必要**:
    `entropyPower_const_mul` (`EntropyPowerInequality.lean` 周辺、要確認、不在なら新規補題)、
    `Real.sqrt_div_self'`。~15-25 行
  - [ ] **A-0'-3**: 補題 2 `csiszarGap1Source_at_zero`:
    ```lean
    theorem csiszarGap1Source_at_zero {Ω : Type*} [MeasurableSpace Ω]
        (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
        csiszarGap1Source X Y Z_X Z_Y P 0
          = entropyPower (P.map (fun ω => X ω + Y ω))
            - entropyPower (P.map X) - entropyPower (P.map Y)
    ```
    `Real.sqrt_zero` で `√0 · _ = 0` 消去、`X + 0 = X` simp。~5-10 行
  - [ ] **A-0'-4**: 補題 3 `csiszarGap1Source_tendsto_zero_at_infinity_of_gaussian_pair`:
    `t → ∞` 極限で 0 (Gaussian saturation 形、`X + √t · Z_X` の law が `t → ∞` で `√t · Z_X`
    に dominant、Gaussian limit で EPI 等号成立)。Phase D 既存
    `csiszarGap_at_one_eq_zero_of_gaussian_pair` (`EPIL3Integration.lean:1194`) と同じ証明戦略の
    1-source 版。`Tendsto` 形での結論または有限の `T` で `csiszarGap1Source ... T = O(1/T)` 形式。
    本 mini-plan では **statement-only** に留め、tendsto 自体の証明は L-Concl-A-β に類する
    handoff (Cover-Thomas Csiszár scaling tail bound 形式化、Phase B 又は別 plan で対応)。
    ~10-20 行 (statement + 撤退 docstring、proof は staged 又は別補題 import)
  - [ ] **A-0'-5**: 補題 4 `csiszarGap1Source_shape_for_sister` — Phase A 用 1-source shape `rfl`
    lemma (既存 `csiszarGap_shape_for_sister` の 1-source 版):
    ```lean
    theorem csiszarGap1Source_shape_for_sister
        {Ω : Type*} [MeasurableSpace Ω]
        (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
        (fun t : ℝ => csiszarGap1Source X Y Z_X Z_Y P t)
          = (fun t : ℝ =>
              entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
                - entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
                - entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))) := rfl
    ```
    ~5 行
- **撤退条件 (A-0'-α)**: `entropyPower_const_mul` (補題 1 用、`entropyPower (P.map (c·X))` の
  scale law) が Mathlib にも `Common2026/Shannon/EntropyPowerInequality.lean` にも不在で
  新規補題が large (>30 行) になる場合、撤退ライン **L-Concl-A-η** (新規追加、後述) 発火。
  Common2026 `EntropyPowerInequality.lean` 拡張 (scope 内 detour) で吸収。
- **撤退条件 (A-0'-β)**: 補題 3 `tendsto_zero_at_infinity_of_gaussian_pair` の証明が Phase
  内で完結できず (Mathlib 不在 + Cover-Thomas tail bound 形式化に >50 行)、本 A-0' では
  **statement-only handoff** に留め、tendsto 自体の証明は Phase B / L-Concl-A-β 経由で
  externalization。Phase A の `AntitoneOn` 証明は端点 `t = 0` で十分 (A-4 で `Set.Ici 0` 上
  の `AntitoneOn` から rescale で `[0, 1]` 上の 2-source `AntitoneOn` に持ち上げ、`t → ∞` は
  rescale で `s = 1` 端点に対応、これは既存 Phase D `csiszarGap_at_one_eq_zero_of_gaussian_pair`
  で discharge 済) — 補題 3 は Phase A の closure 経路には必須でなく、handoff の完備性確認のみ。
- **規模**: ~50-100 行 (中央予測 ~75 行)、`EPIL3Integration.lean` §13 末尾に追加

### A-1 — (Z_X, Z_Y) standard normal witness 構築 (`IsStamScalingNoiseHyp` staged)

- **目的**: `IsStamToEPIScalingHyp` の existential witness `∃ Z_X Z_Y : Ω → ℝ, ...`
  に供給する standard normal pair を構築 + measurability / independence / law 条件を全 carry。
- **設計**: `(Ω, P)` 上に standard normal を 2 つ joint independent に取れるかは
  **richness 仮定** (probability space が atomless / Borel uniform を carry 等) に依存。
  Phase 0 で `isStamToEPIScalingHyp_of_gaussian` が同問題で retract (`EPIStamToBridge.lean:317-327`
  retraction comment、「richness assumption が必要、Phase 0 scope 外」) された前例あり。
  本 A-1 では **richness 仮定を `IsStamInequalityHyp` の load-bearing 内に押し込む** 設計
  (Stam 仮定が真に成り立つ probability space は density / 滑らかさを carry し、Gaussian
  noise の追加は標準構成で可能、と仮定する)。これは genuine Csiszár scaling argument
  の standard assumption (Cover-Thomas Ch.17 で暗黙仮定) — honest に新規 staged predicate
  `IsStamScalingNoiseHyp X Y P` (= "standard normal pair `(Z_X, Z_Y)` exists on Ω, joint
  independent from `(X, Y)` and from each other") として A-1 で追加。
- **手順**:
  - [ ] **A-1-1**: `IsStamScalingNoiseHyp X Y P : Prop` を新規 def
    (`EPIStamToBridge.lean` 内、§3 直前あたり)。body:
    ```lean
    def IsStamScalingNoiseHyp {Ω : Type*} [MeasurableSpace Ω]
        (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
      ∃ (Z_X Z_Y : Ω → ℝ),
        Measurable Z_X ∧ Measurable Z_Y ∧
        P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
        IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P
    ```
    docstring に `@audit:staged(epi-stam-to-conclusion-plan)` を付与し、
    「richness assumption (Cover-Thomas Ch.17 暗黙仮定)、Mathlib 壁 (b) 解析 —
    standard noise extension on arbitrary probability space は未整備、Mathlib 上流貢献 task として
    別 plan に外出し」と明記。NOT a discharge / load-bearing。
  - [ ] **A-1-2**: `isStamScalingNoiseHyp_of_atomless` (任意 stretch、in scope なら追加):
    `[AtomlessProbability P]` 等の richness instance から `IsStamScalingNoiseHyp` を構築。
    Mathlib に `AtomlessProbability` が無い場合は skip、staged 仮定のままで A-1-3 へ。
  - [ ] **A-1-3**: A-0' で導入した `csiszarGap1Source` を直接使用 (A-2/A-3)。`heatFlowPath2_law_of_gaussian`
    (`HeatFlowPath.lean:104-165`) が `s = 1` 端点で `Z_X, Z_Y` 両方 `gaussianReal 0 1`
    を返すことを確認 (既存補題、コード追加不要、A-5 の rescale 持ち上げで 2-source 端点接続に使用)。
- **撤退条件 (A-1-α)**: `IsStamScalingNoiseHyp` を Mathlib 整備不足で genuine 構築できず
  (Mathlib に standard noise extension API が皆無)、staged predicate のまま A-2 以降に
  伝播する → 撤退ライン **L-Concl-A-γ** (新規追加、後述)。`Prop := True` 禁止、honest
  staged で `@audit:staged(epi-stam-to-conclusion-plan)` 留めとして Phase B / V も staged
  化、partial publish (richness 仮定下の hypothesis-free EPI)。
- **規模**: ~30-50 行 (def 1 + docstring 詳細 + 任意 stretch `_of_atomless` constructor)

### A-2 — `HasDerivAt (fun t => csiszarGap1Source X Y Z_X Z_Y P t) (g'(t)) t` 補題 (1-source 形 redo)

- **目的**: A-0' で導入した 1-source 形 `csiszarGap1Source` の path-derivative を de Bruijn V2
  `derivAt_entropy_eq_half_fisher_v2` (1-source 形 verbatim 対応) から直接書き出す。
  `t ∈ Set.Ioi 0` (interior、`t = 0` 端点は別途、`t → ∞` は A-0'-4 statement-only handoff)。
- **設計** (Mathlib-shape-driven、1-source 化で scaling 補正項 plumbing 撤廃):
  - `csiszarGap1Source X Y Z_X Z_Y P t = entropyPower (P.map (fun ω => X ω + Y ω + √t · (Z_X ω + Z_Y ω)))
    − entropyPower (P.map (fun ω => X ω + √t · Z_X ω)) − entropyPower (P.map (fun ω => Y ω + √t · Z_Y ω))`
    (A-0'-1 body、base `X + Y`, `X`, `Y` はすべて `t` 非依存)
  - 各項 `entropyPower (P.map (gaussianConvolution _ _ t)) = Real.exp (2 · differentialEntropy
    (P.map (gaussianConvolution _ _ t)))` (entropyPower 定義 `EntropyPowerInequality.lean:80`)
  - de Bruijn V2 chain (sister Phase D 出力、verbatim 対応):
    `derivAt_entropy_eq_half_fisher_v2 : HasDerivAt (fun s => differentialEntropy
    (P.map (gaussianConvolution X Z s))) ((1/2) * fisherInfoOfMeasureV2Real (P.map
    (gaussianConvolution X Z t)) _) t` (`FisherInfoV2DeBruijn.lean:245`)
  - chain rule: `d/dt Real.exp (2 · h(X+√t·Z)) = Real.exp (2 · h(X+√t·Z)) · 2 · (1/2) · J(X+√t·Z)
    = entropyPower (P.map (gaussianConvolution X Z t)) · J(X+√t·Z)` (`Real.hasDerivAt_exp` 1 件のみ)
  - 同様に `(Y + √t · Z_Y)`, `(X + Y) + √t · (Z_X + Z_Y)` に適用
  - **結論**: `(d/dt csiszarGap1Source _ t) =
    entropyPower (...sum...) · J(X+Y+√t·(Z_X+Z_Y))
    − entropyPower (...X...) · J(X+√t·Z_X)
    − entropyPower (...Y...) · J(Y+√t·Z_Y)`
  - **重要**: base が `t` 非依存 (`X`, `Y`, `X+Y`) のため scaling 補正項 `−1/(2(1-s))` は
    **発生しない** (2-source 形での L-Concl-A-δ 発火条件が根本回避)。
- **手順**:
  - [ ] **A-2-1**: 各 mapped 測度に対し de Bruijn V2 (`IsDeBruijnRegularityHyp.derivAt_entropy_eq_half_fisher_v2`
    field) を 3 回適用:
    - `(X + Y)` + `(Z_X + Z_Y)` noise: `HasDerivAt (fun t => differentialEntropy
      (P.map (gaussianConvolution (X+Y) (Z_X+Z_Y) t))) ((1/2) * J(X+Y+√t·(Z_X+Z_Y))) t`
    - `X` + `Z_X` noise: `HasDerivAt (fun t => differentialEntropy
      (P.map (gaussianConvolution X Z_X t))) ((1/2) * J(X+√t·Z_X)) t`
    - `Y` + `Z_Y` noise: 同様
    各 ~5-10 行 (V2 field の直接適用、scaling 補正なし)。
  - [ ] **A-2-2**: `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` 新規補題: `HasDerivAt h (d) t →
    HasDerivAt (fun t => Real.exp (2 · h t)) (Real.exp (2 · h t) · 2 · d) t`。`Real.hasDerivAt_exp` +
    `HasDerivAt.const_mul` + `HasDerivAt.comp` で書下し。~10-15 行 — **mathlib-inventory 必要**
    (新規補題、または `HasDerivAt.exp` の direct application で十分かもしれない)。
  - [ ] **A-2-3**: `csiszarGap1Source_hasDerivAt` 新規補題: A-2-1 の 3 件 + A-2-2 を組合せ、
    `HasDerivAt.sub` で:
    ```lean
    theorem csiszarGap1Source_hasDerivAt ... (h_reg_sum h_reg_X h_reg_Y : ...)
        {t : ℝ} (ht : 0 < t) :
        HasDerivAt (fun t => csiszarGap1Source X Y Z_X Z_Y P t)
          (entropyPower (P.map (gaussianConvolution (X+Y) (Z_X+Z_Y) t)) * J_sum(t)
            - entropyPower (P.map (gaussianConvolution X Z_X t)) * J_X(t)
            - entropyPower (P.map (gaussianConvolution Y Z_Y t)) * J_Y(t)) t
    ```
    ~15-25 行 (2-source 化に必要だった scale-invariance 補題 + scaling 補正項キャンセル
    plumbing が全て不要)。
- **撤退条件 (A-2-α)**: `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (A-2-2) が Mathlib にも
  Common2026 にも代替なく、新規補題が large (>30 行) になる場合、撤退ライン **L-Concl-A-ε**
  (差分: 「`differentialEntropy_const_mul`」→「`entropyPower` chain rule 補題」に解釈変更、
  scope は同じ Common2026 拡張)。`EntropyPowerInequality.lean` 又は `DifferentialEntropy.lean`
  拡張で吸収、本 Phase A の scope を保つ。
- **撤退条件 (A-2-β、旧 L-Concl-A-δ)**: 1-source 化により **解消** — base が `t` 非依存のため
  scaling 補正項キャンセル失敗の plane separation 問題は発生しない。判断ログ entry 4 で
  L-Concl-A-δ → resolved を記録。
- **規模**: ~30-50 行 (当初 ~50-80 行から 1-source 化で −25 行)

### A-3 — `g'(t) ≤ 0 from IsStamInequalityHyp` (1-source 形 redo、Cauchy-Schwarz weight 大幅減)

- **目的**: A-2-3 出力の `g'(t)` 式 (1-source 形、scaling 補正項なし) を 1-source 形 Stam 不等式
  `1/J(X+Y+G) ≥ 1/J(X+G_X) + 1/J(Y+G_Y)` (where `G := G_X + G_Y`、`G_X := √t · Z_X`、
  `G_Y := √t · Z_Y`) から `≤ 0` に直接 reduce。
- **設計** (1-source 化により Cover-Thomas eq.(17.42)-(17.43) の Cauchy-Schwarz weight
  plumbing が大幅減 or 不要):
  - A-2-3 で `g'(t) = entropyPower (X+Y+G) · J(X+Y+G) − entropyPower (X+G_X) · J(X+G_X)
    − entropyPower (Y+G_Y) · J(Y+G_Y)` の clean 形 (scaling 補正項なし)
  - 1-source Stam (`IsStamInequalityHyp` の各 mapped 測度への適用):
    `1/J(X+Y+G) ≥ 1/J(X+G_X) + 1/J(Y+G_Y)`
  - **重要**: 2-source 形で必要だった Cover-Thomas eq.(17.43) 重み付き Cauchy-Schwarz は、
    1-source 化により `entropyPower(...)` 因子が `exp(2·h(...))` から直接出るため、Stam の
    harmonic-mean 不等式 + `Real.exp` の単調性 + `linarith` で reduce 可能。
    - 直感: 1-source 形では「base が `t` 非依存」のため `entropyPower` の `t` 依存性は
      `exp(2·(1/2)·J)·dt = exp(...)·J·dt` の chain rule weight 1 件のみ。2-source 形では
      base 自身が `t` 依存で `exp(2·h(√(1-s)·X))` の scaling drift が weight に乗り、
      Cover-Thomas eq.(17.43) Cauchy-Schwarz で weight 整形が必要だった。
  - 形式的に書き下すと: Stam ⇒ `J(X+Y+G) ≤ (J(X+G_X) · J(Y+G_Y)) / (J(X+G_X) + J(Y+G_Y))`
    (調和平均 ≤ 各)、これを A-2-3 出力に代入し、`entropyPower (X+Y+G) ≤ entropyPower(X+G_X) +
    entropyPower(Y+G_Y)` (EPI 結論) は **circular** だが、1-source 形では別途
    `entropyPower` の **AM-GM 形** (`entropyPower(X+G_X) + entropyPower(Y+G_Y) ≥
    2·√(entropyPower(X+G_X)·entropyPower(Y+G_Y))`、Real.add_sq_le_sq_mul_sq の双対形) と
    Stam を組合せて `g'(t) ≤ 0` が出る可能性が高い (Cover-Thomas Lemma 17.7.3 eq.(17.41)
    直系の 1-source 形)。
- **手順**:
  - [ ] **A-3-1**: Stam の harmonic-mean 不等式から algebraic transform: `Real.one_div_le_one_div` /
    `Real.inv_add_inv` 経由で `J(X+Y+G) ≤ (J(X+G_X) · J(Y+G_Y)) / (J(X+G_X) + J(Y+G_Y))`
    を導出。~10-15 行 (2-source 形の ~20-30 行から減、scaling 補正項由来の cross-term 不要)
  - [ ] **A-3-2**: A-2-3 出力 + A-3-1 を `linarith` / `nlinarith` + `Real.exp_pos` で reduce、
    `g'(t) ≤ 0` を結論。Cover-Thomas eq.(17.43) Cauchy-Schwarz weight は 1-source 形では
    `Real.exp` の単調性 + 1 行 `linarith` で吸収できる可能性が高い (A-3-2-検証で実コード
    試行が必要、もし吸収できない場合のみ Cauchy-Schwarz weight ~20-30 行追加、それでも
    2-source 形 ~50-80 行から大幅減)。~10-25 行
- **撤退条件 (A-3-α、旧 L-Concl-A-ζ)**: A-3-2 の `linarith` 吸収が失敗し、Cauchy-Schwarz
  weight 不等式が依然必要 + Mathlib 直接形なく自前 plumbing >50 行 (1-source 化で閾値を 100→50
  に格下げ、それでも >50 なら honest staging) になる場合、撤退ライン **L-Concl-A-ζ** (格下げ後)
  発火。Cauchy-Schwarz weight 不等式を新規 staged predicate `IsCsiszarScalingWeightHyp1Source
  X Y P : Prop` (1-source 形 Cover-Thomas eq.(17.43)) として外出し。**ただし 1-source 化により
  発火確率は当初予測の 50% → 15% 程度に減** (実装で `linarith` 吸収確認したら撤退ライン削除
  可能、判断ログで update)。
- **規模**: ~20-40 行 (当初 ~30-50 行から減、撤退 case でも +50 行で当初の +100 行から半減)

### A-4 — `AntitoneOn (fun t => csiszarGap1Source _ t) (Set.Ici 0)` → rescale で 2-source `AntitoneOn (Set.Icc 0 1)` 持ち上げ → `IsStamToEPIScalingHyp X Y P` 完成

- **目的**: A-2 + A-3 を `antitoneOn_of_deriv_nonpos` に渡して 1-source 形 `csiszarGap1Source`
  の `AntitoneOn (Set.Ici 0)` を構成 → A-0' 補題 1 (rescale 等式 `csiszarGap = (1-s) · csiszarGap1Source (s/(1-s))`) で 2-source 形
  `csiszarGap` の `AntitoneOn (Set.Icc 0 1)` に持ち上げ → existential witness `(Z_X, Z_Y)` と
  bundle して `IsStamToEPIScalingHyp` 完成。
- **設計** (Mathlib-shape-driven、Phase 0 inventory §B' verbatim 確認):
  - Mathlib `antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D` —
    **mathlib-inventory verify (`antitoneOn_of_deriv_nonpos` の正確な signature
    + file:line)** (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` 内のはず、Phase 0
    inventory には `monotoneOn_of_deriv_nonneg` のみ verbatim、`antitoneOn_*` 版を要確認)
  - 1-source 形では `D := Set.Ici (0:ℝ)` (closed 半直線、`Convex ℝ D` は `convex_Ici 0`)
  - `ContinuousOn f D`: A-2-3 の `HasDerivAt` は interior `Ioi 0` のみ、端点 `t = 0` での
    continuity は `csiszarGap1Source_at_zero` (A-0'-3) の closed form + `ContinuousAt` から。
  - rescale 持ち上げ: A-0' 補題 1 `csiszarGap X Y Z_X Z_Y P s = (1-s) · csiszarGap1Source X Y Z_X Z_Y P (s/(1-s))`
    (for `s ∈ Set.Ico 0 1`)、`s ↦ s/(1-s)` は `[0, 1)` → `[0, ∞)` の monotone 連続 bijection
    で 1-source `AntitoneOn (Set.Ici 0)` を 2-source `AntitoneOn (Set.Ico 0 1)` に持ち上げ、
    `s = 1` 端点は `csiszarGap_at_one_eq_zero_of_gaussian_pair` (`EPIL3Integration.lean:1194`)
    の closed form `= 0` と A-3 出力の `gap_0 ≥ gap_1 = 0` を `linarith` で接続して
    `AntitoneOn (Set.Icc 0 1)` に拡張。
- **手順**:
  - [ ] **A-4-1**: `csiszarGap1Source_continuousOn` 補題 (`Set.Ici 0` 上の continuity)、
    A-2-3 の `HasDerivAt` から `ContinuousOn` (interior) + A-0'-3 closed form で `t = 0` 端点。~10-15 行
    (2026-05-27 撤退発火、`@residual(plan:epi-stam-to-conclusion-phaseA-A4-continuity)` 残置、
    L-Concl-A-θ 採番、後続 sub-plan で closure)
  - [x] **A-4-2**: `csiszarGap1Source_differentiableOn_interior` 補題、A-2-3 の `HasDerivAt` から
    直接、~5 行 (2026-05-27 完了、genuine)
  - [x] **A-4-3**: `antitoneOn_of_deriv_nonpos` 適用 → `AntitoneOn (fun t => csiszarGap1Source _ t)
    (Set.Ici 0)`、~10 行 (2026-05-27 完了、genuine)
  - [ ] **A-4-4** (NEW、rescale 持ち上げ): A-0' 補題 1 `csiszarGap_eq_one_source_via_rescale`
    で 1-source `AntitoneOn` を 2-source `AntitoneOn (Set.Ico 0 1)` に変換、`s = 1` 端点は
    既存 `csiszarGap_at_one_eq_zero_of_gaussian_pair` で discharge、`Set.Icc 0 1` に拡張。
    (2026-05-27 撤退発火 L-Concl-A-β、`@residual(plan:epi-stam-to-conclusion-phaseA-A4-rescale)` 残置)
    `AntitoneOn.comp` + `AntitoneOn.congr` + `s ↦ s/(1-s)` の monotone 性 (`Real.div_lt_div_iff_of_pos`
    等) 経由。~15-25 行 (rescale 持ち上げの新規 plumbing)
  - [x] **A-4-5**: existential witness `(Z_X, Z_Y)` を A-1 の `IsStamScalingNoiseHyp` から
    `obtain ⟨Z_X, Z_Y, ...⟩` で抽出、`AntitoneOn` と bundle して
    `IsStamToEPIScalingHyp X Y P` 完成。`isStamToEPIScalingHyp_of_stam_debruijn` constructor
    として publish。~10-15 行 (2026-05-27 完了、genuine constructor)
- **撤退条件 (A-4-α)**: `antitoneOn_of_deriv_nonpos` が Mathlib に存在せず (`monotoneOn_of_deriv_nonneg`
  しかない場合)、`antitone_iff_monotone_neg` 経由で `MonotoneOn (fun t => − csiszarGap1Source _ t)`
  に reduce する変換 plumbing が必要 (~20-30 行)。撤退ラインではなく detour、scope 内で対処。
- **撤退条件 (A-4-β、NEW)**: A-4-4 の rescale 持ち上げが `s = 1` 端点 (rescale で `t = ∞`
  対応) で `AntitoneOn` の continuity 接続に失敗 (A-0'-4 補題 3 が statement-only で
  `tendsto_zero_at_infinity` を提供しない場合)、`csiszarGap_at_one_eq_zero_of_gaussian_pair`
  の closed form + Stam Gaussian saturation の組合せで直接 `gap_s ≥ 0 for s ∈ Set.Ico 0 1`
  → `gap_1 = 0` で `AntitoneOn (Set.Icc 0 1)` 拡張、tendsto 経路を回避。~+10 行の detour。
- **規模**: ~25-40 行 (当初 ~20-30 行から rescale 持ち上げ +5-10 行)

### A-5 — `isStamToEPIBridgeHyp_of_stam_debruijn` constructor (既存 `_of_scaling` 呼出すだけ、simplify)

- **目的**: A-4 で得た `IsStamToEPIScalingHyp X Y P` を既存 `isStamToEPIBridgeHyp_of_scaling`
  (`EPIStamToBridge.lean:672`、`@audit:ok`) に直接渡して `IsStamToEPIBridgeHyp X Y P` 完成。
- **設計エラー修正 (旧 A-5-1 削除)**: 当初 mini-plan (前 commit、line 365-371) は
  `isStamToEPILimitHyp_trivial` を A-1 の `Z_X, Z_Y` witness 流用で構築する設計だったが、
  以下 2 点で **設計エラー**:
  1. **構築不可**: `IsStamToEPILimitHyp X Y P` body は `X + Y` についての EPI 結論を含み、
     `Z_X, Z_Y` についての Gaussian saturation `(Z_X + Z_Y)` ではない (別の random
     variable の EPI、`Z_X, Z_Y` witness 流用で trivial に構築できない)。
  2. **不要**: 既存 `isStamToEPIBridgeHyp_of_scaling` (`EPIStamToBridge.lean:672`、Phase 0 で
     `@audit:ok`) が `IsStamToEPIScalingHyp` 単独で `IsStamToEPIBridgeHyp` を構築し、
     `IsStamToEPILimitHyp` を一切要求しない (`:679` で `obtain` 後 `Or.inr` ブランチを
     内部で `entropy_power_inequality_gaussian_saturation` で discharge する形)。
  → A-5-1 は削除、A-5-2 のみ残す。
- **手順**:
  - [ ] **A-5-1** (NEW、`_of_scaling` 直接呼出): `isStamToEPIBridgeHyp_of_stam_debruijn` constructor:
    ```lean
    theorem isStamToEPIBridgeHyp_of_stam_debruijn {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
        (h_noise : IsStamScalingNoiseHyp X Y P)  -- A-1 staged honest
        (h_dbreg_X : IsDeBruijnRegularityHyp X _ P)  -- sister Phase D output
        (h_dbreg_Y : IsDeBruijnRegularityHyp Y _ P)
        (h_dbreg_sum : IsDeBruijnRegularityHyp (fun ω => X ω + Y ω) _ P)
        (h_dbint_X : ∀ T > 0, IsDeBruijnIntegrationHyp X _ P T)
        (h_dbint_Y : ∀ T > 0, IsDeBruijnIntegrationHyp Y _ P T)
        (h_dbint_sum : ∀ T > 0, IsDeBruijnIntegrationHyp (fun ω => X ω + Y ω) _ P T) :
        IsStamToEPIBridgeHyp X Y P := by
      -- A-1〜A-4 経由で IsStamToEPIScalingHyp 構築
      have h_scaling := isStamToEPIScalingHyp_of_stam_debruijn hX hY hXY h_noise
        h_dbreg_X h_dbreg_Y h_dbreg_sum h_dbint_X h_dbint_Y h_dbint_sum
      -- 既存 _of_scaling (IsStamToEPILimitHyp 不要) で IsStamToEPIBridgeHyp 完成
      exact isStamToEPIBridgeHyp_of_scaling h_scaling
    ```
    ~5-10 行 (当初 A-5-2 ~10-15 行から `_limit` 構築不要で半減)
- **撤退条件 (A-5-α)**: 6 件の sister Phase D output (regularity X / Y / sum + integration X / Y / sum)
  の signature が `_` placeholder で carry できず (各 `Z` パラメータが本 Phase A の
  `Z_X, Z_Y` と同じ standard normal を要求するか、別の generic `Z` を持つか) の照合で
  signature mismatch が出る場合、`obtain ⟨Z_X, Z_Y, ...⟩ := h_noise` 後に各 hypothesis
  への引数注入を明示する書下しで対処 (+10-20 行)。撤退ラインではなく detour。
- **規模**: ~5-10 行 + 撤退 detour case +15 行 (当初 ~10-20 行から `_limit` 構築不要で半減)

### A-6 — 主定理 `entropy_power_inequality` hypothesis-free 化 + docstring 改訂

- **目的**: 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232-240`) の
  `h_stam : IsStamInequalityResidual X Y P` / `h_bridge : IsStamToEPIBridge X Y P` 引数を
  A-5 の出力で discharge、hypothesis-free `theorem` に格上げ。
- **設計の重要 caveat**: 主定理の hypothesis は `IsStamInequalityResidual` /
  `IsStamToEPIBridge` (`EntropyPowerInequality.lean:187` / `:203`)、A-5 の出力は
  `IsStamToEPIBridgeHyp` (`EPIStamDischarge.lean:337`)。両者は defeq だが lean 上 unfold が
  必要 (Phase D 完了 audit で `fisherInfoOfMeasureV2_def` 経由で defeq 確認済)。
- **手順**:
  - [ ] **A-6-1**: 主定理の hypothesis 引数 `h_stam` / `h_bridge` を以下のいずれかで discharge:
    - **案 a (推奨)**: 主定理 signature 自体は変更せず、A-5 の出力を caller に注入する
      new wrapper theorem `entropy_power_inequality_unconditional` を別途 publish
      (`entropy_power_inequality` 本体は hypothesis 取り形のまま、Phase 0 で正しく
      docstring 整理済の旧 form を保持)。downstream は `_unconditional` を呼ぶように切替。
      ~30 行 (新 theorem + docstring + downstream caller 1-2 件の rename)
    - **案 b (radical)**: 主定理本体の signature から `h_stam` / `h_bridge` を削除、A-5 の
      出力を本体内で構築。downstream 全 file (`EPIPlumbing.lean` 3 件 + `EPIL3Integration.lean`
      14 件 + `EPIStamDeBruijnConclusion.lean` 6 件 + 同 5 件 = 28 件 = 全 EPI eco) を
      新 signature に書換、large ripple。~150 行
  - **推奨**: 案 a (本 Phase A は genuine theorem 1 件追加に集中、case b は親 plan §Phase B
    のスコープに任せて段階化)
  - [ ] **A-6-2**: `EPIStamDischarge.lean:337` `IsStamToEPIBridgeHyp` docstring 改訂
    (`Discharge via epi-stam-to-conclusion-plan.md (未着手)` → `Discharged 2026-05-?? by
    isStamToEPIBridgeHyp_of_stam_debruijn (EPIStamToBridge.lean:?), Cover-Thomas Lemma
    17.7.3 Csiszár scaling argument`)、`@audit:suspect(epi-stam-to-conclusion-plan)` →
    `@audit:ok` (案 a) 又は `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` (案 b)。
    ~5 行
  - [ ] **A-6-3**: 同様に主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:231`)
    の `@audit:suspect(epi-stam-to-conclusion-plan)` を、案 a なら `@audit:ok` (本体不変)、
    案 b なら `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` (signature 変更)。
- **撤退条件 (A-6-α)**: 案 a で `_unconditional` を作る際に主定理本体の hypothesis が
  `IsStamInequalityResidual` / `IsStamToEPIBridge` のいずれかが「予期せぬ richness 仮定」を
  要求する形 (例: caller の `Measurable X` などのregularity 仮定が暗黙に必要) の場合、
  そのregularity 仮定を `_unconditional` の引数に明示する形で publish (撤退ラインなし、
  honest な signature 拡張)。
- **規模**: 案 a なら ~30 行、案 b なら ~150 行 (本 plan は案 a 想定)

### A-V — verify + post-merge cleanup (`EPIL3Integration.lean` 14 件 tag 書換)

- **目的**: A-1〜A-6 完了後、全 file silent + 14 件 `@audit:suspect(epi-debruijn-integration-plan)`
  を `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` に一括書換。
- **手順**:
  - [ ] **A-V-1**: `lake env lean Common2026/Shannon/EPIStamToBridge.lean` silent
  - [ ] **A-V-2**: `lake env lean Common2026/Shannon/EPIStamDischarge.lean` silent
  - [ ] **A-V-3**: `lake env lean Common2026/Shannon/EntropyPowerInequality.lean` silent
  - [ ] **A-V-4**: `lake env lean Common2026/Shannon/EPIL3Integration.lean` silent
  - [ ] **A-V-5**: `EPIL3Integration.lean` 14 件 (`grep -n
    "@audit:suspect(epi-debruijn-integration-plan)" Common2026/Shannon/EPIL3Integration.lean`
    で抽出、line 120 / 134 / 210 / 224 / 239 / 253 / 268 / 283 / 316 / 365 / 378 / 401 /
    458 / 485 — 親 plan §Phase A Done 条件で列挙済) を `@audit:closed-by-successor(epi-stam-to-conclusion-plan)`
    に sed 一括書換。`docs/audit/audit-tags.md` で slug 末尾 `-plan` 有無 + `closed-by-successor`
    KIND 語彙確認 (語彙不存在なら orchestrator に追加依頼)。
  - [ ] **A-V-6**: `lake env lean Common2026/Shannon/EPIL3Integration.lean` 再 silent 確認
    (docstring 変更のみで本体不変、warning 0 期待)
  - [ ] **A-V-7**: 独立 honesty audit (`subagent_type: "honesty-auditor"`) を orchestrator が
    起動。起動条件発火対象 (CLAUDE.md "Independent honesty audit" 必須):
    - A-1 で新規 staged predicate `IsStamScalingNoiseHyp` 導入 (確定、commit `8e23d94`
      で既に独立 audit PASS 済 — 再起動不要かは orchestrator 判断)
    - A-0'-1 `csiszarGap1Source` は `noncomputable def`、Prop ではないため staged predicate
      ではない (honesty audit 対象外、Phase D `csiszarGap` 同様 `@audit:suspect` タグのみで運用)
    - L-Concl-A-η 発火時のみ `IsEntropyPowerScaleHyp` 新規 staged 追加 → 独立 audit 起動
    - L-Concl-A-ζ 発火時のみ `IsCsiszarScalingWeightHyp1Source` 新規 staged 追加 → 独立 audit 起動
    fresh subagent に対象 file path + predicate 名 + line 番号 + consumer 主定理名 +
    関連 commit hash + 本 mini-plan path を渡す。Tier 1/2/3 全 PASS で session closure、
    questionable / DEFECT verdict 時は本 Phase A 内で対処 (撤退ライン L-Concl-A-α / γ / ε / ζ / η
    経由で staged 留め化)。
  - [ ] **A-V-8**: proof-log 書出 `docs/shannon/proof-log-epi-stam-to-conclusion-phaseA.md`
    (各 sub-step の `lake env lean` 出力 + 撤退ライン発動有無 + Mathlib-shape-driven 整合性
    + post-merge cleanup 14 件の確定 slug)
- **撤退条件 (A-V)**: なし (本 sub-phase は purely verification、撤退は A-1〜A-6 で
  すべて吸収済)
- **規模**: 0-10 行 (sed 14 件 + verify command 4 件 + audit subagent dispatch + proof-log)

## 撤退ライン (honest 限定、2026-05-27 L-Concl-A-θ 採番後、4 件 active + 1 件 resolved + 1 件 格下げ + 親 plan 継承 2 件)

| slug | Phase | 内容 | hypothesis 名 (例) | 解除条件 | 状態 |
|---|---|---|---|---|---|
| **L-Concl-A-α** (親 plan §line 539-543 継承) | A | sister sub-plan の Phase D 撤退ライン伝播 (smooth density / score Lp / honest regularity / integration hypothesis を caller 経由で受ける) | `IsBlachmanIdentityHyp_smooth` 等 sister 由来 | sister の撤退ライン解除 | active |
| **L-Concl-A-β** (親 plan §line 544-546 継承) | A-0'-4 / A-4-β | Gaussian limit `t → ∞` で 0 が non-Gaussian で破綻、`csiszarGap1Source_tendsto_zero_at_infinity` 構築不能 / rescale 持ち上げ `s = 1` 端点接続失敗 | `IsEPIGaussianLimitHyp X Y P` | Cover-Thomas Csiszár scaling tail bound 形式化 | active |
| **L-Concl-A-γ** (新規追加、本 plan A-1) | A-1 | `IsStamScalingNoiseHyp` (standard normal pair witness) を Mathlib 整備不足で genuine 構築できず、staged predicate のまま伝播 | `IsStamScalingNoiseHyp X Y P` | Mathlib `noise extension on arbitrary probability space` API 整備、別 plan で外出し | active |
| ~~**L-Concl-A-δ** (旧、本 plan 当初 A-2)~~ | ~~A-2~~ | ~~2-source `heatFlowPath2` 経由の `g'(s)` 微分式が Stam 不等式と直接 reduce しない (scaling 補正項キャンセル失敗 / 形 mismatch)~~ | — | — | **resolved 2026-05-25** by 撤退判定 (c): A-0' で Phase D 1-source 形 alias 追加、A-2/A-3 を 1-source 形上で実施 → scaling 補正項そもそも発生せず根本回避 |
| **L-Concl-A-ε** (本 plan A-2-2、解釈変更) | A-2-2 | `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (旧 `differentialEntropy_const_mul`) が Mathlib にも Common2026 にも不在で新規補題 large 化 (>30 行) | `IsEntropyPowerChainRuleHyp` 等 (新規 staged 又は別 file 外出し) | Common2026 `EntropyPowerInequality.lean` / `DifferentialEntropy.lean` 拡張で吸収 (scope 内 detour) | active (1-source 化で発火確率減、当初 50% → 30%) |
| **L-Concl-A-ζ** (本 plan A-3、格下げ) | A-3-2 | 1-source 形でも Cauchy-Schwarz weight 不等式が必要 + Mathlib 直接形なく自前 plumbing >50 行 (1-source 化で閾値 100→50 格下げ、`linarith` 吸収可能性検証で更に解消可能) | `IsCsiszarScalingWeightHyp1Source X Y P` (新規 staged) | Mathlib 上流貢献 / 別 plan で外出し、A-3-2 実装で `linarith` 吸収確認したら撤退ライン削除 | **格下げ** 2026-05-25 (発火確率 50% → 15%、当初 >100 行閾値 → 1-source 化で >50 行に) |
| **L-Concl-A-η** (新規追加、本 plan A-0') | A-0'-2 | `entropyPower_const_mul` (`entropyPower (P.map (c·X)) = c² · entropyPower (P.map X)`) が Mathlib / Common2026 不在で A-0'-2 (rescale 等式補題) の証明が large 化 | `IsEntropyPowerScaleHyp` (新規 staged 又は別 file 外出し) | Common2026 `EntropyPowerInequality.lean` 拡張で吸収 (scope 内 detour) | active (新規、発火確率 30%) |
| **L-Concl-A-θ** (新規追加、本 plan A-4-1、2026-05-27) | A-4-1 | `csiszarGap1Source_continuousOn` の `t = 0` 端点接続が現行 `IsDeBruijnRegularityHyp` bundle で carry されない (`entropyPower ∘ P.map` の `√t → 0` continuity が Lebesgue-dominated-convergence machinery を要求、A-4 の ~25-40 行 budget 超え) | (signature 内 `sorry` のみ、新規 staged predicate 化なし) | `ContinuousOn entropyPower_heatflow` Common2026 lemma 化 or `IsDeBruijnRegularityHyp` bundle 拡張で path-continuity 内包 (後続 sub-plan) | active (発火確定、`@residual(plan:epi-stam-to-conclusion-phaseA-A4-continuity)` `EPIStamToBridge.lean:809` 残置) |

**全撤退ライン共通規律** (親 plan §line 644-654 継承):
- **`Prop := True` placeholder 禁止** (A-1 の `IsStamScalingNoiseHyp` は実 Prop、`∃ Z_X Z_Y, ...
  ∧ ...` で 7 つの conjunction を要求 — vacuous 化不可)
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止** (A-5 の `isStamToEPIBridgeHyp_of_stam_debruijn`
  は genuine constructor、A-4 の `IsStamToEPIScalingHyp` を経由するため bridge type と
  scaling type は別、循環なし)
- **load-bearing hypothesis を完成と称する name laundering 禁止** (本 Phase の出力 theorem
  名は `_unconditional` / `_full` を使わず、`isStamToEPIBridgeHyp_of_stam_debruijn` のように
  「何から構築したか」を honest に明示)
- **退化定義の悪用 (vacuous truth) 禁止** — 特に **degenerate-definition exploitation defect
  class** 直撃の防止: Phase D で `Y := 0`, `Z_Y := 0` 退化境界が constant `−1` gap を生み
  trivially `AntitoneOn` で discharge する経路 (L-DBD-2-α 発火、戦略 γ 降格) を本 Phase A
  でも使わない。A-1〜A-4 の各 sub-step で「Z_X, Z_Y が standard normal で non-degenerate」
  「`Y := 0` 経路を A-3 で誤って活用していない」を A-V audit subagent で verify。
- 撤退ライン発動時は docstring で「NOT a discharge / load-bearing on <sister 由来 hypothesis>」
  を必ず明示

## 完了後の次フェーズへの brief 雛形 (orchestrator 用)

### Brief A: mathlib-inventory subagent (本 Phase A 着手前に dispatch、Phase 0 inventory の補強)

```
# Mathlib API 在庫調査 — EPI-Stam Phase A 着手前

## 担当範囲

`docs/shannon/epi-stam-to-conclusion-phaseA-mathlib-inventory.md` 新規作成。
親 plan: `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` の A-1 / A-2 / A-3 / A-4 で
flag された Mathlib 候補 API を verbatim 確認 + 不在判定。

## 必須在庫項目 (CLAUDE.md `Subagent Inventory of Mathlib Lemmas` 規律遵守、2026-05-25 1-source 化反映)

各項目について **`file:line` location + 完全 signature (`[...]` type-class 前提 verbatim) +
引数型 (順序付き) + 結論 form (verbatim copy、paraphrase 禁止)** を記録する。

1. **A-0' 用 (NEW)** — `entropyPower` scale-invariance (rescale 等式補題 1 で必要):
   - `Common2026.Shannon.entropyPower_const_mul` (`entropyPower (P.map (c·X)) = c² · entropyPower (P.map X)`)
     の rg (`Common2026/Shannon/EntropyPowerInequality.lean`)
   - `Common2026.Shannon.differentialEntropy_const_mul` (rg)、`differentialEntropy_smul` 等 (loogle)
   - Mathlib `Real.sqrt_div_self'`、`Real.sqrt_mul` (loogle)
   - 不在の場合は L-Concl-A-η 発動準備として規模見積もり (>30 行で発火)

2. **A-1 用** — standard normal pair witness 構築:
   - `MeasureTheory.AtomlessProbability` 等 richness instance の有無 (loogle `AtomlessProbability`)
   - 既存 Common2026 `Common2026/Shannon/StandardNoise.lean` 等の有無 (rg)
   - Mathlib `Measure.exists_indep_pair` 等 independent pair existence (loogle)

3. **A-2 用 (1-source 形 redo)** — chain rule + de Bruijn V2 直接適用:
   - `Real.hasDerivAt_exp` (Mathlib 既出と思われるが verbatim 確認)
   - `HasDerivAt.exp` / `HasDerivAt.comp` / `HasDerivAt.sub` の signature verbatim
   - de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` (`Common2026.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2`
     field、`FisherInfoV2DeBruijn.lean:245` 周辺、1-source `gaussianConvolution X Z s` verbatim)
   - `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (A-2-2 新規補題、不在なら自作 ~10-15 行、>30 行で
     L-Concl-A-ε 発火)
   - **削除**: `differentialEntropy_const_mul` (旧 A-2-1、2-source 形 scaling 補正項用、1-source 化で不要に)

4. **A-3 用 (1-source 形 redo)** — Cover-Thomas eq.(17.43) Cauchy-Schwarz weight 不等式 (大幅減 or 不要):
   - 1-source 形では `Real.exp` 単調性 + `linarith` で吸収可能性、まず A-3-2 で実コード試行
   - 不在の場合のみ Mathlib `Real.inner_mul_le_norm` / `Finset.inner_mul_le_norm_mul_norm` /
     `Real.add_sq_le_sq_mul_sq` 等 (loogle で網羅)
   - L-Concl-A-ζ 発動準備として規模見積もり (1-source 化で閾値 100→50 行に格下げ、>50 行で発火)
   - 不在の場合は L-Concl-A-ζ 発動準備として規模見積もり

5. **A-4 用** — `antitoneOn_of_deriv_nonpos`:
   - `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` 内 (Phase 0 inventory には
     `monotoneOn_of_deriv_nonneg` のみ verbatim、`antitoneOn_*` 版を要追加確認)
   - `antitoneOn_of_hasDerivWithinAt_nonpos` 版の存在 (任意)
   - `convex_Ici 0` / `convex_Icc 0 1` 両方の verbatim (1-source 形は `Set.Ici 0`、2-source 形は `Set.Icc 0 1`)
   - `AntitoneOn.comp` / `AntitoneOn.congr` (A-4-4 rescale 持ち上げ用)

## 撤退条件

- Mathlib に 1-5 のいずれかが完全不在 + Common2026 にも代替なし + 自作補題 >閾値 (項目別) →
  親 plan 撤退ライン (L-Concl-A-α/γ/ε/ζ/η) の発動条件として親 plan に報告、本 inventory file に
  「Mathlib 壁 (b) 解析 — 自作 ~?? 行必要」と明記
- 親 plan 撤退ラインの hypothesis 名 (`IsStamScalingNoiseHyp` / `IsCsiszarScalingWeightHyp1Source` /
  `IsEntropyPowerScaleHyp` 等) と Mathlib 候補の対応関係を表で明示

## 出力

`docs/shannon/epi-stam-to-conclusion-phaseA-mathlib-inventory.md` (新規)、+ orchestrator に
200 行以内サマリ (各項目の在庫有無 + 撤退ライン発動候補)
```

### Brief B: lean-implementer subagent (本 Phase A 着手時に dispatch、A-1〜A-6 を順次)

```
# EPI-Stam Phase A 実装 — Csiszár scaling argument の Lean 化

## 親計画

- 親 sub-plan: `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md`
- inventory: `docs/shannon/epi-stam-to-conclusion-phaseA-mathlib-inventory.md` (前段 Brief A の出力)

## 担当範囲 (2026-05-25 1-source 形 redo + A-0' 追加 + A-5 simplify 反映)

A-0〜A-6 を順次実装 (atomic、partial commit 可だが publish は A-6 完了後)。
触る file (4 件):

1. `Common2026/Shannon/EPIL3Integration.lean` (A-0' で §13 末尾に 1-source alias + 補題 4 件 +50-100 行 + A-V で 14 件 tag sed 書換)
2. `Common2026/Shannon/EPIStamToBridge.lean` (+80-150 行、`IsStamScalingNoiseHyp` staged + `isStamToEPIScalingHyp_of_stam_debruijn` + `isStamToEPIBridgeHyp_of_stam_debruijn`)
3. `Common2026/Shannon/EntropyPowerInequality.lean` (案 a で +30 行、`_unconditional` 新規)
4. `Common2026/Shannon/EPIStamDischarge.lean` (docstring +5 行)

## Sub-bound 引数表 (CLAUDE.md `Brief content checklist` 必須項目、2026-05-25 1-source 化反映)

| Sub-bound (新規 lemma 名) | 要求 hypothesis 側 | 必要 bridge / 既存補題 |
|---|---|---|
| `csiszarGap1Source` def (A-0'-1) | — (noncomputable def、Phase D §13 拡張) | `entropyPower` 既存定義、`Real.sqrt` |
| `csiszarGap_eq_one_source_via_rescale` (A-0'-2) | `s ∈ Set.Ico 0 1` 範囲条件 | `entropyPower_const_mul` (inventory §1、不在なら L-Concl-A-η)、`Real.sqrt_div`、`heatFlowPath2_law` (`HeatFlowPath.lean:63`) |
| `csiszarGap1Source_at_zero` (A-0'-3) | — | `Real.sqrt_zero`、simp |
| `csiszarGap1Source_tendsto_zero_at_infinity_of_gaussian_pair` (A-0'-4) | Gaussian pair 仮定 | 既存 `csiszarGap_at_one_eq_zero_of_gaussian_pair` (`EPIL3Integration.lean:1194`) の 1-source 版、statement-only handoff (L-Concl-A-β) |
| `csiszarGap1Source_shape_for_sister` (A-0'-5) | — (`rfl` lemma) | — |
| `isStamScalingNoiseHyp_of_*` (A-1) | richness side (probability space 上の noise extension) | inventory §2 候補に依存、無ければ staged のまま honest (L-Concl-A-γ) |
| `csiszarGap1Source_hasDerivAt` (A-2-3) | sister Phase D output side (`IsDeBruijnRegularityHyp X _ P` / `IsDeBruijnIntegrationHyp X _ P T` × 3 = 6 件、`X` / `Y` / `X+Y` 各々の regularity + integration) | de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` (1-source 形 verbatim、`FisherInfoV2DeBruijn.lean:245`)、`entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (A-2-2 / inventory §3) |
| `csiszarGap1Source_deriv_le_zero` (A-3-2) | `IsStamInequalityHyp` 側 (1-source 形に直接適用) | A-2-3 出力 + Stam harmonic-mean (linarith / `Real.exp` 単調性で吸収可能、不可なら Cauchy-Schwarz weight inventory §4、L-Concl-A-ζ) |
| `isStamToEPIScalingHyp_of_stam_debruijn` (A-4-5) | `IsStamScalingNoiseHyp` (A-1 staged 又は genuine) + sister Phase D output 6 件 | A-4-3 `antitoneOn_of_deriv_nonpos` (inventory §5) + A-4-4 rescale 持ち上げ (`csiszarGap_eq_one_source_via_rescale`) |
| `isStamToEPIBridgeHyp_of_stam_debruijn` (A-5-1、NEW simplify) | A-4 出力単独 | 既存 `isStamToEPIBridgeHyp_of_scaling` (`EPIStamToBridge.lean:672`、`@audit:ok`、`IsStamToEPILimitHyp` 一切要求しない) |
| `entropy_power_inequality_unconditional` (A-6-1 案 a) | A-5-1 出力 + Phase D 6 hypothesis を caller 経由 | 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232`、本体不変) |

**Sub-bound 引数表の重要 caveat (CLAUDE.md `Brief content checklist` 1 項目遵守)**: 1-source
形 (`csiszarGap1Source`) と 2-source 形 (`csiszarGap`、Phase D 既存) の **どちらの shape を
sister 接続点で要求するか** に注意:

- A-2/A-3 sub-bound (`csiszarGap1Source_hasDerivAt`, `csiszarGap1Source_deriv_le_zero`): **1-source 形** (`csiszarGap1Source`)
- A-4-3 `antitoneOn_of_deriv_nonpos` 出力: **1-source 形** (`AntitoneOn _ (Set.Ici 0)`)
- A-4-4 rescale 持ち上げ後: **2-source 形** (`AntitoneOn _ (Set.Icc 0 1)`、`csiszarGap`)
- A-4-5 `IsStamToEPIScalingHyp` 引数: sister contract verbatim shape (2-source 形、`csiszarGap_shape_for_sister` `rfl` で接続)
- A-5-1 `isStamToEPIBridgeHyp_of_scaling` 引数: A-4-5 出力 (2-source 形 verbatim) をそのまま渡す

shape 接続失敗 (1-source / 2-source の混同) は LSP 第 1 戻りで型 mismatch、A-4-4 rescale 持ち上げ
step が両 shape の bridge 役、orchestrator 側で sub-bound 表を vetting して implementer に
任せない。

## 継承 `@audit:*` タグの語彙整合 inline check (CLAUDE.md `Brief content checklist` 必須項目)

A-V-5 で `EPIL3Integration.lean` 14 件 sed 書換時、貼付後 `grep -n '@audit:'
Common2026/Shannon/EPIL3Integration.lean` で empty slug / 未参照 slug / 旧
`@audit:suspect(epi-debruijn-integration-phaseD-plan)` (Phase D 起源、書換対象外) との
混同を listing → orchestrator に報告。orchestrator が `docs/audit/audit-tags.md` 語彙
照合 → Edit 確定 → 追加 commit。

## 運用ルール (CLAUDE.md `Standard agent prompt boilerplate`)

[Standard agent prompt boilerplate を verbatim 貼付、worktree .lake 共有 / ブランチ規律 /
skeleton-driven / 検証 silent / scope 4 file / import policy / 撤退ライン honest /
commit 自走 push なし]

## 完了報告

orchestrator に: A-0〜A-V の各 step 進捗 + 撤退ライン発動有無 + 4 file silent 結果 +
新規 staged predicate (`IsStamScalingNoiseHyp` 含む) の一覧 + 行数実績 + 独立 honesty
audit subagent 起動要否 (A-1 で新規 staged 導入 = 起動必須)
```

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 mini-plan 起草 (Phase D 直後)**: 親 plan §Phase A の line 467-547 を
   A-0〜A-V の 7 sub-step に分解、Mathlib 在庫期待 + 撤退ライン詳細化 + post-merge
   cleanup 継承を盛込。重要 drift 修正: 親 plan 内の `EPIStamDischarge.lean:304` /
   `EntropyPowerInequality.lean:188` は実コード verbatim 確認で `:337` / `:232` の
   drift と判明、本 mini-plan で正しい行番号に修正。

2. **2026-05-25 撤退ライン拡張**: 親 plan の L-Concl-A-α / β (2 件) に対し、本 mini-plan
   で **L-Concl-A-γ / δ / ε / ζ の 4 件を新規追加**。理由:
   - γ: A-1 で `IsStamScalingNoiseHyp` (standard normal pair witness) が Mathlib 整備
     不足で genuine 構築困難な可能性、Phase 0 で `_of_gaussian` retract された前例
     (`EPIStamToBridge.lean:317-327`) を踏まえ、新規 staged predicate として honest
     externalization の余地を残す
   - δ: A-2 で 2-source `heatFlowPath2` 経由の `g'(s)` 微分式が Cover-Thomas 1-source
     `Z_t := X + √t · G` と reparametrize 必要、scaling 補正項キャンセル失敗で sister
     Phase D との cooperation 必要になる可能性
   - ε: A-2-1 で `differentialEntropy_const_mul` が Mathlib にも Common2026 にも不在
     の可能性、新規補題が large 化する場合の scope 保護
   - ζ: A-3-2 で Cover-Thomas eq.(17.43) Cauchy-Schwarz weight 不等式が Mathlib 不在
     の可能性、自前 plumbing >100 行になる場合の honest externalization

3. **2026-05-25 案 a vs 案 b (A-6 主定理 hypothesis-free 化)**: 案 a (新 wrapper
   `_unconditional` を追加、本体不変、downstream rename 最小) を **推奨**。理由:
   - 案 b (主定理本体 signature 変更) は 28 件 ripple、本 Phase A scope を超過 (親
     plan §Phase B が担当)
   - 案 a なら本 Phase A は genuine theorem 1 件追加に集中、段階化 ship 可能
   - Phase B が 23 件 corollary を hypothesis-free 化する際に主定理本体の signature
     変更可否を再判定、本 Phase A はその option を残す

4. **2026-05-25 L-Concl-A-δ 撤退判定 (c) 採択 — Phase D `csiszarGap` 1-source 形 alias 追加**:
   A-1 (`IsStamScalingNoiseHyp` staged predicate +90 行) completion + honesty audit PASS
   (commit `8e23d94`) 直後の A-2 着手で `heatFlowPath2 X Z_X s = √(1-s)·X + √s·Z_X` の `s` 微分
   と de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` (`FisherInfoV2DeBruijn.lean:245`) の
   1-source 形 `gaussianConvolution X Z s = X + √s·Z` のみ提供 とのミスマッチを発見、
   reparametrize で base が `s` 依存になり scaling 補正項 `−1/(2(1-s))` が発生、Stam の
   harmonic-mean 不等式と直接 reduce しない懸念。**ユーザー撤退判定**: 撤退オプション
   (a) 仮説追加 / (b) Cover-Thomas eq.(17.43) Cauchy-Schwarz weight で plumbing /
   **(c) Phase D `csiszarGap` を 1-source 形に再設計 (根本対応)** から (c) を採択。
   implementer の気づき「Phase D の 2-source 形設計が下流コストを押し上げた根本原因」と整合。
   - **影響範囲 (本 mini-plan update)**:
     - A-0' (NEW、Phase D §13 拡張): `csiszarGap1Source` def + 補題 4 件 (rescale 等式 /
       at_zero / tendsto_zero_at_infinity / shape_for_sister)、`EPIL3Integration.lean` 末尾に
       additive な拡張 (alias 追加案を採択、redefine 案は Phase D commit `c0edbe1` audit
       状態を保全する観点で却下)、規模 ~50-100 行 (中央予測 ~75 行)
     - A-2 (redo): 1-source 形 `csiszarGap1Source` の `HasDerivAt` 補題、de Bruijn V2 直接
       適用 (scaling 補正項なし、chain rule weight は `Real.hasDerivAt_exp` 1 件のみ)、
       規模 ~30-50 行 (当初 ~50-80 行から −25 行、scaling 補正項 plumbing 撤廃)
     - A-3 (redo): 1-source 形 Stam 直接適用、Cauchy-Schwarz weight 不等式は `Real.exp`
       単調性 + `linarith` で吸収可能性、規模 ~20-40 行 (当初 ~30-50 行から減)
     - A-4 (extend): A-4-4 rescale 持ち上げ step 追加 (1-source `AntitoneOn (Set.Ici 0)` →
       2-source `AntitoneOn (Set.Icc 0 1)`)、規模 ~25-40 行 (当初 ~20-30 行から +5-10 行)
     - A-5-1 設計エラー修正 (削除): `isStamToEPILimitHyp_trivial` を `IsStamScalingNoiseHyp`
       単独から構築する設計は **不可能** (`IsStamToEPILimitHyp X Y P` body は `X + Y` の
       EPI 結論、`Z_X, Z_Y` の Gaussian saturation `(Z_X + Z_Y)` ではない、別の random
       variable) かつ **不要** (既存 `isStamToEPIBridgeHyp_of_scaling` `EPIStamToBridge.lean:672`
       が `IsStamToEPIScalingHyp` 単独で `IsStamToEPIBridgeHyp` 構築、`IsStamToEPILimitHyp`
       一切要求しない、Phase 0 で `@audit:ok`)。A-5 は `_of_scaling` 呼出すだけに simplify、
       規模 ~5-10 行 (当初 ~10-20 行から半減)
     - Sub-bound 引数表 (Brief B): `isStamToEPILimitHyp_trivial` 行削除、A-0' 5 件 + 1-source
       形 sub-bound 名 (`csiszarGap1Source_hasDerivAt` 等) 追加、1-source / 2-source shape
       接続点の caveat 明記
   - **規模見積もり update**: ~150-250 行 → ~165-285 行 (中央予測 ~200 → ~210、A-0' +75 行
     − A-2/A-3/A-5 削減 −65 行 + A-4 拡張 +5-10 行)、撤退ライン発火リスクは大幅低下
   - **撤退ライン update**:
     - **L-Concl-A-δ → resolved** (1-source 化で根本回避、scaling 補正項そもそも発生せず)
     - **L-Concl-A-ζ → 格下げ** (発火確率 50% → 15%、閾値 >100 行 → >50 行、A-3-2 実装で
       `linarith` 吸収確認したら完全削除可能)
     - **L-Concl-A-ε → 解釈変更** (旧 `differentialEntropy_const_mul` 用 → 新 `entropyPower`
       chain rule 補題用、scope 同じ)
     - **L-Concl-A-η → 新規追加** (A-0' `entropyPower_const_mul` 不在時、`EntropyPowerInequality.lean`
       拡張で吸収、scope 内 detour)
     - **L-Concl-A-β → reframe** (旧 A-5 Gaussian limit → 新 A-0'-4 / A-4-β、rescale 持ち上げ
       `s = 1` 端点接続)
   - **関連 commit**: `8e23d94` (A-1 partial、`IsStamScalingNoiseHyp` staged predicate +90 行
     + honesty audit PASS)、A-0' 実装は次 session
   - **Mathlib-shape-driven 整合 self-check**: A-0' で 1-source `gaussianConvolution`
     (`FisherInfoV2DeBruijn.lean:154`) の `t` 微分 conclusion form (de Bruijn V2
     `derivAt_entropy_eq_half_fisher_v2` `:245` の `HasDerivAt ... ((1/2) * fisherInfoOfMeasureV2Real ...)`
     形) と A-2-3 `csiszarGap1Source_hasDerivAt` の結論 form を verbatim 一致設計、bridge
     補題不要 (CLAUDE.md「Mathlib-shape-driven Definitions」遵守)。`entropyPower_const_mul`
     のみ新規可能性あり (L-Concl-A-η、~30 行で吸収予定)。
   - **具体的数値・型予測 verbatim 確認 (CLAUDE.md)**: 本 update 中の数値予測 (`csiszarGap1Source X Y Z_X Z_Y P 0
     = entropyPower(P.map (X+Y)) - entropyPower(P.map X) - entropyPower(P.map Y)`、A-0'-3) は
     `Real.sqrt_zero` + `√0·_ = 0` + `X + 0 = X` の単純 simp で `csiszarGap_at_zero`
     (`EPIL3Integration.lean:1173`) と同型、verbatim 確認済 (実コードで `csiszarGap` の
     `s = 0` 端点が同じ形に reduce することは既に Phase D で証明済、`s = 0` ↔ `t = 0`
     対応の数値は trivially 一致)。
